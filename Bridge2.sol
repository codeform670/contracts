// SPDX-License-Identifier: UNLICENSED

/*
 * Hyperliquid L2 Bridge Contract operating on Arbitrum (L2).
 * It manages asset transfers (currently USDC) and validator set consensus
 * with the Tendermint-based Hyperliquid L1.
 *
 * Security Mechanism:
 * - Two-thirds (2/3) validator power quorum required for withdrawals and hot validator set updates.
 * - Transactions are pending during a dispute period (time and blocks).
 * - Lockers can pause the bridge during the dispute period.
 * - Cold wallet quorum required to unlock the bridge or modify critical parameters.
 */

pragma solidity ^0.8.9;

import "@openzeppelin/contracts/security/Pausable.sol";
import "@openzeppelin/contracts/security/ReentrancyGuard.sol";
import "@openzeppelin/contracts/token/ERC20/ERC20.sol";
import "@openzeppelin/contracts/token/ERC20/utils/SafeERC20.sol";
import "@openzeppelin/contracts/token/ERC20/extensions/draft-ERC20Permit.sol";
import "@arbitrum/nitro-contracts/src/precompiles/ArbSys.sol";
// Assume Signature.sol imports necessary EIP-712 hashing utilities (e.g., Agent struct, hash, recoverSigner)
import "./Signature.sol";

// --- Struct Definitions ---

struct ValidatorSet {
  uint64 epoch;
  address[] validators;
  uint64[] powers;
}

struct ValidatorSetUpdateRequest {
  uint64 epoch;
  address[] hotAddresses;
  address[] coldAddresses;
  uint64[] powers;
}

struct PendingValidatorSetUpdate {
  uint64 epoch;
  uint64 totalValidatorPower;
  uint64 updateTime;
  uint64 updateBlockNumber;
  uint64 nValidators;
  bytes32 hotValidatorSetHash;
  bytes32 coldValidatorSetHash;
}

struct Withdrawal {
  address user;
  address destination;
  uint64 usd;
  uint64 nonce;
  uint64 requestedTime;
  uint64 requestedBlockNumber;
  bytes32 message;
}

struct WithdrawalRequest {
  address user;
  address destination;
  uint64 usd;
  uint64 nonce;
  Signature[] signatures;
}

struct DepositWithPermit {
  address user;
  uint64 usd;
  uint64 deadline;
  Signature signature;
}

contract Bridge2 is Pausable, ReentrancyGuard {
  using SafeERC20 for ERC20Permit;
  ERC20Permit public usdcToken;

  // Validator Set Checkpoints
  bytes32 public hotValidatorSetHash;
  bytes32 public coldValidatorSetHash;
  PendingValidatorSetUpdate public pendingValidatorSetUpdate;

  // Message Tracking (for nonces/unique operations)
  mapping(bytes32 => bool) public usedMessages;

  // Locker Mechanism (Emergency Pause)
  mapping(address => bool) public lockers;
  address[] private lockersVotingLock;
  uint64 public lockerThreshold;

  // Finalizer Mechanism (Withdrawal/Update Execution)
  mapping(address => bool) public finalizers;

  // Bridge Configuration
  uint64 public epoch;
  uint64 public totalValidatorPower;
  uint64 public disputePeriodSeconds;
  // Measures the duration of a block in milliseconds for dispute period calculation on Arbitrum.
  uint64 public blockDurationMillis; 
  uint64 public nValidators; // Convenience variable for validator count

  // Withdrawal Tracking
  mapping(bytes32 => Withdrawal) public requestedWithdrawals;
  mapping(bytes32 => bool) public finalizedWithdrawals;
  mapping(bytes32 => bool) public withdrawalsInvalidated;

  // EIP-712 domain separator for signature hash calculations
  bytes32 immutable domainSeparator;

  // --- Events ---
  event Deposit(address indexed user, uint64 usd);
  event RequestedWithdrawal(
    address indexed user,
    address destination,
    uint64 usd,
    uint64 nonce,
    bytes32 message,
    uint64 requestedTime
  );
  event FinalizedWithdrawal(
    address indexed user,
    address destination,
    uint64 usd,
    uint64 nonce,
    bytes32 message
  );
  event RequestedValidatorSetUpdate(
    uint64 epoch,
    bytes32 hotValidatorSetHash,
    bytes32 coldValidatorSetHash,
    uint64 updateTime
  );
  event FinalizedValidatorSetUpdate(
    uint64 epoch,
    bytes32 hotValidatorSetHash,
    bytes32 coldValidatorSetHash
  );
  event FailedWithdrawal(bytes32 message, uint32 errorCode);
  event ModifiedLocker(address indexed locker, bool isLocker);
  event FailedPermitDeposit(address user, uint64 usd, uint32 errorCode);
  event ModifiedFinalizer(address indexed finalizer, bool isFinalizer);
  event ChangedDisputePeriodSeconds(uint64 newDisputePeriodSeconds);
  event ChangedBlockDurationMillis(uint64 newBlockDurationMillis);
  event ChangedLockerThreshold(uint64 newLockerThreshold);
  event InvalidatedWithdrawal(Withdrawal withdrawal);


  // --- Constructor ---

  constructor(
    address[] memory hotAddresses,
    address[] memory coldAddresses,
    uint64[] memory powers,
    address usdcAddress,
    uint64 _disputePeriodSeconds,
    uint64 _blockDurationMillis,
    uint64 _lockerThreshold
  ) {
    domainSeparator = makeDomainSeparator();
    totalValidatorPower = checkNewValidatorPowers(powers);

    require(
      hotAddresses.length == coldAddresses.length,
      "Hot and cold validator sets length mismatch"
    );
    nValidators = uint64(hotAddresses.length);

    // Initialize Hot Validator Set (Epoch 0)
    ValidatorSet memory hotValidatorSet = ValidatorSet({ epoch: 0, validators: hotAddresses, powers: powers });
    bytes32 newHotValidatorSetHash = makeValidatorSetHash(hotValidatorSet);
    hotValidatorSetHash = newHotValidatorSetHash;

    // Initialize Cold Validator Set (Epoch 0)
    ValidatorSet memory coldValidatorSet = ValidatorSet({ epoch: 0, validators: coldAddresses, powers: powers });
    bytes32 newColdValidatorSetHash = makeValidatorSetHash(coldValidatorSet);
    coldValidatorSetHash = newColdValidatorSetHash;

    usdcToken = ERC20Permit(usdcAddress);
    disputePeriodSeconds = _disputePeriodSeconds;
    blockDurationMillis = _blockDurationMillis;
    lockerThreshold = _lockerThreshold;
    addLockersAndFinalizers(hotAddresses);

    // Initial Validator Set Update Request
    emit RequestedValidatorSetUpdate(
      0,
      hotValidatorSetHash,
      coldValidatorSetHash,
      uint64(block.timestamp)
    );

    // Finalize the initial set immediately (no dispute period needed for initialization)
    pendingValidatorSetUpdate = PendingValidatorSetUpdate({
      epoch: 0,
      totalValidatorPower: totalValidatorPower,
      updateTime: 1, // Set to 1 to mark it as 'requested' but immediately finalized below
      updateBlockNumber: getCurBlockNumber(),
      hotValidatorSetHash: hotValidatorSetHash,
      coldValidatorSetHash: coldValidatorSetHash,
      nValidators: nValidators
    });

    finalizeValidatorSetUpdateInner(); // Mark as final and set updateTime = 0
  }

  // --- Utility Functions ---

  /** Registers initial hot validators as both lockers and finalizers. */
  function addLockersAndFinalizers(address[] memory addresses) private {
    uint64 end = uint64(addresses.length);
    for (uint64 idx; idx < end; idx++) {
      address _address = addresses[idx];
      lockers[_address] = true;
      finalizers[_address] = true;
    }
  }

  /** Calculates the hash (checkpoint) of a ValidatorSet struct. */
  function makeValidatorSetHash(ValidatorSet memory validatorSet) private pure returns (bytes32) {
    require(
      validatorSet.validators.length == validatorSet.powers.length,
      "Malformed validator set"
    );
    // Hash includes validators, powers, and epoch
    bytes32 checkpoint = keccak256(
      abi.encode(validatorSet.validators, validatorSet.powers, validatorSet.epoch)
    );
    return checkpoint;
  }

  /** Checks if the sender is authorized as a finalizer. */
  function checkFinalizer(address finalizer) private view {
    require(finalizers[finalizer], "Sender is not a finalizer");
  }

  /** Checks that the total power of the new validator set is greater than zero. */
  function checkNewValidatorPowers(uint64[] memory powers) private pure returns (uint64) {
    uint64 cumulativePower;
    for (uint64 i; i < powers.length; i++) {
      cumulativePower += powers[i];
    }
    require(cumulativePower > 0, "Submitted validator powers must be greater than zero");
    return cumulativePower;
  }

  /** Gets the current block number, using ArbSys precompile on Arbitrum L2. */
  function getCurBlockNumber() private view returns (uint64) {
    // Check for local testing environment (e.g., Hardhat/Ganache)
    if (block.chainid == 1337) {
      return uint64(block.number);
    }
    // For Arbitrum, use the precompile to get the actual L2 block number
    return uint64(ArbSys(address(100)).arbBlockNumber());
  }

  /** Constructs the EIP-712 compatible message hash for signature validation. */
  function makeMessage(bytes32 data) private view returns (bytes32) {
    // Note: Assumes Agent struct and hash function are defined in Signature.sol for EIP-712
    Agent memory agent = Agent("a", keccak256(abi.encode(address(this), data)));
    return hash(agent);
  }

  /** Ensures a message hash has not been previously used. */
  function checkMessageNotUsed(bytes32 message) private {
    require(!usedMessages[message], "Message already used");
    usedMessages[message] = true;
  }
  
  /** Checks if a withdrawal has not been explicitly invalidated by a cold wallet quorum. */
  function isValidWithdrawal(bytes32 message) private view returns (bool) {
    return !withdrawalsInvalidated[message];
  }

  // Returns 0 if the dispute period has elapsed, otherwise returns an error code (3: time, 4: blocks).
  function getDisputePeriodErrorCode(
    uint64 time,
    uint64 blockNumber
  ) private view returns (uint32) {
    if (block.timestamp <= time + disputePeriodSeconds) {
      return 3; // Dispute period not over (time)
    }

    uint64 curBlockNumber = getCurBlockNumber();
    
    // Check if enough L2 blocks have passed to satisfy the time-based duration
    // (curBlockNumber - blockNumber) * blockDurationMillis > 1000 * disputePeriodSeconds
    if ((curBlockNumber - blockNumber) * blockDurationMillis <= 1000 * disputePeriodSeconds) {
      return 4; // Dispute period not over (blocks)
    }

    return 0;
  }
  
  /** Verifies validator signatures and checks if the power quorum (2/3) is met. */
  function checkValidatorSignatures(
    bytes32 message,
    ValidatorSet memory activeValidatorSet,
    Signature[] memory signatures,
    bytes32 validatorSetHash
  ) private view {
    // Ensure the supplied validator set matches the active checkpoint hash
    require(
      makeValidatorSetHash(activeValidatorSet) == validatorSetHash,
      "Supplied active validators and powers do not match the active checkpoint"
    );

    uint64 nSignatures = uint64(signatures.length);
    require(nSignatures > 0, "Signers empty");
    uint64 cumulativePower = 0;
    uint64 signatureIdx = 0;
    uint64 end = uint64(activeValidatorSet.validators.length);
    
    // Iterate through the ACTIVE set to check powers in the correct order
    for (uint64 activeValidatorSetIdx; activeValidatorSetIdx < end; activeValidatorSetIdx++) {
      // NOTE: This assumes signatures are provided in the same order as signing validators appear in the activeValidatorSet.
      // If the signature list is exhausted, we break (no quorum means failure later).
      if (signatureIdx >= nSignatures) break; 
      
      // Recover the signer address using the message and signature
      address signer = recoverSigner(message, signatures[signatureIdx], domainSeparator);
      
      // Check if the recovered signer is the expected active validator at the current index
      if (signer == activeValidatorSet.validators[activeValidatorSetIdx]) {
        uint64 power = activeValidatorSet.powers[activeValidatorSetIdx];
        cumulativePower += power;

        // Quorum check: 3 * cumulativePower > 2 * totalValidatorPower (i.e., > 2/3)
        if (3 * cumulativePower > 2 * totalValidatorPower) {
          break;
        }

        signatureIdx += 1;
      }
      // If the recovered signer does NOT match the active validator, the signature is ignored,
      // and we continue checking the next active validator. The signature index is NOT incremented.
    }

    require(
      3 * cumulativePower > 2 * totalValidatorPower,
      "Submitted validator set signatures do not have enough power"
    );
  }

  // --- Deposits ---

  /** Handles a single USDC deposit via EIP-2612 Permit. */
  function depositWithPermit(
    address user,
    uint64 usd,
    uint64 deadline,
    Signature memory signature
  ) private {
    // CRITICAL FIX: Ensure non-zero amount
    if (usd == 0) {
      emit FailedPermitDeposit(user, usd, 2); // New error code for zero amount
      return;
    }

    address spender = address(this);
    
    // 1. Permit the contract to spend the user's USDC
    try
      usdcToken.permit(
        user,
        spender,
        usd,
        deadline,
        signature.v,
        bytes32(signature.r),
        bytes32(signature.s)
      )
    {} catch {
      emit FailedPermitDeposit(user, usd, 0); // Permit failed
      return;
    }

    // 2. Transfer the USDC from the user to the contract
    try usdcToken.transferFrom(user, spender, usd) returns (bool success) {
      if (!success) {
        emit FailedPermitDeposit(user, usd, 1); // Transfer failed
        return;
      }
    } catch {
      emit FailedPermitDeposit(user, usd, 1); // Transfer failed (revert)
      return;
    }

    // 3. Emit deposit event for L1 validators to credit the L1 account
    emit Deposit(user, usd);
  }

  /** Batched function to process multiple Permit deposits. */
  function batchedDepositWithPermit(
    DepositWithPermit[] memory deposits
  ) external nonReentrant whenNotPaused {
    uint64 end = uint64(deposits.length);
    for (uint64 idx; idx < end; idx++) {
      depositWithPermit(
        deposits[idx].user,
        deposits[idx].usd,
        deposits[idx].deadline,
        deposits[idx].signature
      );
    }
  }

  // --- Withdrawals ---

  /** Internal function to request a single withdrawal, verified by hot validator signatures. */
  function requestWithdrawal(
    address user,
    address destination,
    uint64 usd,
    uint64 nonce,
    ValidatorSet calldata hotValidatorSet,
    Signature[] memory signatures
  ) internal {
    // Generate the unique message hash for the withdrawal
    bytes32 data = keccak256(abi.encode("requestWithdrawal", user, destination, usd, nonce));
    bytes32 message = makeMessage(data);

    if (!isValidWithdrawal(message)) {
      emit FailedWithdrawal(message, 5); // Withdrawal invalidated
      return;
    }

    // NEW FIX: Ensure this exact message hash (including nonce) hasn't been used for any unique operation
    checkMessageNotUsed(message);

    // Ensure the withdrawal hasn't been requested before
    if (requestedWithdrawals[message].requestedTime != 0) {
      emit FailedWithdrawal(message, 0); // Already requested
      return;
    }
    
    // Check if signatures meet the 2/3 hot validator quorum
    checkValidatorSignatures(message, hotValidatorSet, signatures, hotValidatorSetHash);
    
    // Record the pending withdrawal
    Withdrawal memory withdrawal = Withdrawal({
      user: user,
      destination: destination,
      usd: usd,
      nonce: nonce,
      requestedTime: uint64(block.timestamp),
      requestedBlockNumber: getCurBlockNumber(),
      message: message
    });
    
    requestedWithdrawals[message] = withdrawal;
    
    emit RequestedWithdrawal(
      withdrawal.user,
      withdrawal.destination,
      withdrawal.usd,
      withdrawal.nonce,
      withdrawal.message,
      withdrawal.requestedTime
    );
  }

  /** External function callable by anyone to process batched withdrawal requests from the L1. */
  function batchedRequestWithdrawals(
    WithdrawalRequest[] memory withdrawalRequests,
    ValidatorSet calldata hotValidatorSet
  ) external nonReentrant whenNotPaused {
    uint64 end = uint64(withdrawalRequests.length);
    for (uint64 idx; idx < end; idx++) {
      WithdrawalRequest memory withdrawalRequest = withdrawalRequests[idx];
      requestWithdrawal(
        withdrawalRequest.user,
        withdrawalRequest.destination,
        withdrawalRequest.usd,
        withdrawalRequest.nonce,
        hotValidatorSet,
        withdrawalRequest.signatures
      );
    }
  }

  /** Internal function to finalize a single withdrawal and transfer tokens. */
  function finalizeWithdrawal(bytes32 message) internal {
    if (!isValidWithdrawal(message)) {
      emit FailedWithdrawal(message, 5); // Withdrawal invalidated
      return;
    }

    if (finalizedWithdrawals[message]) {
      emit FailedWithdrawal(message, 1); // Already finalized
      return;
    }

    Withdrawal memory withdrawal = requestedWithdrawals[message];
    if (withdrawal.requestedTime == 0) {
      emit FailedWithdrawal(message, 2); // Not requested
      return;
    }

    // Check if the dispute period has fully elapsed (time and blocks)
    uint32 errorCode = getDisputePeriodErrorCode(
      withdrawal.requestedTime,
      withdrawal.requestedBlockNumber
    );

    if (errorCode != 0) {
      emit FailedWithdrawal(message, errorCode); // Dispute period active
      return;
    }

    finalizedWithdrawals[message] = true;
    usdcToken.safeTransfer(withdrawal.destination, withdrawal.usd);
    
    emit FinalizedWithdrawal(
      withdrawal.user,
      withdrawal.destination,
      withdrawal.usd,
      withdrawal.nonce,
      withdrawal.message
    );
  }

  /** External function callable by a finalizer to process batched withdrawal finalizations. */
  function batchedFinalizeWithdrawals(
    bytes32[] calldata messages
  ) external nonReentrant whenNotPaused {
    checkFinalizer(msg.sender);
    uint64 end = uint64(messages.length);
    for (uint64 idx; idx < end; idx++) {
      finalizeWithdrawal(messages[idx]);
    }
  }

  /** Cold wallet quorum can invalidate a batch of requested withdrawals during the dispute period. */
  function invalidateWithdrawals(
    bytes32[] memory messages,
    uint64 nonce,
    ValidatorSet memory activeColdValidatorSet,
    Signature[] memory signatures
  ) external {
    // Requires cold validator quorum
    bytes32 data = keccak256(abi.encode("invalidateWithdrawals", messages, nonce));
    bytes32 message = makeMessage(data);

    checkMessageNotUsed(message);
    checkValidatorSignatures(message, activeColdValidatorSet, signatures, coldValidatorSetHash);

    uint64 end = uint64(messages.length);
    for (uint64 idx; idx < end; idx++) {
      withdrawalsInvalidated[messages[idx]] = true;
      // Emit the full withdrawal details for off-chain tracking
      emit InvalidatedWithdrawal(requestedWithdrawals[messages[idx]]);
    }
  }
  
  // --- Validator Set Updates ---

  /** Updates the pending validator set using hot validator quorum. */
  function updateValidatorSet(
    ValidatorSetUpdateRequest memory newValidatorSet,
    ValidatorSet memory activeHotValidatorSet,
    Signature[] memory signatures
  ) external whenNotPaused {
    // Check if the currently supplied active set matches the L2 checkpoint
    require(
      makeValidatorSetHash(activeHotValidatorSet) == hotValidatorSetHash,
      "Supplied active validators and powers do not match checkpoint"
    );

    // Generate the unique message hash for the update
    bytes32 data = keccak256(
      abi.encode(
        "updateValidatorSet",
        newValidatorSet.epoch,
        newValidatorSet.hotAddresses,
        newValidatorSet.coldAddresses,
        newValidatorSet.powers
      )
    );
    bytes32 message = makeMessage(data);

    // Uses hotValidatorSetHash to check signatures
    updateValidatorSetInner(newValidatorSet, activeHotValidatorSet, signatures, message, false);
  }

  /** Internal core logic for updating the validator set request. */
  function updateValidatorSetInner(
    ValidatorSetUpdateRequest memory newValidatorSet,
    ValidatorSet memory activeValidatorSet,
    Signature[] memory signatures,
    bytes32 message,
    bool useColdValidatorSet
  ) private {
    require(
      newValidatorSet.hotAddresses.length == newValidatorSet.coldAddresses.length,
      "New hot and cold validator sets length mismatch"
    );
    require(
      newValidatorSet.hotAddresses.length == newValidatorSet.powers.length,
      "New validator set and powers length mismatch"
    );
    require(
      newValidatorSet.epoch > pendingValidatorSetUpdate.epoch, // Corrected from activeValidatorSet.epoch
      "New validator set epoch must be greater than the pending/active epoch"
    );

    uint64 newTotalValidatorPower = checkNewValidatorPowers(newValidatorSet.powers);

    bytes32 validatorSetHash = useColdValidatorSet ? coldValidatorSetHash : hotValidatorSetHash;

    // Check signatures against the appropriate current active set (hot or cold)
    checkValidatorSignatures(message, activeValidatorSet, signatures, validatorSetHash);

    // Generate hashes for the new set
    ValidatorSet memory newHotValidatorSet = ValidatorSet({
      epoch: newValidatorSet.epoch,
      validators: newValidatorSet.hotAddresses,
      powers: newValidatorSet.powers
    });
    bytes32 newHotValidatorSetHash = makeValidatorSetHash(newHotValidatorSet);

    ValidatorSet memory newColdValidatorSet = ValidatorSet({
      epoch: newValidatorSet.epoch,
      validators: newValidatorSet.coldAddresses,
      powers: newValidatorSet.powers
    });
    bytes32 newColdValidatorSetHash = makeValidatorSetHash(newColdValidatorSet);

    // Record the pending update
    uint64 updateTime = uint64(block.timestamp);
    pendingValidatorSetUpdate = PendingValidatorSetUpdate({
      epoch: newValidatorSet.epoch,
      totalValidatorPower: newTotalValidatorPower,
      updateTime: updateTime,
      updateBlockNumber: getCurBlockNumber(),
      hotValidatorSetHash: newHotValidatorSetHash,
      coldValidatorSetHash: newColdValidatorSetHash,
      nValidators: uint64(newHotValidatorSet.validators.length)
    });

    emit RequestedValidatorSetUpdate(
      newValidatorSet.epoch,
      newHotValidatorSetHash,
      newColdValidatorSetHash,
      updateTime
    );
  }

  /** External function callable by a finalizer to finalize a pending validator set update. */
  function finalizeValidatorSetUpdate() external nonReentrant whenNotPaused {
    checkFinalizer(msg.sender);

    require(
      pendingValidatorSetUpdate.updateTime != 0,
      "No pending validator set update to finalize"
    );

    uint32 errorCode = getDisputePeriodErrorCode(
      pendingValidatorSetUpdate.updateTime,
      pendingValidatorSetUpdate.updateBlockNumber
    );
    require(errorCode == 0, "Still in dispute period");

    finalizeValidatorSetUpdateInner();
  }

  /** Internal core logic for atomically finalizing the validator set. */
  function finalizeValidatorSetUpdateInner() private {
    require(
      pendingValidatorSetUpdate.updateTime != 0,
      "Pending validator set update already finalized"
    );
    
    // Atomically swap the active set
    hotValidatorSetHash = pendingValidatorSetUpdate.hotValidatorSetHash;
    coldValidatorSetHash = pendingValidatorSetUpdate.coldValidatorSetHash;
    epoch = pendingValidatorSetUpdate.epoch;
    totalValidatorPower = pendingValidatorSetUpdate.totalValidatorPower;
    nValidators = pendingValidatorSetUpdate.nValidators;
    pendingValidatorSetUpdate.updateTime = 0; // Clear the pending state

    emit FinalizedValidatorSetUpdate(
      epoch,
      hotValidatorSetHash,
      coldValidatorSetHash
    );
  }

  // --- Configuration and Management ---

  /** Changes the dispute period duration (seconds), requiring cold validator quorum. */
  function changeDisputePeriodSeconds(
    uint64 newDisputePeriodSeconds,
    uint64 nonce,
    ValidatorSet memory activeColdValidatorSet,
    Signature[] memory signatures
  ) external {
    bytes32 data = keccak256(
      abi.encode("changeDisputePeriodSeconds", newDisputePeriodSeconds, nonce)
    );
    bytes32 message = makeMessage(data);
    
    checkMessageNotUsed(message);
    checkValidatorSignatures(message, activeColdValidatorSet, signatures, coldValidatorSetHash);

    disputePeriodSeconds = newDisputePeriodSeconds;
    emit ChangedDisputePeriodSeconds(newDisputePeriodSeconds);
  }

  /** Changes the assumed block duration (milliseconds), requiring cold validator quorum. */
  function changeBlockDurationMillis(
    uint64 newBlockDurationMillis,
    uint64 nonce,
    ValidatorSet memory activeColdValidatorSet,
    Signature[] memory signatures
  ) external {
    bytes32 data = keccak256(
      abi.encode("changeBlockDurationMillis", newBlockDurationMillis, nonce)
    );
    bytes32 message = makeMessage(data);

    checkMessageNotUsed(message);
    checkValidatorSignatures(message, activeColdValidatorSet, signatures, coldValidatorSetHash);

    blockDurationMillis = newBlockDurationMillis;
    emit ChangedBlockDurationMillis(newBlockDurationMillis);
  }

  /** Changes the locker threshold, requiring cold validator quorum. */
  function changeLockerThreshold(
    uint64 newLockerThreshold,
    uint64 nonce,
    ValidatorSet memory activeColdValidatorSet,
    Signature[] memory signatures
  ) external {
    bytes32 data = keccak256(abi.encode("changeLockerThreshold", newLockerThreshold, nonce));
    bytes32 message = makeMessage(data);

    checkMessageNotUsed(message);
    checkValidatorSignatures(message, activeColdValidatorSet, signatures, coldValidatorSetHash);

    lockerThreshold = newLockerThreshold;
    // Check if the new threshold triggers an immediate pause
    if (uint64(lockersVotingLock.length) >= lockerThreshold && !paused()) {
      _pause();
    }
    emit ChangedLockerThreshold(newLockerThreshold);
  }
  
  // --- Locker / Pausable Logic ---

  /** External function to allow a whitelisted locker to cast an emergency lock vote. */
  function voteEmergencyLock() external {
    require(lockers[msg.sender], "Sender is not authorized to lock smart contract");
    require(!isVotingLock(msg.sender), "Locker already voted for emergency lock");
    lockersVotingLock.push(msg.sender);
    
    // Check if threshold is met to pause the contract
    if (uint64(lockersVotingLock.length) >= lockerThreshold && !paused()) {
      _pause();
    }
  }

  /** External function to allow a whitelisted locker to retract their emergency lock vote. */
  function unvoteEmergencyLock() external whenNotPaused {
    require(lockers[msg.sender], "Sender is not authorized to lock smart contract");
    require(isVotingLock(msg.sender), "Locker is not currently voting for emergency lock");
    removeLockerVote(msg.sender);
  }

  /** Internal utility to remove a locker's vote from the array. */
  function removeLockerVote(address locker) private {
    // Note: The `whenNotPaused` check was removed from this private function 
    // as it is only necessary for the external caller (`unvoteEmergencyLock`), 
    // but the original code had it here and in `modifyLocker`. Keeping it internal 
    // and relying on external checks is cleaner.

    require(lockers[locker], "Address is not authorized to lock smart contract");
    uint64 length = uint64(lockersVotingLock.length);
    for (uint64 i = 0; i < length; i++) {
      if (lockersVotingLock[i] == locker) {
        // Swap the found locker with the last element for O(1) removal
        lockersVotingLock[i] = lockersVotingLock[length - 1];
        lockersVotingLock.pop();
        break;
      }
    }
  }

  /** Modifies the locker whitelist, requiring hot/cold quorum based on operation. */
  function modifyLocker(
    address locker,
    bool _isLocker,
    uint64 nonce,
    ValidatorSet calldata activeValidatorSet,
    Signature[] memory signatures
  ) external {
    bytes32 data = keccak256(abi.encode("modifyLocker", locker, _isLocker, nonce));
    bytes32 message = makeMessage(data);

    bytes32 validatorSetHash = _isLocker ? hotValidatorSetHash : coldValidatorSetHash;

    checkMessageNotUsed(message);
    checkValidatorSignatures(message, activeValidatorSet, signatures, validatorSetHash);
    
    // If removing a locker and the contract is not paused, remove any existing lock vote
    if (lockers[locker] && !_isLocker && !paused()) {
      removeLockerVote(locker);
    }
    lockers[locker] = _isLocker;
    emit ModifiedLocker(locker, _isLocker);
  }

  /** Modifies the finalizer whitelist, requiring hot/cold quorum based on operation. */
  function modifyFinalizer(
    address finalizer,
    bool _isFinalizer,
    uint64 nonce,
    ValidatorSet calldata activeValidatorSet,
    Signature[] memory signatures
  ) external {
    bytes32 data = keccak256(abi.encode("modifyFinalizer", finalizer, _isFinalizer, nonce));
    bytes32 message = makeMessage(data);

    bytes32 validatorSetHash = _isFinalizer ? hotValidatorSetHash : coldValidatorSetHash;

    checkMessageNotUsed(message);
    checkValidatorSignatures(message, activeValidatorSet, signatures, validatorSetHash);
    
    finalizers[finalizer] = _isFinalizer;
    emit ModifiedFinalizer(finalizer, _isFinalizer);
  }

  /** Unlocks the bridge, atomically setting a new validator set, requiring cold validator quorum. */
  function emergencyUnlock(
    ValidatorSetUpdateRequest memory newValidatorSet,
    ValidatorSet calldata activeColdValidatorSet,
    Signature[] calldata signatures,
    uint64 nonce
  ) external whenPaused {
    bytes32 data = keccak256(
      abi.encode(
        "unlock",
        newValidatorSet.epoch,
        newValidatorSet.hotAddresses,
        newValidatorSet.coldAddresses,
        newValidatorSet.powers,
        nonce
      )
    );
    bytes32 message = makeMessage(data);

    checkMessageNotUsed(message);
    // Use cold wallet set hash for signature check
    updateValidatorSetInner(newValidatorSet, activeColdValidatorSet, signatures, message, true);
    
    // Finalize the update immediately
    finalizeValidatorSetUpdateInner();
    
    // Clear all existing votes and unpause
    delete lockersVotingLock;
    _unpause();
  }
}
