import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Coordinates

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial

open Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

inductive ReviewKind
  | payment (holder : Holder input)
  | assignment (sender recipient : Holder input)

def reviewOperation (claim : IssuedClaim input) (kind : ReviewKind input) (quantity : ℚ) :
    Operation Party Good Technology Instrument :=
  match kind with
  | .payment holder => .settle claim.instrument claim.debtor (holderParty input holder) quantity
  | .assignment sender recipient =>
      .assign claim.instrument claim.debtor (holderParty input sender) (holderParty input recipient) quantity

structure Review (claim : IssuedClaim input) where
  private mk ::
  origin : InstructionOrigin input
  instruction : ExecutionItem Party Good Port Technology Instrument
  instruction_exact : origin.instruction? input = some instruction
  kind : ReviewKind input
  quantity : ℚ
  operation_exact : instruction.request.operation = reviewOperation input claim kind quantity
  accepted : input.law.Valid instruction.before instruction.request

namespace Review

def fromHolder {claim : IssuedClaim input} (review : Review input claim) : Holder input :=
  match review.kind with
  | .payment holder => holder
  | .assignment sender _ => sender

def toHolder {claim : IssuedClaim input} (review : Review input claim) : Holder input :=
  match review.kind with
  | .payment holder => holder
  | .assignment _ recipient => recipient

def senderBirth {claim : IssuedClaim input} (review : Review input claim) :
    Source.ProgrammeFace.ActualBirth.At input review.origin.visit
      (holderParty input (review.fromHolder input)) :=
  review.origin.participantBirth input review.instruction review.instruction_exact _ (by
    rw [review.operation_exact]
    cases kind : review.kind <;> simp [reviewOperation, fromHolder, kind,
      Source.ProgrammeFace.operationParties])

def recipientBirth {claim : IssuedClaim input} (review : Review input claim) :
    Source.ProgrammeFace.ActualBirth.At input review.origin.visit
      (holderParty input (review.toHolder input)) :=
  review.origin.participantBirth input review.instruction review.instruction_exact _ (by
    rw [review.operation_exact]
    cases kind : review.kind <;> simp [reviewOperation, toHolder, kind,
      Source.ProgrammeFace.operationParties])

def allocated {claim : IssuedClaim input} (review : Review input claim)
    (balance : Balance input) (remaining : ℚ) : ℚ :=
  min remaining (balance (review.fromHolder input))

def after {claim : IssuedClaim input} (review : Review input claim)
    (balance : Balance input) (remaining : ℚ) : Balance input :=
  let used := review.allocated input balance remaining
  match review.kind with
  | .payment holder => pay input balance holder used
  | .assignment sender recipient => assign input balance sender recipient used

omit [DecidableEq Port] in
theorem quantity_nonnegative {claim : IssuedClaim input} (review : Review input claim) :
    0 ≤ review.quantity := by
  have guarded := review.accepted.2.2.1
  unfold RawLaw.ClaimGuard at guarded
  rw [review.operation_exact] at guarded
  cases kind : review.kind <;>
    simp only [reviewOperation, kind] at guarded <;> exact guarded.1

omit [DecidableEq Port] in
theorem allocated_nonnegative {claim : IssuedClaim input} (review : Review input claim)
    (balance : Balance input) (remaining : ℚ)
    (balance_nonnegative : Nonnegative input balance) (available : 0 ≤ remaining) :
    0 ≤ review.allocated input balance remaining :=
  le_min available (balance_nonnegative _)

omit [DecidableEq Port] in
theorem allocated_le_available {claim : IssuedClaim input} (review : Review input claim)
    (balance : Balance input) (remaining : ℚ) :
    review.allocated input balance remaining ≤ remaining := min_le_left _ _

omit [DecidableEq Port] in
theorem allocated_le_old_share {claim : IssuedClaim input} (review : Review input claim)
    (balance : Balance input) (remaining : ℚ) :
    review.allocated input balance remaining ≤ balance (review.fromHolder input) := min_le_right _ _

omit [DecidableEq Port] in
theorem after_nonnegative {claim : IssuedClaim input} (review : Review input claim)
    (balance : Balance input) (remaining : ℚ)
    (balance_nonnegative : Nonnegative input balance) (available : 0 ≤ remaining) :
    Nonnegative input (review.after input balance remaining) := by
  have positive := review.allocated_nonnegative input balance remaining balance_nonnegative available
  have bounded := review.allocated_le_old_share input balance remaining
  cases kind : review.kind with
  | payment holder =>
      simp only [after, kind]
      exact pay_nonnegative input balance holder _ balance_nonnegative (by
        simpa only [fromHolder, kind] using bounded)
  | assignment sender recipient =>
      simp only [after, kind]
      exact assign_nonnegative input balance sender recipient _ balance_nonnegative positive (by
        simpa only [fromHolder, kind] using bounded)

end Review

def readReview (claim : IssuedClaim input) (origin : InstructionOrigin input) :
    Option (Review input claim) :=
  match original : origin.instruction? input with
  | none => none
  | some instruction =>
      if accepted : input.law.Valid instruction.before instruction.request then
        match operation : instruction.request.operation with
        | .settle instrument debtor holder quantity =>
            if instrument_eq : instrument = claim.instrument then
              if debtor_eq : debtor = claim.debtor then
                some ⟨origin, instruction, original, .payment (holderIndex input holder),
                  quantity, by
                    simpa only [reviewOperation, holderParty_index, ← instrument_eq, ← debtor_eq] using operation,
                  accepted⟩
              else none
            else none
        | .assign instrument debtor sender recipient quantity =>
            if instrument_eq : instrument = claim.instrument then
              if debtor_eq : debtor = claim.debtor then
                some ⟨origin, instruction, original,
                  .assignment (holderIndex input sender) (holderIndex input recipient),
                  quantity, by
                    simpa only [reviewOperation, holderParty_index, ← instrument_eq, ← debtor_eq] using operation,
                  accepted⟩
              else none
            else none
        | .produce _ | .transfer _ _ _ | .use _ _ _ | .issue _ _ _ _ | .revise _ _ | .present => none
      else none

omit [DecidableEq Port] in
theorem readReview_payment_complete (claim : IssuedClaim input) (origin : InstructionOrigin input)
    (instruction : ExecutionItem Party Good Port Technology Instrument)
    (original : origin.instruction? input = some instruction)
    (holder : Party) (quantity : ℚ)
    (operation : instruction.request.operation = .settle claim.instrument claim.debtor holder quantity)
    (accepted : input.law.Valid instruction.before instruction.request) :
    ∃ receipt, readReview input claim origin = some receipt ∧
      receipt.origin = origin ∧ receipt.kind = .payment (holderIndex input holder) ∧
      receipt.quantity = quantity := by
  unfold readReview
  split
  · rename_i absent
    have impossible := absent.symm.trans original
    cases impossible
  · rename_i actual actualEq
    have same := Option.some.inj (actualEq.symm.trans original)
    subst actual
    rw [dif_pos accepted]
    split <;> rename_i branchEq
    all_goals cases (operation.symm.trans branchEq)
    simp only
    exact ⟨_, rfl, rfl, rfl, rfl⟩

omit [DecidableEq Port] in
theorem readReview_assignment_complete (claim : IssuedClaim input) (origin : InstructionOrigin input)
    (instruction : ExecutionItem Party Good Port Technology Instrument)
    (original : origin.instruction? input = some instruction)
    (sender recipient : Party) (quantity : ℚ)
    (operation : instruction.request.operation = .assign claim.instrument claim.debtor sender recipient quantity)
    (accepted : input.law.Valid instruction.before instruction.request) :
    ∃ receipt, readReview input claim origin = some receipt ∧
      receipt.origin = origin ∧
      receipt.kind = .assignment (holderIndex input sender) (holderIndex input recipient) ∧
      receipt.quantity = quantity := by
  unfold readReview
  split
  · rename_i absent
    have impossible := absent.symm.trans original
    cases impossible
  · rename_i actual actualEq
    have same := Option.some.inj (actualEq.symm.trans original)
    subst actual
    rw [dif_pos accepted]
    split <;> rename_i branchEq
    all_goals cases (operation.symm.trans branchEq)
    simp only
    exact ⟨_, rfl, rfl, rfl, rfl⟩

omit [DecidableEq Port] in
theorem readReview_origin (claim : IssuedClaim input) (origin : InstructionOrigin input)
    (receipt : Review input claim) (returned : readReview input claim origin = some receipt) :
    receipt.origin = origin := by
  unfold readReview at returned
  repeat' first
    | rfl
    | contradiction
    | split at returned
    | (cases Option.some.inj returned; rfl)

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial
