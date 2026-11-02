import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Instruction

/-! Financial participants come from the current original instruction and the
first M0 birth in its actual root history.  A matrix entry supplies no actor. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation

open ResponsibilityLifecycle Source.Program Source.ProgrammeFace

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

omit [DecidableEq Port] in
theorem original_request_mem_word (origin : InstructionOrigin input)
    (instruction : ExecutionItem Party Good Port Technology Instrument)
    (exactInstruction : origin.instruction? input = some instruction) :
    instruction.request ∈ ProgrammeSource.rawEvent input origin.visit.current := by
  have actual := origin.instruction_mem input instruction exactInstruction
  have mapped : instruction.request ∈
      (input.law.rawItems (ProgrammeSource.rawCurrent input origin.visit.current)
        (ProgrammeSource.rawEvent input origin.visit.current)).map ExecutionItem.request :=
    List.mem_map.mpr ⟨instruction, actual, rfl⟩
  simpa only [RawLaw.rawItems, RawLaw.inventory_requests_exact] using mapped

def movement_sender_birth {origin : InstructionOrigin input} (movement : Movement input origin) :
    ActualBirth.At input origin.visit movement.sender :=
  origin.participantBirth input movement.instruction movement.original movement.sender (by
    rw [movement.operation_exact]
    cases movement.kind <;> simp [operationParties])

def movement_recipient_birth {origin : InstructionOrigin input} (movement : Movement input origin)
    (assignment : movement.kind = .assignment) : ActualBirth.At input origin.visit movement.recipient :=
  origin.participantBirth input movement.instruction movement.original movement.recipient (by
    rw [movement.operation_exact, assignment]
    simp [operationParties])

omit [DecidableEq Port] in
theorem selected_review_instruction {origin : InstructionOrigin input}
    (movement : Movement input origin) {claim : IssuedClaim input} (review : Review input claim)
    (selected : readReview input claim origin = some review) :
    review.instruction = movement.instruction := by
  have actual := review.instruction_exact
  rw [readReview_origin input claim origin review selected] at actual
  exact Option.some.inj (actual.symm.trans movement.original)

omit [DecidableEq Port] in
theorem selected_review_keys {origin : InstructionOrigin input}
    (movement : Movement input origin) {claim : IssuedClaim input} (review : Review input claim)
    (selected : readReview input claim origin = some review) :
    claim.instrument = movement.instrument ∧ claim.debtor = movement.debtor ∧
      holderParty input (review.fromHolder input) = movement.sender ∧
      review.quantity = movement.quantity := by
  have operation := review.operation_exact
  rw [selected_review_instruction input movement review selected, movement.operation_exact] at operation
  cases kind : movement.kind <;> cases reviewKind : review.kind <;>
    simp_all [reviewOperation, Review.fromHolder]

omit [DecidableEq Port] in
theorem matching_review_exists {origin : InstructionOrigin input}
    (movement : Movement input origin) (claim : IssuedClaim input)
    (sameInstrument : claim.instrument = movement.instrument)
    (sameDebtor : claim.debtor = movement.debtor) :
    ∃ review, readReview input claim origin = some review := by
  cases kind : movement.kind with
  | payment =>
      obtain ⟨review, selected, _⟩ := readReview_payment_complete input claim origin
        movement.instruction movement.original movement.sender movement.quantity
        (by simpa only [kind, sameInstrument, sameDebtor] using movement.operation_exact)
        movement.accepted
      exact ⟨review, selected⟩
  | assignment =>
      obtain ⟨review, selected, _⟩ := readReview_assignment_complete input claim origin
        movement.instruction movement.original movement.sender movement.recipient movement.quantity
        (by simpa only [kind, sameInstrument, sameDebtor] using movement.operation_exact)
        movement.accepted
      exact ⟨review, selected⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation
