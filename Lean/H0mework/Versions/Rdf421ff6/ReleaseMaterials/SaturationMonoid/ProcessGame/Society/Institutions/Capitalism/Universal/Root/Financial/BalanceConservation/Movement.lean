import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation.Effects
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation.Scan
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation.SourceFacts
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.FinancialFlow

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation

open ResponsibilityLifecycle Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

def movementDelta {origin : InstructionOrigin input} (movement : Movement input origin)
    (amount : ℚ) (instrument : Instrument) (debtor creditor : Party) : ℚ :=
  if movement.instrument = instrument ∧ movement.debtor = debtor then
    -(if movement.sender = creditor then amount else 0) +
      match movement.kind with
      | .payment => 0
      | .assignment => if movement.recipient = creditor then amount else 0
  else 0

omit [DecidableEq Port] in
theorem movementDelta_zero {origin : InstructionOrigin input} (movement : Movement input origin)
    (instrument : Instrument) (debtor creditor : Party) :
    movementDelta input movement 0 instrument debtor creditor = 0 := by
  unfold movementDelta
  split_ifs <;> cases movement.kind <;> simp

omit [DecidableEq Port] in
theorem movementDelta_add {origin : InstructionOrigin input} (movement : Movement input origin)
    (left right : ℚ) (instrument : Instrument) (debtor creditor : Party) :
    movementDelta input movement (left + right) instrument debtor creditor =
      movementDelta input movement left instrument debtor creditor +
        movementDelta input movement right instrument debtor creditor := by
  cases kind : movement.kind <;> simp only [movementDelta, kind] <;> split_ifs <;> ring

omit [DecidableEq Port] in
theorem movementDelta_actual {origin : InstructionOrigin input} (movement : Movement input origin)
    (instrument : Instrument) (debtor creditor : Party) :
    movementDelta input movement movement.quantity instrument debtor creditor =
      RawLaw.claimDelta movement.instruction.request instrument debtor creditor := by
  unfold RawLaw.claimDelta
  rw [movement.operation_exact]
  cases kind : movement.kind <;>
    by_cases sameInstrument : instrument = movement.instrument <;>
    by_cases sameDebtor : debtor = movement.debtor <;>
    by_cases sameSender : creditor = movement.sender <;>
    by_cases sameRecipient : creditor = movement.recipient <;>
    simp [movementDelta, kind, Prod.mk.injEq, eq_comm, sameInstrument, sameDebtor,
      sameSender, sameRecipient]

omit [DecidableEq Port] in
theorem selected_review_delta {origin : InstructionOrigin input} (movement : Movement input origin)
    {claim : IssuedClaim input} (review : Review input claim)
    (selected : readReview input claim origin = some review)
    (amount : ℚ) (instrument : Instrument) (debtor creditor : Party) :
    reviewDelta input review amount instrument debtor creditor =
      movementDelta input movement amount instrument debtor creditor := by
  have operation := review.operation_exact
  rw [selected_review_instruction input movement review selected, movement.operation_exact] at operation
  cases kind : movement.kind <;> cases reviewKind : review.kind <;>
    simp_all [reviewOperation, reviewDelta, movementDelta]

omit [DecidableEq Port] in
theorem movement_source_quantity {origin : InstructionOrigin input} (movement : Movement input origin) :
    ReviewQuantityAt input origin movement.quantity := by
  intro claim review selected
  exact (selected_review_keys input movement review selected).2.2.2

theorem movement_capacity {origin : InstructionOrigin input} (movement : Movement input origin)
    (slot : ObligationSlot (vocabulary input)) :
    reviewCapacity input origin slot =
      slotClaims input slot movement.instrument movement.debtor movement.sender := by
  cases slot with
  | terminal archive => simp [reviewCapacity]
  | live obligation =>
      cases selected : readReview input obligation.content origin with
      | none =>
          by_cases sameInstrument : obligation.content.instrument = movement.instrument
          · by_cases sameDebtor : obligation.content.debtor = movement.debtor
            · obtain ⟨review, found⟩ := matching_review_exists input movement obligation.content
                sameInstrument sameDebtor
              rw [selected] at found
              contradiction
            · simp [reviewCapacity, selected, slotClaims, slotClaim, slotObligation, sameDebtor]
          · simp [reviewCapacity, selected, slotClaims, slotClaim, slotObligation, sameInstrument]
      | some review =>
          obtain ⟨sameInstrument, sameDebtor, sameHolder, _⟩ :=
            selected_review_keys input movement review selected
          simp only [reviewCapacity, selected, slotClaims, slotClaim, slotObligation, slotBalance,
            sameInstrument, sameDebtor, and_self, ↓reduceIte]
          rw [← sameHolder, shareAt_key]

theorem movement_full_capacity {origin : InstructionOrigin input} (movement : Movement input origin)
    (state : ResponsibilityState (vocabulary input)) :
    suffixCapacity input origin state 0 =
      ledgerClaims input state movement.instrument movement.debtor movement.sender := by
  simp only [suffixCapacity, List.drop_zero, ledgerClaims]
  congr 1
  apply List.map_congr_left
  intro slot _
  exact movement_capacity input movement slot

theorem allocateAt_ledgerClaims {origin : InstructionOrigin input} (movement : Movement input origin)
    (state : (process input).GeneratedState) (position : Nat)
    (available : ℚ) (nonnegative : 0 ≤ available)
    (instrument : Instrument) (debtor creditor : Party) :
    ledgerClaims input (allocateAt input origin state position available nonnegative).after.current
        instrument debtor creditor =
      ledgerClaims input state.current instrument debtor creditor +
        movementDelta input movement
          ((allocateAt input origin state position available nonnegative).used input)
          instrument debtor creditor := by
  unfold allocateAt
  split_ifs
  · split
    · simp only [Allocation.idle, Allocation.used, sub_self, movementDelta_zero, add_zero]
    · split
      · simp only [Allocation.idle, Allocation.used, sub_self, movementDelta_zero, add_zero]
      next review selected =>
        rw [allocateLive_ledgerClaims, selected_review_delta input movement review selected]
  · simp only [Allocation.idle, Allocation.used, sub_self, movementDelta_zero, add_zero]

theorem allocateFrom_ledgerClaims {origin : InstructionOrigin input} (movement : Movement input origin)
    (fuel position : Nat) (state : (process input).GeneratedState)
    (available : ℚ) (nonnegative : 0 ≤ available)
    (instrument : Instrument) (debtor creditor : Party) :
    ledgerClaims input (allocateFrom input origin position fuel state available nonnegative).after.current
        instrument debtor creditor =
      ledgerClaims input state.current instrument debtor creditor +
        movementDelta input movement
          ((allocateFrom input origin position fuel state available nonnegative).used input)
          instrument debtor creditor := by
  induction fuel generalizing position state available with
  | zero => simp only [allocateFrom, Allocation.idle, Allocation.used, sub_self, movementDelta_zero, add_zero]
  | succ fuel ih =>
      let first := allocateAt input origin state position available nonnegative
      let rest := allocateFrom input origin (position + 1) fuel first.after
        first.remaining first.remaining_nonnegative
      change ledgerClaims input rest.after.current instrument debtor creditor =
        ledgerClaims input state.current instrument debtor creditor +
          movementDelta input movement ((first.append input rest).used input) instrument debtor creditor
      rw [Allocation.used_append, movementDelta_add]
      have later := ih (position + 1) first.after first.remaining first.remaining_nonnegative
      have earlier := allocateAt_ledgerClaims input movement state position available nonnegative
        instrument debtor creditor
      change ledgerClaims input rest.after.current instrument debtor creditor = _ at later
      change ledgerClaims input first.after.current instrument debtor creditor = _ at earlier
      linarith

theorem matched_movement_quota_exhausted {origin : InstructionOrigin input}
    (movement : Movement input origin) (state : (process input).GeneratedState)
    (matched : ledgerClaims input state.current = movement.instruction.before.claims) :
    (allocate input origin state movement.quantity (movement.quantity_nonnegative input)).remaining = 0 := by
  rw [allocate_remaining input origin movement.quantity (movement_source_quantity input movement),
    movement_full_capacity input movement, matched]
  have guarded := movement.accepted.2.2.1
  unfold RawLaw.ClaimGuard at guarded
  rw [movement.operation_exact] at guarded
  have covered : movement.quantity ≤ movement.instruction.before.claims
      movement.instrument movement.debtor movement.sender := by
    cases kind : movement.kind with
    | payment =>
        simp only [kind] at guarded
        exact guarded.2.1
    | assignment =>
        simp only [kind] at guarded
        exact guarded.2
  exact max_eq_right (sub_nonpos.mpr covered)

theorem matched_movement_claims {origin : InstructionOrigin input}
    (movement : Movement input origin) (state : (process input).GeneratedState)
    (matched : ledgerClaims input state.current = movement.instruction.before.claims) :
    ledgerClaims input
      (allocate input origin state movement.quantity (movement.quantity_nonnegative input)).after.current =
      (input.law.step movement.instruction.before movement.instruction.request).claims := by
  funext instrument debtor creditor
  have effects := allocateFrom_ledgerClaims input movement state.current.slots.length 0 state
    movement.quantity (movement.quantity_nonnegative input) instrument debtor creditor
  have consumed : (allocate input origin state movement.quantity
      (movement.quantity_nonnegative input)).used input = movement.quantity := by
    rw [Allocation.used, matched_movement_quota_exhausted input movement state matched, sub_zero]
  change ledgerClaims input (allocate input origin state movement.quantity
    (movement.quantity_nonnegative input)).after.current instrument debtor creditor = _ at effects
  dsimp only [allocate] at consumed
  rw [effects, consumed, matched]
  rw [input.law.step_financial_balance, input.law.accepted_delta _ _ movement.accepted,
    movementDelta_actual]

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation
