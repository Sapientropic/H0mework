import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation.Movement
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.BalanceConservation.Effects
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.BalanceConservation.Scan
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.BalanceConservation.SourceFacts
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.FinancialFlow

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.BalanceConservation

open ResponsibilityLifecycle Source.Program

variable {Party Good Port Technology Instrument Index : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (sources : Index → ProgrammeSource.Input Party Good Port Technology Instrument)

omit [DecidableEq Port] in
theorem selected_review_delta {origin : Origin sources}
    (movement : Movement (sources origin.1) origin.2)
    (emitted : readMovement (sources origin.1) origin.2 = some movement)
    {claim : Claim sources} (review : Review sources claim)
    (selected : readReview sources claim origin = some review)
    (amount : ℚ) (instrument : Instrument) (debtor creditor : Party) :
    reviewDelta sources review amount instrument debtor creditor =
      Financial.BalanceConservation.movementDelta (sources origin.1) movement amount instrument debtor creditor := by
  obtain ⟨i, d, k, s, r, _⟩ := selected_review_keys sources movement emitted review selected
  simp only [reviewDelta, Financial.BalanceConservation.movementDelta, i, d, k, s, r]
  rfl

omit [DecidableEq Port] in
theorem movement_source_quantity {origin : Origin sources}
    (movement : Movement (sources origin.1) origin.2)
    (emitted : readMovement (sources origin.1) origin.2 = some movement) :
    ReviewQuantityAt sources origin movement.quantity := by
  intro claim review selected
  exact (selected_review_keys sources movement emitted review selected).2.2.2.2.2

theorem movement_capacity {origin : Origin sources} (movement : Movement (sources origin.1) origin.2)
    (emitted : readMovement (sources origin.1) origin.2 = some movement)
    (slot : ObligationSlot (vocabulary sources))
    (compatible : DenominatedAt sources origin.1 (slotClaim sources slot)) :
    reviewCapacity sources origin slot =
      slotClaims sources slot movement.instrument movement.debtor movement.sender := by
  cases slot with
  | terminal archive => simp [reviewCapacity, slotClaims, slotBalance]
  | live obligation =>
      cases selected : readReview sources obligation.content origin with
      | none =>
          by_cases sameInstrument : obligation.content.2.instrument = movement.instrument
          · by_cases sameDebtor : obligation.content.2.debtor = movement.debtor
            · obtain ⟨review, found⟩ := matching_review_exists sources movement emitted obligation.content
                sameInstrument sameDebtor compatible
              rw [selected] at found
              contradiction
            · simp [reviewCapacity, selected, slotClaims, slotClaim, slotObligation, sameDebtor]
          · simp [reviewCapacity, selected, slotClaims, slotClaim, slotObligation, sameInstrument]
      | some review =>
          obtain ⟨sameInstrument, sameDebtor, _, sameHolder, _⟩ :=
            selected_review_keys sources movement emitted review selected
          simp only [reviewCapacity, selected, slotClaims, slotClaim, slotObligation, slotBalance,
            sameInstrument, sameDebtor, and_self, ↓reduceIte]
          rw [sameHolder]

theorem movement_full_capacity {origin : Origin sources} (movement : Movement (sources origin.1) origin.2)
    (emitted : readMovement (sources origin.1) origin.2 = some movement)
    (state : ResponsibilityState (vocabulary sources)) (compatible : Compatible sources origin.1 state) :
    suffixCapacity sources origin state 0 =
      ledgerClaims sources state movement.instrument movement.debtor movement.sender := by
  simp only [suffixCapacity, List.drop_zero, ledgerClaims]
  congr 1
  apply List.map_congr_left
  intro slot member
  exact movement_capacity sources movement emitted slot (compatible _ (List.mem_map.mpr ⟨slot, member, rfl⟩))

theorem allocateAt_ledgerClaims {origin : Origin sources} (movement : Movement (sources origin.1) origin.2)
    (emitted : readMovement (sources origin.1) origin.2 = some movement)
    (state : (process sources).GeneratedState) (position : Nat)
    (available : ℚ) (nonnegative : 0 ≤ available)
    (instrument : Instrument) (debtor creditor : Party) :
    ledgerClaims sources (allocateAt sources origin state position available nonnegative).after.current
        instrument debtor creditor =
      ledgerClaims sources state.current instrument debtor creditor +
        Financial.BalanceConservation.movementDelta (sources origin.1) movement
          ((allocateAt sources origin state position available nonnegative).used sources)
          instrument debtor creditor := by
  unfold allocateAt
  split_ifs
  · split
    · simp only [Allocation.idle, Allocation.used, sub_self, Financial.BalanceConservation.movementDelta_zero, add_zero]
    · split
      · simp only [Allocation.idle, Allocation.used, sub_self, Financial.BalanceConservation.movementDelta_zero, add_zero]
      next review selected =>
        rw [allocateLive_ledgerClaims, selected_review_delta sources movement emitted review selected]
  · simp only [Allocation.idle, Allocation.used, sub_self, Financial.BalanceConservation.movementDelta_zero, add_zero]

theorem allocateFrom_ledgerClaims {origin : Origin sources} (movement : Movement (sources origin.1) origin.2)
    (emitted : readMovement (sources origin.1) origin.2 = some movement)
    (fuel position : Nat) (state : (process sources).GeneratedState)
    (available : ℚ) (nonnegative : 0 ≤ available)
    (instrument : Instrument) (debtor creditor : Party) :
    ledgerClaims sources (allocateFrom sources origin position fuel state available nonnegative).after.current
        instrument debtor creditor =
      ledgerClaims sources state.current instrument debtor creditor +
        Financial.BalanceConservation.movementDelta (sources origin.1) movement
          ((allocateFrom sources origin position fuel state available nonnegative).used sources)
          instrument debtor creditor := by
  induction fuel generalizing position state available with
  | zero => simp only [allocateFrom, Allocation.idle, Allocation.used, sub_self, Financial.BalanceConservation.movementDelta_zero, add_zero]
  | succ fuel ih =>
      let first := allocateAt sources origin state position available nonnegative
      let rest := allocateFrom sources origin (position + 1) fuel first.after
        first.remaining first.remaining_nonnegative
      change ledgerClaims sources rest.after.current instrument debtor creditor =
        ledgerClaims sources state.current instrument debtor creditor +
          Financial.BalanceConservation.movementDelta (sources origin.1) movement ((first.append sources rest).used sources) instrument debtor creditor
      rw [Allocation.used_append, Financial.BalanceConservation.movementDelta_add]
      have later := ih (position + 1) first.after first.remaining first.remaining_nonnegative
      have earlier := allocateAt_ledgerClaims sources movement emitted state position available nonnegative
        instrument debtor creditor
      change ledgerClaims sources rest.after.current instrument debtor creditor = _ at later
      change ledgerClaims sources first.after.current instrument debtor creditor = _ at earlier
      linarith

theorem matched_movement_quota_exhausted {origin : Origin sources}
    (movement : Movement (sources origin.1) origin.2)
    (emitted : readMovement (sources origin.1) origin.2 = some movement) (state : (process sources).GeneratedState)
    (compatible : Compatible sources origin.1 state.current)
    (matched : ledgerClaims sources state.current = movement.instruction.before.claims) :
    (allocate sources origin state movement.quantity (movement.quantity_nonnegative (sources origin.1))).remaining = 0 := by
  rw [allocate_remaining sources origin movement.quantity (movement_source_quantity sources movement emitted),
    movement_full_capacity sources movement emitted _ compatible, matched]
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

theorem matched_movement_claims {origin : Origin sources}
    (movement : Movement (sources origin.1) origin.2)
    (emitted : readMovement (sources origin.1) origin.2 = some movement) (state : (process sources).GeneratedState)
    (compatible : Compatible sources origin.1 state.current)
    (matched : ledgerClaims sources state.current = movement.instruction.before.claims) :
    ledgerClaims sources
      (allocate sources origin state movement.quantity (movement.quantity_nonnegative (sources origin.1))).after.current =
      ((sources origin.1).law.step movement.instruction.before movement.instruction.request).claims := by
  funext instrument debtor creditor
  have effects := allocateFrom_ledgerClaims sources movement emitted state.current.slots.length 0 state
    movement.quantity (movement.quantity_nonnegative (sources origin.1)) instrument debtor creditor
  have consumed : (allocate sources origin state movement.quantity
      (movement.quantity_nonnegative (sources origin.1))).used sources = movement.quantity := by
    rw [Allocation.used, matched_movement_quota_exhausted sources movement emitted state compatible matched, sub_zero]
  change ledgerClaims sources (allocate sources origin state movement.quantity
    (movement.quantity_nonnegative (sources origin.1))).after.current instrument debtor creditor = _ at effects
  dsimp only [allocate] at consumed
  rw [effects, consumed, matched]
  rw [(sources origin.1).law.step_financial_balance, (sources origin.1).law.accepted_delta _ _ movement.accepted,
    Financial.BalanceConservation.movementDelta_actual]

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.BalanceConservation
