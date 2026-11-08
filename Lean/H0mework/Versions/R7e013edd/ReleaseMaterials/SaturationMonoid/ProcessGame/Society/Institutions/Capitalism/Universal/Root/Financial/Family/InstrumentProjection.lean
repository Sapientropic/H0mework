import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.BalanceConservation.Execution

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.InstrumentProjection
open ResponsibilityLifecycle Source.Program Source.ProgrammeFace Financial.Family.BalanceConservation

variable {Party Good Port Technology Instrument Index : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (sources : Index → ProgrammeSource.Input Party Good Port Technology Instrument)

theorem movement_quota_is_paid_from_its_own_instrument {origin : Origin sources}
    (movement : Movement (sources origin.1) origin.2)
    (emitted : readMovement (sources origin.1) origin.2 = some movement)
    (state : (process sources).GeneratedState)
    (compatible : Compatible sources origin.1 state.current)
    (matched : ledgerClaims sources state.current movement.instrument =
      movement.instruction.before.claims movement.instrument) :
    (allocate sources origin state movement.quantity (movement.quantity_nonnegative (sources origin.1))).remaining = 0 := by
  rw [allocate_remaining sources origin movement.quantity (movement_source_quantity sources movement emitted),
    movement_full_capacity sources movement emitted _ compatible, matched]
  have guarded := movement.accepted.2.2.1
  unfold RawLaw.ClaimGuard at guarded
  rw [movement.operation_exact] at guarded
  have covered : movement.quantity ≤ movement.instruction.before.claims
      movement.instrument movement.debtor movement.sender := by
    cases kind : movement.kind with
    | payment => simp only [kind] at guarded; exact guarded.2.1
    | assignment => simp only [kind] at guarded; exact guarded.2
  exact max_eq_right (sub_nonpos.mpr covered)

theorem movement_preserves_the_selected_source_slice {origin : Origin sources}
    (movement : Movement (sources origin.1) origin.2)
    (emitted : readMovement (sources origin.1) origin.2 = some movement)
    (state : (process sources).GeneratedState) (instrument : Instrument)
    (compatible : Compatible sources origin.1 state.current)
    (matched : ledgerClaims sources state.current instrument = movement.instruction.before.claims instrument) :
    ledgerClaims sources
      (allocate sources origin state movement.quantity (movement.quantity_nonnegative (sources origin.1))).after.current instrument =
      ((sources origin.1).law.step movement.instruction.before movement.instruction.request).claims instrument := by
  funext debtor creditor
  have effects := allocateFrom_ledgerClaims sources movement emitted state.current.slots.length 0 state
    movement.quantity (movement.quantity_nonnegative (sources origin.1)) instrument debtor creditor
  change ledgerClaims sources (allocate sources origin state movement.quantity
    (movement.quantity_nonnegative (sources origin.1))).after.current instrument debtor creditor = _ at effects
  rw [effects, matched]
  rw [(sources origin.1).law.step_financial_balance, (sources origin.1).law.accepted_delta _ _ movement.accepted,
    ← Financial.BalanceConservation.movementDelta_actual]
  by_cases same : movement.instrument = instrument
  · have paid := movement_quota_is_paid_from_its_own_instrument sources movement emitted state compatible
      (by simpa only [same] using matched)
    have consumed : (allocate sources origin state movement.quantity
        (movement.quantity_nonnegative (sources origin.1))).used sources = movement.quantity := by
      rw [Allocation.used, paid, sub_zero]
    dsimp only [allocate] at consumed
    rw [consumed]
  · simp only [Financial.BalanceConservation.movementDelta, same, false_and, ↓reduceIte]

theorem issue_preserves_the_selected_source_slice (claim : Claim sources)
    (state : (process sources).GeneratedState) (instrument : Instrument)
    (matched : ledgerClaims sources state.current instrument = claim.2.instruction.before.claims instrument) :
    ledgerClaims sources (admit sources state claim).current instrument =
      ((sources claim.1).law.step claim.2.instruction.before claim.2.instruction.request).claims instrument := by
  funext debtor creditor
  rw [admit_ledgerClaims, matched]
  simp only [RawLaw.step, if_pos claim.2.accepted, RawLaw.paidStep, RawLaw.nextClaims, claim.2.issue_exact]

theorem consume_preserves_the_selected_source_slice (origin : Origin sources)
    (state : (process sources).GeneratedState)
    (instruction : ExecutionItem Party Good Port Technology Instrument)
    (original : origin.2.instruction? (sources origin.1) = some instruction) (instrument : Instrument)
    (compatible : Compatible sources origin.1 state.current)
    (matched : ledgerClaims sources state.current instrument = instruction.before.claims instrument) :
    ledgerClaims sources ((consume sources origin state).next sources).current instrument =
      ((sources origin.1).law.step instruction.before instruction.request).claims instrument := by
  by_cases accepted : (sources origin.1).law.Valid instruction.before instruction.request
  · cases operation : instruction.request.operation
    case issue issued debtor holder quantity =>
        obtain ⟨claim, sameOrigin, emitted, sameInstruction⟩ := Financial.BalanceConservation.issue_readout_issued
          (sources origin.1) origin.2 instruction original issued debtor holder quantity operation accepted
        simp only [consume, emitted, InstructionResult.next]
        have sourceMatched : ledgerClaims sources state.current instrument = claim.instruction.before.claims instrument := by
          rw [sameInstruction]; exact matched
        simpa only [sameInstruction] using issue_preserves_the_selected_source_slice sources ⟨origin.1, claim⟩ state instrument sourceMatched
    case settle moved debtor holder quantity =>
        have noIssue := Financial.BalanceConservation.issue_readout_nonissue (sources origin.1) origin.2 instruction original
          (by intro i d h q; simp [operation])
        obtain ⟨movement, emitted⟩ := Financial.BalanceConservation.payment_readout_exists (sources origin.1) origin.2
          instruction original moved debtor holder quantity operation accepted
        simp only [consume, noIssue, emitted, InstructionResult.next]
        have same := Option.some.inj (movement.original.symm.trans original)
        have sourceMatched : ledgerClaims sources state.current instrument = movement.instruction.before.claims instrument := by
          rw [same]; exact matched
        simpa only [same] using movement_preserves_the_selected_source_slice sources movement emitted state instrument compatible sourceMatched
    case assign moved debtor sender recipient quantity =>
        have noIssue := Financial.BalanceConservation.issue_readout_nonissue (sources origin.1) origin.2 instruction original
          (by intro i d h q; simp [operation])
        obtain ⟨movement, emitted⟩ := Financial.BalanceConservation.assignment_readout_exists (sources origin.1) origin.2
          instruction original moved debtor sender recipient quantity operation accepted
        simp only [consume, noIssue, emitted, InstructionResult.next]
        have same := Option.some.inj (movement.original.symm.trans original)
        have sourceMatched : ledgerClaims sources state.current instrument = movement.instruction.before.claims instrument := by
          rw [same]; exact matched
        simpa only [same] using movement_preserves_the_selected_source_slice sources movement emitted state instrument compatible sourceMatched
    all_goals
      have noIssue := Financial.BalanceConservation.issue_readout_nonissue (sources origin.1) origin.2 instruction original
        (by intro i d h q; simp [operation])
      have noMovement := Financial.BalanceConservation.movement_readout_nonmovement (sources origin.1) origin.2 instruction original
        (by intro i d h q; simp [operation]) (by intro i d s r q; simp [operation])
      simp only [consume, noIssue, noMovement, InstructionResult.next]
      simpa only [RawLaw.step, if_pos accepted, RawLaw.paidStep, RawLaw.nextClaims, operation] using matched
  · rw [consume_refused sources origin state instruction original accepted,
      (sources origin.1).law.rejected_preserves_current instruction.before instruction.request accepted]
    exact matched

theorem consume_origins_execute (sourceIndex : Index)
    (origins : List (InstructionOrigin (sources sourceIndex))) (state : (process sources).GeneratedState)
    (current : RawCurrent Party Good Technology Instrument) (index : Nat)
    (event : RawEvent Party Good Port Technology Instrument) (instrument : Instrument)
    (sequence : origins.filterMap (InstructionOrigin.instruction? (sources sourceIndex)) =
      ((sources sourceIndex).law.execute current index event).items)
    (compatible : Compatible sources sourceIndex state.current)
    (matched : ledgerClaims sources state.current instrument = current.claims instrument) :
    ledgerClaims sources (consumeOrigins sources (origins.map (Sigma.mk sourceIndex)) state).current instrument =
      ((sources sourceIndex).law.execute current index event).final.claims instrument := by
  induction origins generalizing state current index event with
  | nil =>
    have empty : event.length = 0 := by
      rw [← (sources sourceIndex).law.inventory_length current index event, ← sequence]; rfl
    cases event with
    | nil => exact matched
    | cons request rest => simp at empty
  | cons origin rest ih =>
    cases decoded : origin.instruction? (sources sourceIndex) with
    | none =>
      simp only [List.filterMap_cons, decoded] at sequence
      change ledgerClaims sources (consumeOrigins sources (rest.map (Sigma.mk sourceIndex))
        ((consume sources ⟨sourceIndex, origin⟩ state).next sources)).current instrument = _
      rw [consume_without_instruction sources ⟨sourceIndex, origin⟩ state decoded]
      exact ih state current index event sequence compatible matched
    | some instruction =>
      cases event with
      | nil => simp only [List.filterMap_cons, decoded, RawLaw.execute, List.cons_ne_nil] at sequence
      | cons request remaining =>
        have aligned : instruction :: rest.filterMap (InstructionOrigin.instruction? (sources sourceIndex)) =
            ⟨index, current, request⟩ :: ((sources sourceIndex).law.execute
              ((sources sourceIndex).law.step current request) (index + 1) remaining).items := by
          simpa only [List.filterMap_cons, decoded, RawLaw.execute] using sequence
        obtain ⟨same, after⟩ := List.cons.inj aligned
        have localMatch : ledgerClaims sources state.current instrument = instruction.before.claims instrument := by
          rw [same]; exact matched
        have updated := consume_preserves_the_selected_source_slice sources ⟨sourceIndex, origin⟩ state
          instruction decoded instrument compatible localMatch
        rw [same] at updated
        exact ih ((consume sources ⟨sourceIndex, origin⟩ state).next sources)
          ((sources sourceIndex).law.step current request) (index + 1) remaining after
          (consume_compatible sources sourceIndex origin state compatible) updated

theorem consume_visit_source_slice (sourceIndex : Index) (ordinal : Nat)
    (state : (process sources).GeneratedState) (instrument : Instrument)
    (compatible : Compatible sources sourceIndex state.current)
    (matched : ledgerClaims sources state.current instrument =
      (ProgrammeSource.rawCurrent (sources sourceIndex) (ProgrammeHistory.visitAt (sources sourceIndex) ordinal).current).claims instrument) :
    ledgerClaims sources (consumeVisit sources sourceIndex ordinal state).current instrument =
      (ProgrammeSource.rawCurrent (sources sourceIndex) (ProgrammeHistory.visitAt (sources sourceIndex) (ordinal + 1)).current).claims instrument := by
  change ledgerClaims sources (consumeVisit sources sourceIndex ordinal state).current instrument =
    (ProgrammeSource.rawCurrent (sources sourceIndex) (ProgrammeSource.next (sources sourceIndex)
      (ProgrammeHistory.visitAt (sources sourceIndex) ordinal).current)).claims instrument
  rw [ProgrammeSource.actual_raw_next]
  exact consume_origins_execute sources sourceIndex _ state _ 0 _ instrument
    (Financial.inventoryAt_instructions_exact _ _) compatible matched

theorem continue_visits_source_slice (sourceIndex : Index) (start count : Nat)
    (state : (process sources).GeneratedState) (instrument : Instrument)
    (compatible : Compatible sources sourceIndex state.current)
    (matched : ledgerClaims sources state.current instrument =
      (ProgrammeSource.rawCurrent (sources sourceIndex) (ProgrammeHistory.visitAt (sources sourceIndex) start).current).claims instrument) :
    ledgerClaims sources (continueVisits sources sourceIndex start count state).current instrument =
      (ProgrammeSource.rawCurrent (sources sourceIndex) (ProgrammeHistory.visitAt (sources sourceIndex) (start + count)).current).claims instrument := by
  induction count with
  | zero => exact matched
  | succ count ih =>
    exact consume_visit_source_slice sources sourceIndex _ _ instrument
      (continueVisits_compatible sources sourceIndex start count state compatible) ih

def acceptedIssue (law : RawLaw Party Good Port Technology Instrument)
    (item : ExecutionItem Party Good Port Technology Instrument) : Bool :=
  match item.request.operation with
  | .issue _ _ _ _ => decide (law.Valid item.before item.request)
  | _ => false

omit [DecidableEq Port] in
theorem issued_origin_is_the_actual_accepted_issue (sourceIndex : Index)
    (origin : InstructionOrigin (sources sourceIndex)) :
    (originsClaim? sources ⟨sourceIndex, origin⟩).isSome =
      (origin.instruction? (sources sourceIndex)).any (acceptedIssue (sources sourceIndex).law) := by
  unfold originsClaim?
  dsimp only
  cases original : origin.instruction? (sources sourceIndex) with
  | none => rw [Financial.BalanceConservation.issue_readout_absent _ _ original]; rfl
  | some item =>
    cases operation : item.request.operation
    case issue instrument debtor holder quantity =>
      by_cases accepted : (sources sourceIndex).law.Valid item.before item.request
      · obtain ⟨claim, exactOrigin, emitted, _⟩ := Financial.BalanceConservation.issue_readout_issued
          (sources sourceIndex) origin item original instrument debtor holder quantity operation accepted
        rw [emitted]
        simp [acceptedIssue, operation, accepted]
      · simp only [Option.any_some, acceptedIssue, operation, decide_eq_false accepted]
        cases selected : readIssue (sources sourceIndex) origin <;> try rfl
        rename_i claim sameOrigin
        have identical := claim.instruction_exact
        rw [sameOrigin, original] at identical
        have valid := claim.accepted
        rw [← Option.some.inj identical] at valid
        exact (accepted valid).elim
    all_goals
      have noIssue := Financial.BalanceConservation.issue_readout_nonissue (sources sourceIndex) origin item original
        (by intro i d h q; simp [operation])
      rw [noIssue]
      simp only [Option.isSome_none, Option.any_some, acceptedIssue, operation]

omit [DecidableEq Port] in
theorem native_issued_claim_count_is_actual_item_count (sourceIndex : Index)
    (origins : List (InstructionOrigin (sources sourceIndex))) :
    ((origins.map (Sigma.mk sourceIndex)).filterMap (originsClaim? sources)).length =
      (origins.filterMap (InstructionOrigin.instruction? (sources sourceIndex))).countP
        (acceptedIssue (sources sourceIndex).law) := by
  induction origins with
  | nil => rfl
  | cons origin rest ih =>
    have flag := issued_origin_is_the_actual_accepted_issue sources sourceIndex origin
    cases decoded : origin.instruction? (sources sourceIndex) <;>
      cases issued : originsClaim? sources ⟨sourceIndex, origin⟩ <;>
      simp_all

theorem actual_visit_generates_its_own_slot_count (sourceIndex : Index) (ordinal : Nat)
    (state : (process sources).GeneratedState) :
    (consumeVisit sources sourceIndex ordinal state).current.slots.length = state.current.slots.length +
      ((sources sourceIndex).law.rawItems
        (ProgrammeSource.rawCurrent (sources sourceIndex) (ProgrammeHistory.visitAt (sources sourceIndex) ordinal).current)
        (ProgrammeSource.rawEvent (sources sourceIndex) (ProgrammeHistory.visitAt (sources sourceIndex) ordinal).current)).countP
          (acceptedIssue (sources sourceIndex).law) := by
  have exactSlots := congrArg List.length (origins_exact_claims sources (visitOrigins sources sourceIndex ordinal) state)
  simp only [List.length_map, List.length_append] at exactSlots
  rw [visitOrigins, native_issued_claim_count_is_actual_item_count,
    Financial.inventoryAt_instructions_exact] at exactSlots
  exact exactSlots

theorem first_two_visits_generate_their_own_slot_count (sourceIndex : Index)
    (state : (process sources).GeneratedState) :
    (continueVisits sources sourceIndex 0 2 state).current.slots.length = state.current.slots.length +
      ((sources sourceIndex).law.rawItems
        (ProgrammeSource.rawCurrent (sources sourceIndex) (ProgrammeHistory.visitAt (sources sourceIndex) 1).current)
        (ProgrammeSource.rawEvent (sources sourceIndex) (ProgrammeHistory.visitAt (sources sourceIndex) 1).current)).countP
          (acceptedIssue (sources sourceIndex).law) := by
  have initial := actual_visit_generates_its_own_slot_count sources sourceIndex 0 state
  change (consumeVisit sources sourceIndex 0 state).current.slots.length = state.current.slots.length + 0 at initial
  simp only [Nat.add_zero] at initial
  change (consumeVisit sources sourceIndex 1 (consumeVisit sources sourceIndex 0 state)).current.slots.length = _
  rw [actual_visit_generates_its_own_slot_count, initial]

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.InstrumentProjection
