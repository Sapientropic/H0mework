import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.Posting
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Costs.Visits

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.Posting

open ResponsibilityLifecycle Source.Program Family.BalanceConservation Financial.BalanceConservation

variable {Party Good Port Technology Instrument Index : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (sources : Index → ProgrammeSource.Input Party Good Port Technology Instrument)

theorem absent_amount (origin : Origin sources) (state : (process sources).GeneratedState)
    (absent : origin.2.instruction? (sources origin.1) = none) (side : Side) (party : Party) (good : Good) :
    runAmount sources ((consume sources origin state).transition sources) side party good = 0 := by
  unfold consume
  rw [issue_readout_absent (sources origin.1) origin.2 absent,
    movement_readout_absent (sources origin.1) origin.2 absent]
  rfl

theorem refused_amount (origin : Origin sources) (state : (process sources).GeneratedState)
    (instruction : ExecutionItem Party Good Port Technology Instrument)
    (original : origin.2.instruction? (sources origin.1) = some instruction)
    (refused : ¬(sources origin.1).law.Valid instruction.before instruction.request)
    (side : Side) (party : Party) (good : Good) :
    runAmount sources ((consume sources origin state).transition sources) side party good = 0 := by
  unfold consume
  rw [movement_readout_refused (sources origin.1) origin.2 instruction original refused]
  split
  next claim sameOrigin emitted =>
    have actual := claim.instruction_exact
    rw [sameOrigin] at actual
    have same := Option.some.inj (actual.symm.trans original)
    have accepted := claim.accepted
    rw [same] at accepted
    exact (refused accepted).elim
  all_goals rfl

theorem consume_amount (origin : Origin sources) (state : (process sources).GeneratedState)
    (instruction : ExecutionItem Party Good Port Technology Instrument)
    (original : origin.2.instruction? (sources origin.1) = some instruction)
    (compatible : Compatible sources origin.1 state.current)
    (matched : ledgerClaims sources state.current = instruction.before.claims)
    (side : Side) (party : Party) (good : Good) :
    runAmount sources ((consume sources origin state).transition sources) side party good =
      rawAmount sources origin.1 instruction side party good := by
  by_cases accepted : (sources origin.1).law.Valid instruction.before instruction.request
  · cases operation : instruction.request.operation
    case issue instrument debtor holder quantity =>
      obtain ⟨claim, sameOrigin, emitted, sameInstruction⟩ := issue_readout_issued (sources origin.1) origin.2
        instruction original instrument debtor holder quantity operation accepted
      unfold consume
      rw [emitted]
      simp only [rawAmount, operation]
      change (0 : ℚ) + 0 = 0
      exact zero_add 0
    case settle instrument debtor holder quantity =>
      have noIssue := issue_readout_nonissue (sources origin.1) origin.2 instruction original (by
        intro i d h q; simp [operation])
      obtain ⟨movement, emitted⟩ := payment_readout_exists (sources origin.1) origin.2 instruction original
        instrument debtor holder quantity operation accepted
      unfold consume
      rw [noIssue, emitted]
      change runAmount sources (allocate sources origin state movement.quantity (movement.quantity_nonnegative _)).transition side party good = _
      have same := Option.some.inj (movement.original.symm.trans original)
      have sourceMatched : ledgerClaims sources state.current = movement.instruction.before.claims := by
        rw [same]; exact matched
      simpa only [same] using matched_allocation sources movement emitted state compatible sourceMatched side party good
    case assign instrument debtor sender recipient quantity =>
      have noIssue := issue_readout_nonissue (sources origin.1) origin.2 instruction original (by
        intro i d h q; simp [operation])
      obtain ⟨movement, emitted⟩ := assignment_readout_exists (sources origin.1) origin.2 instruction original
        instrument debtor sender recipient quantity operation accepted
      unfold consume
      rw [noIssue, emitted]
      change runAmount sources (allocate sources origin state movement.quantity (movement.quantity_nonnegative _)).transition side party good = _
      have same := Option.some.inj (movement.original.symm.trans original)
      have sourceMatched : ledgerClaims sources state.current = movement.instruction.before.claims := by
        rw [same]; exact matched
      simpa only [same] using matched_allocation sources movement emitted state compatible sourceMatched side party good
    all_goals
      have noIssue := issue_readout_nonissue (sources origin.1) origin.2 instruction original (by
        intro i d h q; simp [operation])
      have noMovement := movement_readout_nonmovement (sources origin.1) origin.2 instruction original
        (by intro i d h q; simp [operation]) (by intro i d s r q; simp [operation])
      unfold consume
      rw [noIssue, noMovement]
      cases operation : instruction.request.operation <;> simp_all only [rawAmount] <;> rfl
  · rw [refused_amount sources origin state instruction original accepted]
    cases operation : instruction.request.operation <;> cases side <;>
      simp [rawAmount, operation, RawLaw.actualDebit, RawLaw.actualCredit, accepted,
        flowAt, Source.Program.amount]

def rawTotal (index : Index) (items : List (ExecutionItem Party Good Port Technology Instrument))
    (side : Side) (party : Party) (good : Good) : ℚ :=
  (items.map (fun item => rawAmount sources index item side party good)).sum

theorem consumeOrigins_amount (sourceIndex : Index)
    (origins : List (InstructionOrigin (sources sourceIndex)))
    (state : (process sources).GeneratedState) (current : RawCurrent Party Good Technology Instrument)
    (index : Nat) (event : RawEvent Party Good Port Technology Instrument)
    (sequence : origins.filterMap (InstructionOrigin.instruction? (sources sourceIndex)) =
      ((sources sourceIndex).law.execute current index event).items)
    (compatible : Compatible sources sourceIndex state.current)
    (matched : ledgerClaims sources state.current = current.claims)
    (side : Side) (party : Party) (good : Good) :
    runAmount sources (consumeOrigins_run sources (origins.map (Sigma.mk sourceIndex)) state) side party good =
      rawTotal sources sourceIndex ((sources sourceIndex).law.execute current index event).items side party good := by
  induction origins generalizing state current index event with
  | nil =>
      have lengthZero : event.length = 0 := by
        rw [← (sources sourceIndex).law.inventory_length current index event, ← sequence]
        rfl
      cases event with
      | nil => rfl
      | cons request tail => simp at lengthZero
  | cons origin tail ih =>
      change runAmount sources (((consume sources ⟨sourceIndex, origin⟩ state).transition sources).concatRuns _
        (consumeOrigins_run sources (tail.map (Sigma.mk sourceIndex)) ((consume sources ⟨sourceIndex, origin⟩ state).next sources))) side party good = _
      rw [run_append]
      cases decoded : origin.instruction? (sources sourceIndex) with
      | none =>
          simp only [List.filterMap_cons, decoded] at sequence
          rw [absent_amount sources ⟨sourceIndex, origin⟩ state decoded,
            consume_without_instruction sources ⟨sourceIndex, origin⟩ state decoded, zero_add]
          exact ih state current index event sequence compatible matched
      | some instruction =>
          cases event with
          | nil => simp only [List.filterMap_cons, decoded, RawLaw.execute, List.cons_ne_nil] at sequence
          | cons request remaining =>
              have aligned : instruction :: tail.filterMap (InstructionOrigin.instruction? (sources sourceIndex)) =
                  ⟨index, current, request⟩ ::
                    ((sources sourceIndex).law.execute ((sources sourceIndex).law.step current request) (index + 1) remaining).items := by
                simpa only [List.filterMap_cons, decoded, RawLaw.execute] using sequence
              obtain ⟨same, after⟩ := List.cons.inj aligned
              have localMatch : ledgerClaims sources state.current = instruction.before.claims := by
                rw [same]; exact matched
              have nextMatch := consume_claims_source_step sources ⟨sourceIndex, origin⟩ state instruction decoded compatible localMatch
              rw [same] at nextMatch
              rw [consume_amount sources ⟨sourceIndex, origin⟩ state instruction decoded compatible localMatch]
              have later := ih ((consume sources ⟨sourceIndex, origin⟩ state).next sources)
                ((sources sourceIndex).law.step current request) (index + 1) remaining after
                (consume_compatible sources sourceIndex origin state compatible) nextMatch
              rw [later, same]
              rfl

def atVisit (entry : PublicFunction.Costs.Visits.Window sources)
    (side : Side) (party : Party) (good : Good) :=
  rawTotal sources entry.1 ((sources entry.1).law.rawItems
    (ProgrammeSource.rawCurrent (sources entry.1) entry.2.current)
    (ProgrammeSource.rawEvent (sources entry.1) entry.2.current)) side party good

theorem visit_amount (sourceIndex : Index) (ordinal : Nat) (state : (process sources).GeneratedState)
    (compatible : Compatible sources sourceIndex state.current)
    (matched : ledgerClaims sources state.current =
      (PublicFunction.Costs.Visits.rawAt sources sourceIndex ordinal).claims)
    (side : Side) (party : Party) (good : Good) :
    runAmount sources (visitRun sources sourceIndex ordinal state) side party good =
      atVisit sources (PublicFunction.Costs.Visits.window sources sourceIndex ordinal) side party good :=
  consumeOrigins_amount sources sourceIndex _ state _ 0 _
    (Financial.inventoryAt_instructions_exact _ _) compatible matched side party good

def total : List (PublicFunction.Costs.Visits.Window sources) → Side → Party → Good → ℚ
  | [], _, _, _ => 0
  | entry :: rest, side, party, good => atVisit sources entry side party good + total rest side party good

omit [DecidableEq Port] in
theorem total_append (left right : List (PublicFunction.Costs.Visits.Window sources))
    (side : Side) (party : Party) (good : Good) :
    total sources (left ++ right) side party good = total sources left side party good + total sources right side party good := by
  induction left with
  | nil => simp only [List.nil_append, total, zero_add]
  | cons entry rest ih => simp only [List.cons_append, total, ih, add_assoc]

omit [DecidableEq Port] in
private theorem interval_snoc (sourceIndex : Index) (start count : Nat) :
    PublicFunction.Costs.Visits.interval sources sourceIndex start (count + 1) =
      PublicFunction.Costs.Visits.interval sources sourceIndex start count ++
        [PublicFunction.Costs.Visits.window sources sourceIndex (start + count)] := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
      change PublicFunction.Costs.Visits.window sources sourceIndex start ::
        PublicFunction.Costs.Visits.interval sources sourceIndex (start + 1) (count + 1) = _
      rw [ih]
      change _ :: (_ ++ [PublicFunction.Costs.Visits.window sources sourceIndex (start + 1 + count)]) =
        _ :: (_ ++ [PublicFunction.Costs.Visits.window sources sourceIndex (start + (count + 1))])
      congr 4
      omega

theorem interval_amount (sourceIndex : Index) (start count : Nat) (state : (process sources).GeneratedState)
    (compatible : Compatible sources sourceIndex state.current)
    (matched : ledgerClaims sources state.current = (PublicFunction.Costs.Visits.rawAt sources sourceIndex start).claims)
    (side : Side) (party : Party) (good : Good) :
    runAmount sources (continueVisits_run sources sourceIndex start count state) side party good =
      total sources (PublicFunction.Costs.Visits.interval sources sourceIndex start count) side party good := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change runAmount sources ((continueVisits_run sources sourceIndex start count state).concatRuns _
        (visitRun sources sourceIndex (start + count) (continueVisits sources sourceIndex start count state))) side party good = _
      rw [run_append, ih, visit_amount sources sourceIndex (start + count)
        (continueVisits sources sourceIndex start count state)
        (continueVisits_compatible sources sourceIndex start count state compatible)
        (continueVisits_claims_source sources sourceIndex start count state compatible matched),
        interval_snoc, total_append]
      simp only [total, add_zero]

omit [DecidableEq Port] in
theorem atVisit_debit (entry : PublicFunction.Costs.Visits.Window sources) (party : Party) (good : Good) :
    atVisit sources entry .debit party good = PublicFunction.Costs.Visits.atVisit sources entry party (.debtPayment good) := by
  unfold atVisit rawTotal PublicFunction.Costs.Visits.atVisit PublicFunction.Costs.wordCost
  congr 1
  apply List.map_congr_left
  intro item member
  cases operation : item.request.operation <;>
    simp [rawAmount, PublicFunction.Costs.itemCost, PublicFunction.Costs.isDebtPayment, operation]

omit [DecidableEq Port] in
theorem total_debit (entries : List (PublicFunction.Costs.Visits.Window sources)) (party : Party) (good : Good) :
    total sources entries .debit party good = PublicFunction.Costs.Visits.total sources entries party (.debtPayment good) := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      change atVisit sources entry .debit party good + total sources rest .debit party good = _
      rw [atVisit_debit, ih]
      rfl

structure VisitReceipt where
  private mk ::
  sourceIndex : Index
  ordinal : Nat
  before : (process sources).GeneratedState
  compatible : Compatible sources sourceIndex before.current
  matched : ledgerClaims sources before.current = (PublicFunction.Costs.Visits.rawAt sources sourceIndex ordinal).claims

def receive (sourceIndex : Index) (ordinal : Nat) (state : (process sources).GeneratedState)
    (compatible : Compatible sources sourceIndex state.current)
    (matched : ledgerClaims sources state.current = (PublicFunction.Costs.Visits.rawAt sources sourceIndex ordinal).claims) :
    VisitReceipt sources := ⟨sourceIndex, ordinal, state, compatible, matched⟩

namespace VisitReceipt

def window (receipt : VisitReceipt sources) :=
  PublicFunction.Costs.Visits.window sources receipt.sourceIndex receipt.ordinal

def native (receipt : VisitReceipt sources) :=
  visitRun sources receipt.sourceIndex receipt.ordinal receipt.before

theorem exact_amount (receipt : VisitReceipt sources) (side : Side) (party : Party) (good : Good) :
    runAmount sources (receipt.native sources) side party good = atVisit sources (receipt.window sources) side party good :=
  visit_amount sources receipt.sourceIndex receipt.ordinal receipt.before receipt.compatible receipt.matched side party good

end VisitReceipt

def intervalReceipts (sourceIndex : Index) (start count : Nat) (state : (process sources).GeneratedState)
    (compatible : Compatible sources sourceIndex state.current)
    (matched : ledgerClaims sources state.current = (PublicFunction.Costs.Visits.rawAt sources sourceIndex start).claims) :
    List (VisitReceipt sources) :=
  match count with
  | 0 => []
  | count + 1 => intervalReceipts sourceIndex start count state compatible matched ++
      [⟨sourceIndex, start + count, continueVisits sources sourceIndex start count state,
        continueVisits_compatible sources sourceIndex start count state compatible,
        continueVisits_claims_source sources sourceIndex start count state compatible matched⟩]

theorem intervalReceipts_keys (sourceIndex : Index) (start count : Nat) (state : (process sources).GeneratedState)
    (compatible : Compatible sources sourceIndex state.current)
    (matched : ledgerClaims sources state.current = (PublicFunction.Costs.Visits.rawAt sources sourceIndex start).claims) :
    (intervalReceipts sources sourceIndex start count state compatible matched).map (VisitReceipt.window sources) =
      PublicFunction.Costs.Visits.interval sources sourceIndex start count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [intervalReceipts, List.map_append, List.map_cons, List.map_nil, ih, VisitReceipt.window]
      exact (interval_snoc sources sourceIndex start count).symm

theorem intervalReceipts_events (sourceIndex : Index) (start count : Nat) (state : (process sources).GeneratedState)
    (compatible : Compatible sources sourceIndex state.current)
    (matched : ledgerClaims sources state.current = (PublicFunction.Costs.Visits.rawAt sources sourceIndex start).claims) :
    ((intervalReceipts sources sourceIndex start count state compatible matched).map
      (fun receipt => (receipt.native sources).events)).flatten =
      (continueVisits_run sources sourceIndex start count state).events := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change ((intervalReceipts sources sourceIndex start count state compatible matched ++
        [(⟨sourceIndex, start + count, continueVisits sources sourceIndex start count state,
          continueVisits_compatible sources sourceIndex start count state compatible,
          continueVisits_claims_source sources sourceIndex start count state compatible matched⟩ : VisitReceipt sources)]).map
          (fun receipt => (receipt.native sources).events)).flatten =
        ((continueVisits_run sources sourceIndex start count state).concatRuns _
          (visitRun sources sourceIndex (start + count) (continueVisits sources sourceIndex start count state))).events
      simp only [List.map_append, List.flatten_append, List.map_cons, List.map_nil,
        List.flatten_cons, List.flatten_nil, List.append_nil, ih,
        NativeResponsibilityProcess.Run.events_concatRuns]
      rfl

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.Posting
