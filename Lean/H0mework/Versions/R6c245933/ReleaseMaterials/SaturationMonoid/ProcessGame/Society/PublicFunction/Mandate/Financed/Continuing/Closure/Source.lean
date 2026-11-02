import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Runtime
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Lifecycle.Observed.Cuts
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Outstanding.History.NativeCuts

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle
open Mandate.Source (Port)

abbrev Past (fuel : ℚ) := OutstandingSource.ExecutionPrefix (source fuel)

theorem actual_prefix_respond (fuel : ℚ) (inputs : List (List Action)) (depth : Nat)
    (observed : inputs.length ≤ depth) :
    (trailAt fuel inputs (depth + 2)).respond = trailAt fuel inputs (depth + 3) := by
  change (trailAt fuel inputs (depth + 2)).append _ =
    (trailAt fuel inputs (depth + 2)).append _
  congr 1
  unfold OutstandingSource.History.word OutstandingSource.History.report
  rw [if_neg (by omega), if_neg (by omega), List.getElem?_eq_none (by omega)]
  exact ((source fuel).decideAt _ _).report_word.symm

inductive Reply (fuel : ℚ) (past : Past fuel) where
  | private received (incoming : IncomingWord law past.frame.raw)
  | private service (nonempty : (source fuel).pendingSlots past.frame.payments ≠ [])
      (outcome : PlanningOutcome law past.frame.raw ((source fuel).pendingTask past.frame.payments nonempty)
        ((source fuel).seed.actionsAt past.frame.raw) (source fuel).seed.budget)
  | private completed (complete : (source fuel).pendingSlots past.frame.payments = [])
      (outcome : Completion past.frame.raw) (exact : outcome = completion past.frame.raw)

def reply (fuel : ℚ) (past : Past fuel) : Reply fuel past :=
  match (source fuel).decideAt past.frame.raw past.frame.payments with
  | .received incoming => .received incoming
  | .planning nonempty outcome => .service nonempty outcome
  | .complete complete => .completed complete (completion past.frame.raw) rfl

def Reply.word {fuel : ℚ} {past : Past fuel} : Reply fuel past → List Action
  | .received incoming => incoming.word
  | .service _ outcome => outcome.word
  | .completed _ outcome _ => outcome.report.word

def Reply.report {fuel : ℚ} {past : Past fuel} : Reply fuel past →
    ProgrammeSource.ProgrammeReport Bool Good Port (State Bool Unit) Unit
  | .received incoming => .original past.frame.raw incoming.word
  | .service nonempty outcome => .planning law past.frame.raw
      ((source fuel).pendingTask past.frame.payments nonempty)
      ((source fuel).seed.actionsAt past.frame.raw) (source fuel).seed.budget outcome
  | .completed _ outcome _ => outcome.report

theorem reply_report_is_source_decision (fuel : ℚ) (past : Past fuel) :
    (reply fuel past).report = ((source fuel).decideAt past.frame.raw past.frame.payments).report := by
  unfold reply
  cases (source fuel).decideAt past.frame.raw past.frame.payments with
  | received incoming => rfl
  | planning nonempty outcome => rfl
  | complete complete => exact completion_evidence_and_word_have_one_producer _

theorem reply_word_is_source_decision (fuel : ℚ) (past : Past fuel) :
    (reply fuel past).word = ((source fuel).decideAt past.frame.raw past.frame.payments).word := by
  unfold reply
  cases (source fuel).decideAt past.frame.raw past.frame.payments with
  | received incoming => rfl
  | planning nonempty outcome => rfl
  | complete complete =>
      exact congrArg
        (fun report : ProgrammeSource.ProgrammeReport Bool Good Port (State Bool Unit) Unit => report.word)
        (completion_evidence_and_word_have_one_producer _)

inductive ReplyKind where
  | received | paid | physical | capture | authority | finance | review
  deriving DecidableEq, Repr

def Reply.kind {fuel : ℚ} {past : Past fuel} (response : Reply fuel past) : ReplyKind := by
  rcases response with ⟨incoming⟩ | ⟨nonempty, outcome⟩ | ⟨complete, outcome, exact⟩
  · exact .received
  · cases outcome with
    | paid plan => exact .paid
    | physical obstruction => exact .physical
    | capture obstruction => exact .capture
  · rcases outcome with ⟨active, outcome, exact⟩ | ⟨inactive, nonempty, outcomes, exact⟩ |
      ⟨inactive, quiet, outcome, exact⟩
    · exact .authority
    · exact .finance
    · exact .review

def Reply.ServiceBlocked {fuel : ℚ} {past : Past fuel} : Reply fuel past → Prop
  | .service _ (.physical _) | .service _ (.capture _) => True
  | _ => False

theorem Reply.service_blockage_keeps_the_original_unpaid_slot
    {fuel : ℚ} {past : Past fuel} (response : Reply fuel past) (blocked : response.ServiceBlocked)
    (index : (source fuel).Slot) (unpaid : past.frame.payments index = none) :
    response.word = [] ∧ (past.append response.word).frame.payments index = none := by
  rcases response with ⟨incoming⟩ | ⟨nonempty, outcome⟩ | ⟨complete, outcome, exact⟩
  · cases blocked
  · cases outcome with
    | paid plan => cases blocked
    | physical obstruction | capture obstruction =>
        exact ⟨rfl, (past.unpaid_append_iff [] index unpaid).mpr ((source fuel).no_payment_from_empty_word _ index)⟩
  · cases blocked

structure Cut (fuel : ℚ) (inputs : List (List Action)) where
  private mk ::
  depth : Nat
  observed : inputs.length ≤ depth
  past : Past fuel
  actual : past = trailAt fuel inputs (depth + 2)

variable {fuel : ℚ} {inputs : List (List Action)}

def Cut.at (depth : Nat) (observed : inputs.length ≤ depth) : Cut fuel inputs :=
  ⟨depth, observed, trailAt fuel inputs (depth + 2), rfl⟩

def start (fuel : ℚ) (inputs : List (List Action)) : Cut fuel inputs :=
  ⟨inputs.length, Nat.le_refl _, OutstandingSource.History.replay (source fuel) inputs, by
    have same := OutstandingSource.History.finite_prefix_exact (source fuel) inputs inputs.length (Nat.le_refl _)
    rw [List.take_length] at same
    exact same.symm⟩

def Cut.advance (cut : Cut fuel inputs) : Cut fuel inputs :=
  ⟨cut.depth + 1, Nat.le_trans cut.observed (Nat.le_succ _), cut.past.respond, by
    rw [cut.actual, actual_prefix_respond fuel inputs cut.depth cut.observed]⟩

theorem Cut.actual_current (cut : Cut fuel inputs) :
    cut.past.frame.raw = currentAt fuel inputs (cut.depth + 2) := by
  rw [cut.actual]
  exact (OutstandingSource.History.actual_frame (source fuel) inputs _).1.symm

theorem Cut.next_is_interpreted_reply (cut : Cut fuel inputs) :
    cut.advance.past = cut.past.append (reply fuel cut.past).word ∧
    cut.advance.past.frame.raw = law.next cut.past.frame.raw (reply fuel cut.past).word := by
  rw [reply_word_is_source_decision]
  exact ⟨rfl, rfl⟩

noncomputable section

structure Step (cut : Cut fuel inputs) where
  private mk ::
  response : Reply fuel cut.past
  generated : response = reply fuel cut.past
  native : Runtime.Disposition fuel inputs cut.depth
  native_exact : native = Runtime.generate fuel inputs cut.depth
  service_runs : (index : (source fuel).Slot) →
    (OutstandingSource.History.NativeService.process (source fuel) inputs).Run
      (OutstandingSource.History.NativeService.historyAt (source fuel) inputs index (cut.depth + 1)).state
      (native.services index).state
  mandate_runs : (birth : Fin (cut.depth + 1)) →
    (grant : Grant base scope (Runtime.mandateCurrentAt fuel inputs birth.val)
      (Runtime.mandateWordAt fuel inputs birth.val)) →
    (Lifecycle.Observed.process (base := base) (scope := scope)
      (currentAt := Runtime.mandateCurrentAt fuel inputs) (wordAt := Runtime.mandateWordAt fuel inputs)
      (birth := birth.val) (grant := grant)).Run
      (Runtime.traceGrant fuel inputs birth.val cut.depth grant).continuation.state
      (Runtime.traceGrant fuel inputs birth.val (cut.depth + 1) grant).continuation.state
  actual_word : (actualExecution fuel inputs (cut.depth + 1)).submitted = response.word
  actual_report : (OutstandingSource.History.writtenReceipt (source fuel) inputs (cut.depth + 1)).val = response.report
  actual_after : cut.advance.past.frame.raw = (actualExecution fuel inputs (cut.depth + 1)).after
  original_row : ProgrammeLedger.transferReceiptOf (input fuel inputs)
    (OutstandingSource.History.taskWrite (source fuel) inputs (cut.depth + 1)).2 =
      some (OutstandingSource.History.writtenReceipt (source fuel) inputs (cut.depth + 1))

def step (cut : Cut fuel inputs) : Step cut := by
  refine ⟨reply fuel cut.past, rfl, Runtime.generate fuel inputs cut.depth, rfl,
    fun index => OutstandingSource.History.NativeService.fromActualCut (source fuel) inputs index (cut.depth + 1) 1,
    fun _birth _grant => Lifecycle.Observed.fromActualCut cut.depth 1, ?_, ?_, ?_,
    OutstandingSource.History.receipt_is_in_own_original_write _ _ (cut.depth + 1)⟩
  · rw [OutstandingSource.History.residual_is_actually_emitted _ _ cut.depth cut.observed,
      reply_word_is_source_decision, cut.actual_current, cut.actual]
  · rw [residual_report_is_the_actual_original_row fuel inputs cut.depth cut.observed,
      reply_report_is_source_decision, cut.actual_current, cut.actual]
  · rw [OutstandingSource.History.actual_next, cut.advance.actual_current]
    rfl

inductive FiniteContinuation : Nat → Cut fuel inputs → Type
  | private observed (cut) : FiniteContinuation 0 cut
  | private next {rounds cut} (head : Step cut) (generated : head = step cut)
      (tail : FiniteContinuation rounds cut.advance) : FiniteContinuation (rounds + 1) cut

def generate (cut : Cut fuel inputs) : (rounds : Nat) → FiniteContinuation rounds cut
  | 0 => .observed cut
  | rounds + 1 => .next (step cut) rfl (generate cut.advance rounds)

def FiniteContinuation.endpoint {rounds : Nat} {cut : Cut fuel inputs} :
    FiniteContinuation rounds cut → Cut fuel inputs
  | .observed cut => cut
  | .next _ _ tail => tail.endpoint

theorem FiniteContinuation.endpoint_depth {rounds : Nat} {cut : Cut fuel inputs}
    (continuation : FiniteContinuation rounds cut) : continuation.endpoint.depth = cut.depth + rounds := by
  induction continuation
  · rfl
  next rounds cut head generated tail ih =>
    rw [FiniteContinuation.endpoint, ih]
    change _ + 1 + _ = _ + (_ + 1)
    omega

theorem FiniteContinuation.endpoint_is_actual {rounds : Nat} {cut : Cut fuel inputs}
    (continuation : FiniteContinuation rounds cut) :
    continuation.endpoint.past = trailAt fuel inputs (cut.depth + rounds + 2) := by
  rw [continuation.endpoint.actual, continuation.endpoint_depth]

def FiniteContinuation.serviceRun {rounds : Nat} {cut : Cut fuel inputs}
    (continuation : FiniteContinuation rounds cut) (index : (source fuel).Slot) :
    (OutstandingSource.History.NativeService.process (source fuel) inputs).Run
      (OutstandingSource.History.NativeService.historyAt (source fuel) inputs index (cut.depth + 1)).state
      (OutstandingSource.History.NativeService.historyAt (source fuel) inputs index
        (continuation.endpoint.depth + 1)).state := by
  induction continuation
  · exact .nil
  next rounds cut head generated tail ih =>
    have first := head.service_runs index
    rw [head.native_exact] at first
    exact first.concatRuns _ ih

def FiniteContinuation.mandateRun {rounds : Nat} {cut : Cut fuel inputs}
    (continuation : FiniteContinuation rounds cut) (birth : Fin (cut.depth + 1))
    (grant : Grant base scope (Runtime.mandateCurrentAt fuel inputs birth.val)
      (Runtime.mandateWordAt fuel inputs birth.val)) :
    (Lifecycle.Observed.process (base := base) (scope := scope)
      (currentAt := Runtime.mandateCurrentAt fuel inputs) (wordAt := Runtime.mandateWordAt fuel inputs)
      (birth := birth.val) (grant := grant)).Run
      (Runtime.traceGrant fuel inputs birth.val cut.depth grant).continuation.state
      (Runtime.traceGrant fuel inputs birth.val continuation.endpoint.depth grant).continuation.state := by
  induction continuation
  · exact .nil
  next rounds cut head generated tail ih =>
    exact (head.mandate_runs birth grant).concatRuns _
      (ih ⟨birth.val, Nat.lt_trans birth.isLt (Nat.lt_succ_self _)⟩ grant)

def FiniteContinuation.financeRun {rounds : Nat} {cut : Cut fuel inputs}
    (continuation : FiniteContinuation rounds cut) :
    (Financial.process (input fuel inputs)).Run (Runtime.account fuel inputs (cut.depth + 2)).current
      (Runtime.account fuel inputs (continuation.endpoint.depth + 2)).current := by
  induction continuation
  · exact .nil
  next rounds cut head generated tail ih =>
    have first := head.native.actual_crossing
    rw [head.native.account_exact] at first
    exact first.concatRuns _ ih

def FiniteContinuation.runFromBirth {rounds : Nat} {cut : Cut fuel inputs}
    (continuation : FiniteContinuation rounds cut) (birth : Fin (continuation.endpoint.depth + 1))
    (grant : Grant base scope (Runtime.mandateCurrentAt fuel inputs birth.val)
      (Runtime.mandateWordAt fuel inputs birth.val)) :
    (Lifecycle.Observed.process (base := base) (scope := scope)
      (currentAt := Runtime.mandateCurrentAt fuel inputs) (wordAt := Runtime.mandateWordAt fuel inputs)
      (birth := birth.val) (grant := grant)).Run
      (Runtime.traceGrant fuel inputs birth.val birth.val grant).continuation.state
      (Runtime.traceGrant fuel inputs birth.val continuation.endpoint.depth grant).continuation.state := by
  have path := Lifecycle.Observed.fromActualCut (base := base) (scope := scope)
    (currentAt := Runtime.mandateCurrentAt fuel inputs) (wordAt := Runtime.mandateWordAt fuel inputs)
    (birth := birth.val) (grant := grant) birth.val (continuation.endpoint.depth - birth.val)
  rw [Nat.add_sub_of_le (Nat.le_of_lt_succ birth.isLt)] at path
  exact path

theorem FiniteContinuation.every_intermediate_grant_is_retained {rounds : Nat} {cut : Cut fuel inputs}
    (continuation : FiniteContinuation rounds cut) (birth : Fin (continuation.endpoint.depth + 1))
    (grant : Grant base scope (Runtime.mandateCurrentAt fuel inputs birth.val)
      (Runtime.mandateWordAt fuel inputs birth.val))
    (actual : grant ∈ grantsAt base scope (Runtime.mandateCurrentAt fuel inputs birth.val)
      (Runtime.mandateWordAt fuel inputs birth.val)) :
    (⟨birth, Runtime.traceGrant fuel inputs birth.val continuation.endpoint.depth grant⟩ :
      Sigma fun birth : Fin (continuation.endpoint.depth + 1) =>
        Runtime.TracedGrant fuel inputs birth.val continuation.endpoint.depth) ∈
      Runtime.recordsAt fuel inputs continuation.endpoint.depth :=
  Runtime.every_original_grant_is_retained fuel inputs _ birth grant actual

theorem FiniteContinuation.original_service_archive_survives {rounds : Nat} {cut : Cut fuel inputs}
    (continuation : FiniteContinuation rounds cut) (index : (source fuel).Slot) (paid : Nat)
    (recorded : cut.past.frame.payments index = some paid) :
    continuation.endpoint.past.frame.payments index = some paid := by
  induction continuation
  · exact recorded
  next rounds cut head generated tail ih =>
    exact ih (cut.past.append_keeps_archive _ index paid recorded)


def FiniteContinuation.kinds {rounds : Nat} {cut : Cut fuel inputs} :
    FiniteContinuation rounds cut → List ReplyKind
  | .observed _ => []
  | .next head _ tail => head.response.kind :: tail.kinds

def responseKinds (fuel : ℚ) (past : Past fuel) : Nat → List ReplyKind
  | 0 => []
  | rounds + 1 => (reply fuel past).kind :: responseKinds fuel past.respond rounds

theorem FiniteContinuation.kinds_are_source_generated {rounds : Nat} {cut : Cut fuel inputs}
    (continuation : FiniteContinuation rounds cut) :
    continuation.kinds = responseKinds fuel cut.past rounds := by
  induction continuation
  · rfl
  next rounds cut head generated tail ih =>
    change head.response.kind :: tail.kinds = _
    rw [ih, head.generated]
    rfl

theorem FiniteContinuation.original_terminal_archive_survives {rounds : Nat} {cut : Cut fuel inputs}
    (continuation : FiniteContinuation rounds cut) (index : (source fuel).Slot)
    (terminal : (OutstandingSource.History.NativeService.historyAt (source fuel) inputs index
      (cut.depth + 1)).state.TerminalAt 0) :
    (OutstandingSource.History.NativeService.historyAt (source fuel) inputs index
      (continuation.endpoint.depth + 1)).state =
    (OutstandingSource.History.NativeService.historyAt (source fuel) inputs index (cut.depth + 1)).state := by
  rw [continuation.endpoint_depth, show cut.depth + rounds + 1 = cut.depth + 1 + rounds by omega]
  exact OutstandingSource.History.NativeService.terminal_state_is_preserved _ _ index _ rounds terminal

theorem FiniteContinuation.original_financial_claims_survive {rounds : Nat} {cut : Cut fuel inputs}
    (continuation : FiniteContinuation rounds cut) :
    (Runtime.account fuel inputs (cut.depth + 2)).current.slots.map (Financial.slotClaim (input fuel inputs)) <+:
      (Runtime.account fuel inputs (continuation.endpoint.depth + 2)).current.slots.map
        (Financial.slotClaim (input fuel inputs)) := by
  rw [continuation.endpoint_depth, show cut.depth + rounds + 2 = cut.depth + 2 + rounds by omega]
  exact Financial.BalanceConservation.cut_preserves_all_original_claims _ _ rounds

theorem every_legal_reachable_current_has_native_finite_continuation
    (fuel : ℚ) (current : Current)
    (reached : OutstandingSource.History.LegalReach (source fuel) current) (rounds : Nat) :
    ∃ inputs : List (List Action), (start fuel inputs).past.frame.raw = current ∧
      Nonempty (FiniteContinuation rounds (start fuel inputs)) := by
  obtain ⟨inputs, same⟩ := OutstandingSource.History.every_legal_reachable_state_has_its_own_actual_source
    (source fuel) current reached
  exact ⟨inputs, (start fuel inputs).actual_current.trans same, ⟨generate (start fuel inputs) rounds⟩⟩

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure
