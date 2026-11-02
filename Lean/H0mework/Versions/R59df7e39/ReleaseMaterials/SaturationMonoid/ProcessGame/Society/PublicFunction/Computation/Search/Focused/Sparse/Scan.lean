import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Sparse.Work
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Sparse
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code))
  (original : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code)
  (reference : Program model.source.code (horizon domain))
  (worker : Fin model.source.code.sites)
  (quote : Charge.Quote (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (quotas : List Nat)

/-- Slots include environment turns. Their costs cannot change after a verdict. -/
abbrev reserved := List.replicate quotas.length (Charge.feeRule quote model worker original)
abbrev Cache := Work model domain original (reserved model original worker quote quotas) reference

variable (point : View (code := model.source.code)) (rival : Opponent model.source.code)

def paidAdvance (quota : Nat) (cache : Option (Cache model domain original reference worker quote quotas)) :
    Option (Cache model domain original reference worker quote quotas) :=
  match seen : (Charge.read quote model worker point rival (Charge.endAt quote model worker point rival)).1 with
  | some (.accepted checked) =>
      let _receipt : Charge.paid quote model worker point rival (Charge.endAt quote model worker point rival) := ⟨checked,seen⟩
      some (advance model domain original (reserved model original worker quote quotas) reference quota
        (match cache with
        | some work => work
        | none => initial model domain original (reserved model original worker quote quotas) reference))
  | _ => cache

theorem an_unpaid_or_inactive_slot_cannot_advance_the_queue
    (quota : Nat) (cache : Option (Cache model domain original reference worker quote quotas))
    (unpaid : ¬ Charge.paid quote model worker point rival (Charge.endAt quote model worker point rival)) :
    paidAdvance model domain original reference worker quote quotas point rival quota cache = cache := by
  unfold paidAdvance
  split
  · rename_i checked seen
    exact False.elim (unpaid ⟨checked,seen⟩)
  · rfl

theorem a_paid_slot_processes_exactly_its_quoted_batch
    (quota : Nat) (cache : Option (Cache model domain original reference worker quote quotas))
    (paid : Charge.paid quote model worker point rival (Charge.endAt quote model worker point rival)) :
    paidAdvance model domain original reference worker quote quotas point rival quota cache =
      some (advance model domain original (reserved model original worker quote quotas) reference quota
        (match cache with
        | some work => work
        | none => initial model domain original (reserved model original worker quote quotas) reference)) := by
  obtain ⟨checked,arrived⟩ := paid
  unfold paidAdvance
  split
  · rfl
  · simp_all

theorem every_supported_nonempty_attempt_consumes_exactly_one_reserved_slot
    (nonempty : (Cut.seed point.point).remaining ≠ 0)
    (supported : Charge.fee quote ∈ words model.source.code.actions model.source.code.actionLimit) :
    (Charge.trace quote worker point rival).rules = [Charge.feeRule quote model worker original] := by
  cases observed : Replay.inspect worker ((Charge.tariff quote).word () 1) point rival with
  | unsupported outside =>
      exact False.elim (outside (by simpa only [Charge.tariff,Tariff.word,List.append_nil] using supported))
  | withheld listed different | refused listed emitted illegal =>
      simp only [Charge.trace,dif_neg nonempty,observed,Cut.Trace.rules,Replay.Attempt.rule,
        Option.toList_some]
      simp only [Charge.feeRule,dif_pos supported,Charge.tariff,Tariff.word,List.append_nil]
  | paid listed emitted legal =>
      by_cases ready : Cut.Ready worker (Replay.Attempt.paid listed emitted legal)
      · simp only [Charge.trace,dif_neg nonempty,observed,dif_pos ready,Cut.Trace.rules,
          Replay.Attempt.rule,Option.toList_some,Cut.Trace.rules,List.append_nil]
        simp only [Charge.feeRule,dif_pos supported,Charge.tariff,Tariff.word,List.append_nil]
      · simp only [Charge.trace,dif_neg nonempty,observed,dif_neg ready,Cut.Trace.rules,
          Replay.Attempt.rule,Option.toList_some]
        simp only [Charge.feeRule,dif_pos supported,Charge.tariff,Tariff.word,List.append_nil]

inductive Halt where
  | exhausted (empty : (Cut.seed point.point).remaining = 0)
  | unsupported (outside : Charge.fee quote ∉ words model.source.code.actions model.source.code.actionLimit)

abbrev PaidSlot := @Segmented.PaidSlot

def replayPayments (cache : Option (Cache model domain original reference worker quote quotas))
    (payments : List (PaidSlot model worker quote rival)) : Option (Cache model domain original reference worker quote quotas) :=
  payments.foldl (fun prior payment => some
    (advance model domain original (reserved model original worker quote quotas) reference payment.quota
      (match prior with
      | some work => work
      | none => initial model domain original (reserved model original worker quote quotas) reference))) cache

/-- The constructor index binds each payment to its own actual current. -/
inductive Scan : View (code := model.source.code) →
    Option (Cache model domain original reference worker quote quotas) → List Nat → Type where
  | empty (point cache) : Scan point cache []
  | stopped (point cache quota rest) (reason : Halt model quote point) : Scan point cache (quota::rest)
  | next (point cache quota rest)
      (consumed : (Charge.trace quote worker point rival).rules = [Charge.feeRule quote model worker original])
      (later : Scan (Charge.trace quote worker point rival).final
        (paidAdvance model domain original reference worker quote quotas point rival quota cache) rest) :
      Scan point cache (quota::rest)

private def scan (jobs : List Nat) (point : View (code := model.source.code))
    (cache : Option (Cache model domain original reference worker quote quotas)) :
    Scan model domain original reference worker quote quotas rival point cache jobs :=
  match jobs with
  | [] => .empty point cache
  | quota::rest =>
      if empty : (Cut.seed point.point).remaining = 0 then .stopped point cache quota rest (.exhausted empty)
      else if supported : Charge.fee quote ∈ words model.source.code.actions model.source.code.actionLimit then
        .next point cache quota rest
          (every_supported_nonempty_attempt_consumes_exactly_one_reserved_slot model original worker quote point rival empty supported)
          (scan rest (Charge.trace quote worker point rival).final
            (paidAdvance model domain original reference worker quote quotas point rival quota cache))
      else .stopped point cache quota rest (.unsupported supported)

def partialTrace (count : Nat) := scan model domain original reference worker quote quotas rival (quotas.take count) point none

namespace Scan
variable {model domain original reference worker quote quotas rival point}
  {cache : Option (Cache model domain original reference worker quote quotas)} {jobs : List Nat}

def final : {point : View (code := model.source.code)} →
    {cache : Option (Cache model domain original reference worker quote quotas)} → {jobs : List Nat} →
    Scan model domain original reference worker quote quotas rival point cache jobs → View (code := model.source.code)
  | _,_,_,.empty point _ | _,_,_,.stopped point .. => point
  | _,_,_,.next _ _ _ _ _ later => later.final

def cached : {point : View (code := model.source.code)} →
    {cache : Option (Cache model domain original reference worker quote quotas)} → {jobs : List Nat} →
    Scan model domain original reference worker quote quotas rival point cache jobs → Option (Cache model domain original reference worker quote quotas)
  | _,_,_,.empty _ cache | _,_,_,.stopped _ cache .. => cache
  | _,_,_,.next _ _ _ _ _ later => later.cached

def remaining : {point : View (code := model.source.code)} →
    {cache : Option (Cache model domain original reference worker quote quotas)} → {jobs : List Nat} →
    Scan model domain original reference worker quote quotas rival point cache jobs → List Nat
  | _,_,_,.empty .. => []
  | _,_,_,.stopped _ _ quota rest _ => quota::rest
  | _,_,_,.next _ _ _ _ _ later => later.remaining

def rules : {point : View (code := model.source.code)} →
    {cache : Option (Cache model domain original reference worker quote quotas)} → {jobs : List Nat} →
    Scan model domain original reference worker quote quotas rival point cache jobs → List (Distributed.Recall.Information.Agency.Protocol.Rule model.source.code)
  | _,_,_,.empty .. | _,_,_,.stopped .. => []
  | _,_,_,.next _ _ _ _ _ later => Charge.feeRule quote model worker original :: later.rules

def blocker : {point : View (code := model.source.code)} →
    {cache : Option (Cache model domain original reference worker quote quotas)} → {jobs : List Nat} →
    Scan model domain original reference worker quote quotas rival point cache jobs →
      Option (Sigma fun current : View (code := model.source.code) => Halt model quote current)
  | _,_,_,.empty .. => none
  | _,_,_,.stopped point _ _ _ reason => some ⟨point,reason⟩
  | _,_,_,.next _ _ _ _ _ later => later.blocker

/-- The final selection service must also have its own active paid slot. -/
def closingReceipt : {point : View (code := model.source.code)} →
    {cache : Option (Cache model domain original reference worker quote quotas)} → {jobs : List Nat} →
    Scan model domain original reference worker quote quotas rival point cache jobs → Option (PaidSlot model worker quote rival)
  | _,_,_,.empty .. | _,_,_,.stopped .. => none
  | _,_,_,.next before _ quota [] _ _ =>
      match seen : (Charge.read quote model worker before rival (Charge.endAt quote model worker before rival)).1 with
      | some (.accepted checked) => some ⟨before,quota,⟨checked,seen⟩⟩
      | _ => none
  | _,_,_,.next _ _ _ (_::_) _ later => later.closingReceipt

abbrev closingPaid (execution : Scan model domain original reference worker quote quotas rival point cache jobs) :=
  execution.closingReceipt.isSome

def payments : {point : View (code := model.source.code)} →
    {cache : Option (Cache model domain original reference worker quote quotas)} → {jobs : List Nat} →
    Scan model domain original reference worker quote quotas rival point cache jobs → List (PaidSlot model worker quote rival)
  | _,_,_,.empty .. | _,_,_,.stopped .. => []
  | _,_,_,.next before _ quota _ _ later =>
      match seen : (Charge.read quote model worker before rival (Charge.endAt quote model worker before rival)).1 with
      | some (.accepted checked) => ⟨before,quota,⟨checked,seen⟩⟩ :: later.payments
      | _ => later.payments

theorem the_entire_cache_replays_only_its_own_ordered_actual_paid_slots
    (execution : Scan model domain original reference worker quote quotas rival point cache jobs) :
    execution.cached = replayPayments model domain original reference worker quote quotas rival cache execution.payments := by
  induction execution with
  | empty | stopped => rfl
  | next before prior quota rest consumed later ih =>
      simp only [payments]
      split
      · rename_i checked seen
        have paid : Charge.paid quote model worker before rival (Charge.endAt quote model worker before rival) := ⟨checked,seen⟩
        exact ih.trans (congrArg (fun start => replayPayments model domain original reference worker quote quotas rival start later.payments)
          (a_paid_slot_processes_exactly_its_quoted_batch model domain original reference worker quote quotas before rival quota prior paid))
      · have unpaid : ¬ Charge.paid quote model worker before rival (Charge.endAt quote model worker before rival) := by
          rintro ⟨checked,arrived⟩
          simp_all
        exact ih.trans (congrArg (fun start => replayPayments model domain original reference worker quote quotas rival start later.payments)
          (an_unpaid_or_inactive_slot_cannot_advance_the_queue model domain original reference worker quote quotas before rival quota prior unpaid))

/-- Resumption starts at the stored actual current and consumes the stored cache. -/
def resume (execution : Scan model domain original reference worker quote quotas rival point cache jobs)
    (more : List Nat) :=
  scan model domain original reference worker quote quotas rival more execution.final execution.cached

def append : {point : View (code := model.source.code)} →
    {cache : Option (Cache model domain original reference worker quote quotas)} → {jobs : List Nat} →
    (execution : Scan model domain original reference worker quote quotas rival point cache jobs) →
    (completed : execution.remaining = []) → {more : List Nat} →
    (later : Scan model domain original reference worker quote quotas rival execution.final execution.cached more) →
    Scan model domain original reference worker quote quotas rival point cache (jobs++more)
  | _,_,_,.empty _ _,_,_,later => later
  | _,_,_,.stopped _ _ _ _ _,completed,_,_ => by cases completed
  | _,_,_,.next before prior quota rest consumed tail,completed,more,later =>
      .next before prior quota (rest++more) consumed (append tail completed later)

/-- Existing nodes are retained; only their terminal actual current runs new jobs. -/
def extend : {point : View (code := model.source.code)} →
    {cache : Option (Cache model domain original reference worker quote quotas)} → {jobs : List Nat} →
    (execution : Scan model domain original reference worker quote quotas rival point cache jobs) →
    (more : List Nat) → Scan model domain original reference worker quote quotas rival point cache (jobs++more)
  | _,_,_,.empty before prior,more => scan model domain original reference worker quote quotas rival more before prior
  | _,_,_,.stopped before prior quota rest reason,more => .stopped before prior quota (rest++more) reason
  | _,_,_,.next before prior quota rest consumed later,more =>
      .next before prior quota (rest++more) consumed (extend later more)

theorem resumption_reuses_the_stored_actual_source_and_cache
    (execution : Scan model domain original reference worker quote quotas rival point cache jobs)
    (completed : execution.remaining = []) {more : List Nat}
    (later : Scan model domain original reference worker quote quotas rival execution.final execution.cached more) :
    (execution.append completed later).final = later.final ∧
    (execution.append completed later).cached = later.cached ∧
    (execution.append completed later).rules = execution.rules ++ later.rules := by
  induction execution with
  | empty => exact ⟨rfl,rfl,rfl⟩
  | stopped => cases completed
  | next before prior quota rest consumed tail ih =>
      obtain ⟨actual,kept,joined⟩ := ih completed later
      exact ⟨actual,kept,congrArg (List.cons (Charge.feeRule quote model worker original)) joined⟩

theorem the_actual_source_contains_exactly_the_executed_fee_prefix
    (execution : Scan model domain original reference worker quote quotas rival point cache jobs) :
    execution.final.point = Splice.install point.point rival execution.rules ∧
    execution.rules = List.replicate (jobs.length-execution.remaining.length) (Charge.feeRule quote model worker original) ∧
    execution.remaining.length ≤ jobs.length := by
  induction execution with
  | empty | stopped => exact ⟨rfl,by simp [rules,remaining],by simp [remaining]⟩
  | next before _ quota rest consumed later ih =>
      refine ⟨?_,?_,?_⟩
      · change later.final.point = _
        rw [ih.1]
        have actual := (Charge.trace quote worker before rival).final_is_generated_only_by_its_actual_single_cut_rules
        rw [consumed] at actual
        change (Charge.trace quote worker before rival).final.point = before.point.after (Charge.feeRule quote model worker original) rival at actual
        rw [actual]
        rfl
      · simp only [rules,remaining,List.length_cons]
        rw [ih.2.1]
        have count : rest.length+1-later.remaining.length = (rest.length-later.remaining.length)+1 := by omega
        rw [count,List.replicate_succ]
      · simpa only [remaining,List.length_cons] using Nat.le_trans ih.2.2 (Nat.le_succ rest.length)
end Scan

/-- The installed producer resumes the retained first segment with exactly its
    original unconsumed suffix, under the same complete comparison prefix. -/
def traceAt (count : Nat) : Scan model domain original reference worker quote quotas rival point none quotas :=
  cast (congrArg (fun jobs => Scan model domain original reference worker quote quotas rival point none jobs)
    (List.take_append_drop count quotas))
    ((partialTrace model domain original reference worker quote quotas point rival count).extend (quotas.drop count))

def trace := traceAt model domain original reference worker quote quotas point rival 1

structure Finished where
  work : Cache model domain original reference worker quote quotas
  complete : work.todo = []
  room : (reserved model original worker quote quotas).length ≤ horizon domain
  choice : Option (Prefix.Choice model domain original (reserved model original worker quote quotas) reference)
  generated : choice = finish model domain original (reserved model original worker quote quotas) reference room work complete

def close (execution : Scan model domain original reference worker quote quotas rival point none quotas) :
    Option (Finished model domain original reference worker quote quotas) :=
  if ready : quotas.length ≤ horizon domain ∧ execution.remaining = [] ∧ execution.closingPaid = true then
    match execution.cached with
    | none => none
    | some work => if complete : work.todo = [] then
        some ⟨work,complete,by simpa only [reserved,List.length_replicate] using ready.1,finish model domain original (reserved model original worker quote quotas) reference (by simpa only [reserved,List.length_replicate] using ready.1) work complete,rfl⟩
      else none
  else none

def result : Option (Finished model domain original reference worker quote quotas) :=
  close model domain original reference worker quote quotas point rival
    (trace model domain original reference worker quote quotas point rival)

theorem a_released_finished_cache_is_its_actual_payment_replay_and_has_a_closing_receipt
    (finished : Finished model domain original reference worker quote quotas)
    (released : result model domain original reference worker quote quotas point rival = some finished) :
    replayPayments model domain original reference worker quote quotas rival none
      (trace model domain original reference worker quote quotas point rival).payments = some finished.work ∧
    ∃ closing, (trace model domain original reference worker quote quotas point rival).closingReceipt = some closing := by
  have replayed := (trace model domain original reference worker quote quotas point rival).the_entire_cache_replays_only_its_own_ordered_actual_paid_slots
  rw [←replayed]
  unfold result close at released
  split at released
  · rename_i ready
    split at released
    · cases released
    · rename_i work cached
      split at released
      · cases Option.some.inj released
        refine ⟨cached,?_⟩
        exact Option.isSome_iff_exists.mp ready.2.2
      · cases released
  · cases released

theorem a_released_result_has_executed_the_entire_fixed_fee_plan
    (finished : Finished model domain original reference worker quote quotas)
    (released : result model domain original reference worker quote quotas point rival = some finished) :
    let execution := trace model domain original reference worker quote quotas point rival
    execution.rules = reserved model original worker quote quotas ∧
    execution.final.point = Splice.install point.point rival (reserved model original worker quote quotas) ∧
    quotas.length ≤ horizon domain := by
  have complete : (trace model domain original reference worker quote quotas point rival).remaining = [] ∧
      quotas.length ≤ horizon domain := by
    unfold result close at released
    split at released
    · rename_i ready
      exact ⟨ready.2.1,ready.1⟩
    · cases released
  obtain ⟨actual,paid,_⟩ := (trace model domain original reference worker quote quotas point rival).the_actual_source_contains_exactly_the_executed_fee_prefix
  have same : (trace model domain original reference worker quote quotas point rival).rules = reserved model original worker quote quotas := by
    simpa only [complete.1,List.length_nil,Nat.sub_zero] using paid
  exact ⟨same,by simpa only [same] using actual,complete.2⟩

theorem a_selected_cache_has_the_complete_independently_reviewable_contract
    (finished : Finished model domain original reference worker quote quotas)
    (choice : Prefix.Choice model domain original (reserved model original worker quote quotas) reference)
    (_selected : finished.choice = some choice) :
    Prefix.Contract model domain original (reserved model original worker quote quotas) reference (.selected choice) :=
  Prefix.every_generated_outcome_has_the_complete_future_contract _ _ _ _ _ _


inductive CloseReason (execution : Scan model domain original reference worker quote quotas rival point none quotas) where
  | outsideWindow (outside : ¬ quotas.length ≤ horizon domain)
  | pending (left : execution.remaining ≠ [])
  | unpaidClosing (unpaid : execution.closingPaid ≠ true)
  | noCache (missing : execution.cached = none)
  | incomplete (work : Cache model domain original reference worker quote quotas)
      (present : execution.cached = some work) (left : work.todo ≠ [])

def closing_obstruction (execution : Scan model domain original reference worker quote quotas rival point none quotas)
    (absent : close model domain original reference worker quote quotas point rival execution = none) :
    CloseReason model domain original reference worker quote quotas point rival execution := by
  by_cases space : quotas.length ≤ horizon domain
  · by_cases complete : execution.remaining = []
    · by_cases paid : execution.closingPaid = true
      · unfold close at absent
        rw [dif_pos ⟨space,complete,paid⟩] at absent
        cases cached : execution.cached with
        | none => exact .noCache cached
        | some work =>
            rw [cached] at absent
            dsimp only at absent
            by_cases ready : work.todo = []
            · rw [dif_pos ready] at absent
              cases absent
            · exact .incomplete work cached ready
      · exact .unpaidClosing paid
    · exact .pending complete
  · exact .outsideWindow space

def the_failed_paid_cache_returns_the_stored_original_failure
    (finished : Finished model domain original reference worker quote quotas)
    (empty : finished.choice = none) (raw : Program model.source.code (horizon domain)) :
    Selection.Rejection model domain original reference
      (Prefix.extension (horizon domain) (reserved model original worker quote quotas) raw) :=
  rejection model domain original (reserved model original worker quote quotas) reference finished.room finished.work finished.complete
    (finished.generated.symm.trans empty) raw

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Sparse
