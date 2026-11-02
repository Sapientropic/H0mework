import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Feedback

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 200000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Local
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open Prefix

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (task : Task (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

namespace Branch
variable (state : Cache task)
abbrev domain (key : task.model.source.code.Key) :=
  Rolling.Receipt.localDomain task.model state.beliefs key.1 key.2
abbrev fallback := state.programme.at task.original state.past.length
abbrev outcome (key : task.model.source.code.Key) := Replanning.compile task.model (domain task state key) (fallback task state)
def head (key : task.model.source.code.Key) : Prefix.Rule task.model.source.code :=
  if (fiber state.beliefs key.1 key.2).isEmpty then fallback task state
  else match outcome task state key with
    | .selected choice => choice.policy.protocol
    | .blocked _ => fallback task state

private def lookup (saved : List (task.model.source.code.Key × Prefix.Rule task.model.source.code))
    (key : task.model.source.code.Key) : Prefix.Rule task.model.source.code :=
  ((saved.find? (fun entry => decide (entry.1 = key))).map Prod.snd).getD (fallback task state)

private theorem lookup_key (keys : List task.model.source.code.Key) (key : task.model.source.code.Key)
    (inside : key ∈ keys) :
    lookup task state (keys.map fun item => (item,head task state item)) key = head task state key := by
  induction keys with
  | nil => cases inside
  | cons first rest ih =>
      by_cases same : first = key
      · subst first;simp [lookup]
      · have later : key ∈ rest := (List.mem_cons.mp inside).resolve_left (Ne.symm same)
        simpa [lookup,same] using ih later

def rule : Prefix.Rule task.model.source.code :=
  let saved := task.model.source.code.keys.map fun key => (key,head task state key)
  {work := ⟨fun key inside => if key.1 = task.reader then (lookup task state saved key).work.val key inside
      else (fallback task state).work.val key inside,by
        apply task.model.source.code.every_local_policy_is_enumerated
        intro key inside
        split
        · exact (List.mem_pi _ _).mp (lookup task state saved key).work.property key inside
        · exact (List.mem_pi _ _).mp (fallback task state).work.property key inside⟩,
   events := fun key inside => if key.1 = task.reader then (lookup task state saved key).events key inside
      else (fallback task state).events key inside}

theorem the_owned_key_uses_the_same_source_generated_head (key : task.model.source.code.Key)
    (owned : key.1 = task.reader) :
    (rule task state).work.val key (task.model.source.code.key_mem key) =
      (head task state key).work.val key (task.model.source.code.key_mem key) ∧
    (rule task state).events key (task.model.source.code.key_mem key) =
      (head task state key).events key (task.model.source.code.key_mem key) := by
  simp only [rule,if_pos owned,lookup_key task state _ key (task.model.source.code.key_mem key)]
  exact ⟨trivial,trivial⟩

theorem other_workers_keep_their_original_work_and_events (key : task.model.source.code.Key)
    (other : key.1 ≠ task.reader) :
    (rule task state).work.val key (task.model.source.code.key_mem key) =
      (fallback task state).work.val key (task.model.source.code.key_mem key) ∧
    (rule task state).events key (task.model.source.code.key_mem key) =
      (fallback task state).events key (task.model.source.code.key_mem key) := by
  simp only [rule,if_neg other]
  exact ⟨trivial,trivial⟩

abbrev proposal := Prefix.extension (horizon task.domain) state.past
  (Splice.word (rule task state :: state.programme.controls.drop (state.past.length+1)))

inductive Decision where
  | admitted (accepted : Selection.acceptable task.model task.domain task.original state.programme (proposal task state))
  | refused (rejected : Selection.Rejection task.model task.domain task.original state.programme (proposal task state))

-- The original compact decision avoids materializing all rows on acceptance.
-- Refusal retains the original row and coordinate, without changing the relation.
def inspect : Decision task state :=
  if accepted : Selection.acceptable task.model task.domain task.original state.programme (proposal task state) then
    .admitted accepted
  else match Distributed.inspect (Selection.holds task.model task.domain task.original state.programme (proposal task state))
      (Replanning.rows task.model task.domain) with
    | .accepted all => False.elim (accepted all)
    | .rejected row original broken => .refused ⟨row,original,broken⟩

def commit (decision : Decision task state) : Cache task :=
  match decision with
  | .refused _ => {state with beliefs := fiber state.beliefs task.reader (observation (state.current task.point task.rival) task.reader)}
  | .admitted accepted =>
      {state with
        beliefs := fiber state.beliefs task.reader (observation (state.current task.point task.rival) task.reader)
        programme := proposal task state
        retained := Prefix.every_completion_preserves_the_committed_control_prefix _ _ _ state.within
        above := Selection.acceptable_trans task.model task.domain task.original _ _ _ accepted state.above}

variable (decision : Decision task state)
theorem commit_past : (commit task state decision).past = state.past := by cases decision <;> rfl

theorem commit_knowledge (covered : Knowledge.Contains state.beliefs (state.current task.point task.rival)) :
    Knowledge.Contains (commit task state decision).beliefs ((commit task state decision).current task.point task.rival) := by
  have posterior := Rolling.Receipt.the_actual_local_record_generates_its_own_covered_planning_domain _ _ covered task.reader
  cases decision <;> simpa only [commit,Paid.State.current] using posterior

variable {task state}
theorem accepted_rule_is_really_the_next_stage (accepted : Selection.acceptable task.model task.domain task.original
    state.programme (proposal task state)) (live : Driving.Progress.Live state) :
    Driving.Progress.rule (commit task state (.admitted accepted)) = rule task state := by
  unfold Driving.Progress.rule commit
  change (proposal task state).at task.original state.past.length = _
  change ((state.past ++ (rule task state :: state.programme.controls.drop (state.past.length+1))).take
    (horizon task.domain))[state.past.length]?.getD _ = _
  rw [List.getElem?_take_of_lt live.2,List.getElem?_append_right (Nat.le_refl _)]
  simp only [Nat.sub_self,List.getElem?_cons_zero,Option.getD_some]
end Branch

inductive Wait : Cache task → Type where
  | terminal {state : Cache task} (ended : ¬ Driving.Progress.Live state) : Wait state
  | ready {state : Cache task} (live : Driving.Progress.Live state) (owned : Owns task state)
      (decision : Branch.Decision task state) : Wait state
  | waiting {state : Cache task} (live : Driving.Progress.Live state) (foreign : ¬ Owns task state)
      (later : Wait (Owned.advance task state)) : Wait state
  | exhausted {state : Cache task} : Wait state

private def await : Nat → (state : Cache task) → Wait task state
  | 0,_ => .exhausted
  | fuel+1,cache =>
      if live : Driving.Progress.Live cache then
        if owned : Owns task cache then .ready live owned (Branch.inspect task cache)
        else .waiting live owned (await fuel (Owned.advance task cache))
      else .terminal live

namespace Wait
variable {task}
def final : {state : Cache task} → Wait task state → Cache task
  | cache,.terminal _ | cache,.exhausted => cache
  | cache,.ready _ _ decision => Owned.advance task (Branch.commit task cache decision)
  | _,.waiting _ _ later => later.final

def rules : {state : Cache task} → Wait task state → List (Prefix.Rule task.model.source.code)
  | _,.terminal _ | _,.exhausted => []
  | cache,.ready _ _ decision => Driving.Progress.rules (Branch.commit task cache decision)
  | cache,.waiting _ _ later => Driving.Progress.rules cache ++ later.rules

def admitted : {state : Cache task} → Wait task state → Option Bool
  | _,.ready _ _ (.admitted _) => some true
  | _,.ready _ _ (.refused _) => some false
  | _,.waiting _ _ later => later.admitted
  | _,_ => none

def learnedAt : {state : Cache task} → Wait task state → Option Nat
  | cache,.ready .. => some cache.past.length
  | _,.waiting _ _ later => later.learnedAt
  | _,_ => none

theorem past_is_literal {state : Cache task} (wait : Wait task state) :
    wait.final.past = state.past ++ wait.rules := by
  induction wait with
  | terminal | exhausted => exact (List.append_nil _).symm
  | ready live owned decision =>
      rw [final,Owned.advance_past,Branch.commit_past]
      rfl
  | waiting live foreign later ih => rw [final,ih,Owned.advance_past,List.append_assoc];rfl

theorem knowledge {state : Cache task} (wait : Wait task state)
    (covered : Knowledge.Contains state.beliefs (state.current task.point task.rival)) :
    Knowledge.Contains wait.final.beliefs (wait.final.current task.point task.rival) := by
  induction wait with
  | terminal | exhausted => exact covered
  | ready live owned decision => exact Owned.advance_knowledge task _ (Branch.commit_knowledge task _ decision covered)
  | waiting live foreign later ih => exact ih (Owned.advance_knowledge task _ covered)

private theorem resolves (fuel : Nat) (cache : Cache task) (room : horizon task.domain < cache.past.length+fuel) :
    (await task fuel cache).learnedAt.isSome ∨ ¬ Driving.Progress.Live (await task fuel cache).final := by
  induction fuel generalizing cache with
  | zero => have inside := cache.within;omega
  | succ fuel ih =>
      unfold await
      split
      · rename_i live
        split
        · exact Or.inl rfl
        · exact ih _ (by
            have moved := Driving.Progress.an_existing_live_slot_is_really_consumed cache live
            change (Owned.advance task cache).past.length = cache.past.length+1 at moved
            omega)
      · exact Or.inr (by assumption)

theorem the_source_window_never_exhausts_its_wait_fuel (cache : Cache task) :
    (await task (horizon task.domain+1) cache).learnedAt.isSome ∨
      ¬ Driving.Progress.Live (await task (horizon task.domain+1) cache).final :=
  resolves _ _ (by omega)
theorem an_admitted_local_rule_is_executed_at_the_actual_owned_stage
    {cache : Cache task} (live : Driving.Progress.Live cache) (owned : Owns task cache)
    (accepted : Selection.acceptable task.model task.domain task.original cache.programme (Branch.proposal task cache)) :
    (Wait.ready (task := task) (state := cache) live owned
      (Branch.Decision.admitted (task := task) (state := cache) accepted)).final.past = cache.past ++ [Branch.rule task cache] := by
  have kept : Driving.Progress.Live (Branch.commit task cache (.admitted accepted)) := live
  change (Owned.advance task (Branch.commit task cache (.admitted accepted))).past = _
  rw [Owned.advance_past,Branch.commit_past]
  rw [Driving.Progress.rules,if_pos kept,Branch.accepted_rule_is_really_the_next_stage accepted live]
end Wait

inductive Turn (state : Cache task) where
  | unchanged (original : Owned.Turn task state)
  | paid (supported : Paid.request task.quote ∈ words task.model.source.code.actions task.model.source.code.actionLimit)
      (booked : state.Booked (Paid.requestedRule task.reader task.quote supported))
      (receipt : Paid.funded state task.reader task.quote task.point task.rival)
      (wait : Wait task (state.carry (Paid.requestedRule task.reader task.quote supported) booked))

def turn (state : Cache task) : Turn task state :=
  if supported : Paid.request task.quote ∈ words task.model.source.code.actions task.model.source.code.actionLimit then
    if booked : state.Booked (Paid.requestedRule task.reader task.quote supported) then
      if receipt : Paid.funded state task.reader task.quote task.point task.rival then
        .paid supported booked receipt (await task (horizon task.domain+1)
          (state.carry (Paid.requestedRule task.reader task.quote supported) booked))
      else .unchanged (.unpaid supported booked receipt)
    else .unchanged (.unreserved supported booked)
  else .unchanged (.unsupported supported)

namespace Turn
variable {task} {state : Cache task}
def final : Turn task state → Cache task
  | .unchanged original => original.final
  | .paid _ _ _ wait => wait.final

def rules : Turn task state → List (Prefix.Rule task.model.source.code)
  | .unchanged original => original.rules
  | .paid supported _ _ wait => Paid.requestedRule task.reader task.quote supported :: wait.rules

def report : Turn task state → Report
  | .unchanged original => Owned.report task state original
  | .paid _ _ _ wait => ⟨state.past.length,wait.final.past.length,true,wait.learnedAt,wait.admitted⟩

theorem past_is_literal (event : Turn task state) : event.final.past = state.past ++ event.rules := by
  cases event with
  | unchanged original => exact original.past_is_the_literal_actual_word
  | paid supported booked receipt wait =>
      rw [final,Wait.past_is_literal]
      change (state.past ++ [_]) ++ _ = _
      rw [List.append_assoc];rfl

theorem knowledge (event : Turn task state)
    (covered : Knowledge.Contains state.beliefs (state.current task.point task.rival)) :
    Knowledge.Contains event.final.beliefs (event.final.current task.point task.rival) := by
  cases event with
  | unchanged original => exact original.knowledge_survives_every_actual_attempt_wait_and_owned_update covered
  | paid supported booked receipt wait =>
      apply wait.knowledge
      have after := Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Observed.Transcript.every_actual_past_keeps_a_representative_in_the_same_public_domain
        [Paid.requestedRule task.reader task.quote supported] state.beliefs (state.current task.point task.rival) covered task.rival
      change Knowledge.Contains _ (Evidence.after (state.current task.point task.rival) _ task.rival) at after
      rw [←Paid.State.carrying_a_reserved_request_is_the_actual_next_stage state _ booked task.point task.rival] at after
      exact after
end Turn

structure Record where
  before : Cache task
  event : Turn task before
  exact_generation : event = turn task before

def trace : Nat → Cache task → Cache task × List Report × List (Record task)
  | 0,cache => (cache,[],[])
  | rounds+1,cache =>
      let event := turn task cache
      let later := trace rounds event.final
      (later.1,event.report :: later.2.1,⟨cache,event,rfl⟩ :: later.2.2)

def executed : Nat → Cache task → List (Prefix.Rule task.model.source.code)
  | 0,_ => []
  | rounds+1,cache => (turn task cache).rules ++ executed rounds (turn task cache).final

theorem actual_word (rounds : Nat) (cache : Cache task) :
    (trace task rounds cache).1.past = cache.past ++ executed task rounds cache := by
  induction rounds generalizing cache with
  | zero => exact (List.append_nil _).symm
  | succ rounds ih =>
      change (trace task rounds (turn task cache).final).1.past = _
      rw [ih,Turn.past_is_literal,List.append_assoc]
      rfl

theorem every_record_is_a_prefix_of_the_actual_source (rounds : Nat) (cache : Cache task) :
    ∀ record ∈ (trace task rounds cache).2.2,
      ∃ suffix, (trace task rounds cache).1.past = record.event.final.past ++ suffix := by
  induction rounds generalizing cache with
  | zero => intro record inside;cases inside
  | succ rounds ih =>
      intro record inside
      change record ∈ (⟨cache,turn task cache,rfl⟩ :: (trace task rounds (turn task cache).final).2.2) at inside
      rcases List.mem_cons.mp inside with first | later
      · subst record
        exact ⟨executed task rounds (turn task cache).final,by
          change (trace task rounds (turn task cache).final).1.past = _
          exact actual_word task rounds (turn task cache).final⟩
      · exact ih _ record later

theorem every_finite_run_preserves_actual_knowledge (rounds : Nat) (state : Cache task)
    (covered : Knowledge.Contains state.beliefs (state.current task.point task.rival)) :
    Knowledge.Contains (trace task rounds state).1.beliefs ((trace task rounds state).1.current task.point task.rival) := by
  induction rounds generalizing state with
  | zero => exact covered
  | succ rounds ih => exact ih _ ((turn task state).knowledge covered)



variable (request : PublicTask.Request (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (quotas : List Nat)
  (point : Cursor request.model.source.code) (future : Opponent request.model.source.code) (rounds : Nat)

inductive Output where
  | inherited (result : PaidSearch.PublicResult request quotas point future)
  | installed (fits : request.reference.length ≤ horizon (PublicTask.domain request (observation (currentView point) request.reader)))
      (work : Focused.Sparse.Finished request.model (PublicTask.domain request (observation (currentView point) request.reader)) request.original
        (PaidSearch.reference request _ fits) request.reader request.quote quotas)
      (released : PaidSearch.finished request _ fits quotas point future = some work)
      (choice : Prefix.Choice request.model (PublicTask.domain request (observation (currentView point) request.reader)) request.original
        (PaidSearch.fees request quotas) (PaidSearch.reference request _ fits)) (selected : work.choice = some choice)
      (actual : Cache (PublicTask.Feedback.task request _ fits quotas point future choice) × List Report ×
        List (Record (PublicTask.Feedback.task request _ fits quotas point future choice)))
      (generated : actual = trace (PublicTask.Feedback.task request _ fits quotas point future choice) rounds
        (PublicTask.Feedback.seed request _ fits quotas point future work released choice))

def produce : Output request quotas point future rounds :=
  match PublicTask.Feedback.produce request quotas point future 0 with
  | .continued fits work released choice selected _ _ =>
      .installed fits work released choice selected
        (trace (PublicTask.Feedback.task request _ fits quotas point future choice) rounds
          (PublicTask.Feedback.seed request _ fits quotas point future work released choice)) rfl
  | previous => .inherited previous.search

namespace Output
variable {request quotas point future rounds}
def controls : Output request quotas point future rounds → List (Prefix.Rule request.model.source.code)
  | .inherited (.absent ..) | .inherited (.overBudget ..) => []
  | .inherited (.scanned fits _) => PaidSearch.scanRules request _ fits quotas point future
  | .installed _ _ _ _ _ actual _ => actual.1.past

def search : Output request quotas point future rounds → PaidSearch.PublicResult request quotas point future
  | .inherited result => result
  | .installed fits work released .. => .scanned fits (.completed work released)

def Sound : Output request quotas point future rounds → Prop
  | .inherited result => result.Sound
  | .installed fits _ _ _ _ actual _ =>
      Selection.acceptable request.model (PublicTask.domain request (observation (currentView point) request.reader)) request.original
        (PaidSearch.reference request _ fits) actual.1.programme ∧
      Knowledge.Contains actual.1.beliefs (actual.1.current (currentView point) future) ∧
      (∃ suffix, actual.1.past = PaidSearch.fees request quotas ++ suffix) ∧
      (∀ other ∈ Prefix.candidates request.model (PublicTask.domain request (observation (currentView point) request.reader))
        request.original (PaidSearch.fees request quotas) (PaidSearch.reference request _ fits),
        ¬ Distributed.Improves
          (Selection.axes (fuel := horizon (PublicTask.domain request (observation (currentView point) request.reader)))
            request.model (PublicTask.domain request (observation (currentView point) request.reader)))
          (Selection.benefit request.model (PublicTask.domain request (observation (currentView point) request.reader)) request.original)
          actual.1.programme other.protocol) ∧
      (∀ record ∈ actual.2.2, ∃ suffix, actual.1.past = record.event.final.past ++ suffix)
def paidControls : Output request quotas point future rounds → List (Prefix.Rule request.model.source.code)
  | .inherited (.absent ..) | .inherited (.overBudget ..) => []
  | .inherited (.scanned fits _) | .installed fits .. => PaidSearch.scanRules request _ fits quotas point future

theorem controls_extend_the_same_actual_paid_search (result : Output request quotas point future rounds) :
    ∃ suffix, result.controls = result.paidControls ++ suffix := by
  cases result with
  | inherited previous =>
      cases previous with
      | absent | overBudget => exact ⟨[],rfl⟩
      | scanned => exact ⟨[],(List.append_nil _).symm⟩
  | installed fits work released choice selected actual generated =>
      change ∃ suffix, actual.1.past = PaidSearch.scanRules request _ fits quotas point future ++ suffix
      rw [generated]
      rw [(PaidSearch.every_completed_search_keeps_the_entire_original_reference_and_fee_prefix work released).1]
      exact ⟨_,actual_word _ _ _⟩
end Output

private theorem nondomination_survives {Policy Axis : Type} (axes : List Axis) (benefit : Policy → Axis → ℚ)
    (old next other : Policy) (maximal : ¬ Distributed.Improves axes benefit old other)
    (above : Distributed.NoWorse axes benefit next old) : ¬ Distributed.Improves axes benefit next other := by
  intro strict
  exact maximal ⟨Distributed.noWorse_trans strict.1 above,
    fun reverse => strict.2 (Distributed.noWorse_trans above reverse)⟩

theorem all_public_histories_generate_actual_local_installation
    (origin : Distributed.Recall.Information.Origin request.model)
    (stages : List (PublicFunction.Protocol.SymbolicAuthentication.EventHistory.Stage (code := request.model.source.code)))
    (installed : stages.map Prod.fst = request.installed) :
    (produce request quotas
      (PublicFunction.Protocol.SymbolicAuthentication.EventHistory.execute
        (PublicFunction.Protocol.SymbolicAuthentication.EventHistory.ofOrigin request.model request.budget origin) stages)
      future rounds).Sound := by
  let current := PublicFunction.Protocol.SymbolicAuthentication.EventHistory.execute
    (PublicFunction.Protocol.SymbolicAuthentication.EventHistory.ofOrigin request.model request.budget origin) stages
  have covered := PublicTask.every_actual_receipt_has_a_complete_local_source request origin stages installed
  unfold produce
  cases old : PublicTask.Feedback.produce request quotas current future 0 with
  | absent | overBudget | unavailable | rejected =>
      have real := PaidSearch.all_origins_and_finite_adaptive_histories_generate_a_paid_search_or_precise_obstruction
        request origin stages installed future quotas
      rw [←PublicTask.Feedback.the_initial_search_projection_is_independent_of_later_feedback
        request quotas current future 0,old] at real
      exact real
  | continued fits work released choice selected actual generated =>
      let localTask := PublicTask.Feedback.task request _ fits quotas current future choice
      let initial := PublicTask.Feedback.seed request _ fits quotas current future work released choice
      let final := (trace localTask rounds initial).1
      refine ⟨Selection.acceptable_trans _ _ _ _ _ _ final.above choice.policy.accepted,?_,?_,?_,?_⟩
      · exact every_finite_run_preserves_actual_knowledge localTask rounds initial
          (PublicTask.Feedback.the_seed_keeps_actual_local_knowledge work released choice covered)
      · exact ⟨executed localTask rounds initial,actual_word localTask rounds initial⟩
      · intro other inside
        exact nondomination_survives
          (Selection.axes (fuel := horizon localTask.domain) localTask.model localTask.domain)
          (Selection.benefit localTask.model localTask.domain localTask.original)
          choice.policy.protocol final.programme other.protocol (choice.maximal other inside)
          (Selection.acceptance_bounds_every_benefit localTask.model localTask.domain localTask.original
            localTask.baseline final.programme final.above)
      · exact every_record_is_a_prefix_of_the_actual_source localTask rounds initial

structure Occurrence where
  generated : Output request quotas point future rounds
  exact_generation : generated = produce request quotas point future rounds

def occurrence : Occurrence request quotas point future rounds := ⟨produce request quotas point future rounds,rfl⟩

namespace Occurrence
variable {request quotas point future rounds}
abbrev controls (made : Occurrence request quotas point future rounds) := made.generated.controls
end Occurrence

abbrev full := Splice.install point future (produce request quotas point future rounds).controls

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Local
