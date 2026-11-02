import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Local.Inquiry

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 600000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Local.Inquiry.Planning
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open PublicFunction.Protocol.SymbolicAuthentication

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (task : Owned.Task (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

abbrev current (cache : Inquiry.Frame task) := cache.current task.point task.rival
abbrev reading (cache : Inquiry.Frame task) := observation (current task cache) task.reader
abbrev posterior (cache : Inquiry.Frame task) := fiber cache.views task.reader (reading task cache)
abbrev domain (cache : Inquiry.Frame task) := (posterior task cache).map View.point
abbrev reference (cache : Inquiry.Frame task) :=
  Continuation.Whole.Complete.clip (horizon (domain task cache)) cache.restore.tail
abbrev Outcome (cache : Inquiry.Frame task) :=
  Selection.Outcome task.model (domain task cache) task.original (reference task cache)
abbrev Choice (cache : Inquiry.Frame task) :=
  Selection.Choice task.model (domain task cache) task.original (reference task cache)

def compile (cache : Inquiry.Frame task) : Outcome task cache :=
  cache.shell.planner (domain task cache) task.original (reference task cache)

/-- A new task begins at the same actual cut with the retained original origin.
Its initial beliefs are the actual posterior, not a new arrival-origin enumeration. -/
def continuation (cache : Inquiry.Frame task) (choice : Choice task cache) : Owned.Task
    (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) :=
  {task with
    domain := domain task cache
    baseline := choice.policy.protocol
    point := current task cache
    planner := cache.shell.planner
    initialVerifier := .isTrue (Prefix.Commitment.admissible_plan_is_its_own_valid_reference
      task.model (domain task cache) task.original (reference task cache) choice.policy.protocol choice.policy.accepted)}

namespace Handoff
variable {task} (cache : Inquiry.Frame task) (choice : Choice task cache)

-- Only computational shell fields are assembled here; the posterior is retained
-- as a delayed value until the next compiler actually consumes it.
def seed : Inquiry.Frame (continuation task cache choice) :=
  ⟨{past := [],programme := choice.policy.protocol,beliefs := [],
    within := Nat.zero_le _,actualWithin := Nat.zero_le _,retained := rfl,
    above := Prefix.Commitment.admissible_plan_is_its_own_valid_reference
      task.model (domain task cache) task.original (reference task cache) choice.policy.protocol choice.policy.accepted,
    planner := cache.shell.planner},fun _ => posterior task cache⟩

abbrev next := Inquiry.Frame.advance (continuation task cache choice) (seed cache choice)
abbrev word := Driving.Progress.rules (seed cache choice).shell

theorem retained_origin : (continuation task cache choice).point.origin.val = (current task cache).origin.val := rfl

theorem posterior_is_not_reinitialized : (seed cache choice).views = posterior task cache := rfl

theorem selected_stage_is_actually_executed (live : Driving.Progress.Live (seed cache choice).shell) :
    (next cache choice).past = [choice.policy.protocol.at task.original 0] := by
  rw [Inquiry.Frame.advance_past]
  simp only [Driving.Progress.rules,if_pos live]
  rfl

theorem complete_selected_future_is_retained (ordinal : Nat) :
    (next cache choice).programme.at task.original ordinal = choice.policy.protocol.at task.original ordinal := by
  change (Driving.Progress.next {(seed cache choice).shell with beliefs := []}).programme.at task.original ordinal = _
  unfold Driving.Progress.next
  split
  · exact Prefix.Padding.every_stage_is_the_original_stage task.original choice.policy.protocol ordinal
  · rfl

theorem actual_current :
    (next cache choice).current (continuation task cache choice).point (continuation task cache choice).rival =
      Window.Observed.Transcript.actualView (word cache choice) (current task cache) task.rival := by
  change Window.Observed.Transcript.actualView (next cache choice).past (current task cache) task.rival = _
  rw [Inquiry.Frame.advance_past]
  rfl

theorem knowledge (covered : Knowledge.Contains cache.views (current task cache)) :
    Knowledge.Contains (next cache choice).views
      ((next cache choice).current (continuation task cache choice).point (continuation task cache choice).rival) := by
  apply Inquiry.Frame.advance_knowledge
  exact Prefix.Rolling.Receipt.the_actual_local_record_generates_its_own_covered_planning_domain
    cache.views (current task cache) covered task.reader

theorem full_actual_responsibility (covered : Knowledge.Contains cache.views (current task cache))
    (future : Opponent task.model.source.code) :
    Synthesis.accepts task.model.source.code (economicAxes (current task cache).point.source (current task cache).point.cut)
      (actualEvaluation task.model (current task cache).point task.original choice.policy.protocol future)
      (actualEvaluation task.model (current task cache).point task.original (reference task cache) future) :=
  Prefix.Rolling.Receipt.a_selected_local_future_protects_every_actual_source_with_that_receipt
    task.model cache.views task.original (reference task cache) task.reader (reading task cache) choice
    (current task cache) covered rfl future
end Handoff

private theorem actual_append {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
    (first later : List (Prefix.Rule code)) (point : View (code := code)) (rival : Opponent code) :
    Window.Observed.Transcript.actualView (first ++ later) point rival =
      Window.Observed.Transcript.actualView later (Window.Observed.Transcript.actualView first point rival) rival := by
  unfold Window.Observed.Transcript.actualView
  exact List.foldl_append

private theorem actual_four {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
    (a b c d : List (Prefix.Rule code)) (point : View (code := code)) (rival : Opponent code) :
    Window.Observed.Transcript.actualView d
      (Window.Observed.Transcript.actualView c
        (Window.Observed.Transcript.actualView b (Window.Observed.Transcript.actualView a point rival) rival) rival) rival =
      Window.Observed.Transcript.actualView (((a ++ b) ++ c) ++ d) point rival := by
  simp only [actual_append]

private theorem leg_current {task : Owned.Task (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)} {cache : Inquiry.Frame task}
    (path : Inquiry.Leg task cache) : current task path.finish =
      Window.Observed.Transcript.actualView path.word (current task cache) task.rival := by
  change Window.Observed.Transcript.actualView path.finish.past task.point task.rival = _
  rw [path.literal,actual_append]
  rfl

/-- Consume the original fee gate without launching the old local-head solver.
The full posterior compiler below is the learning call owned by this charge. -/
def fee (cache : Inquiry.Frame task) : Owned.Turn task cache.restore :=
  if supported : Paid.request task.quote ∈ words task.model.source.code.actions task.model.source.code.actionLimit then
    if booked : cache.restore.Booked (Paid.requestedRule task.reader task.quote supported) then
      if receipt : Paid.funded cache.restore task.reader task.quote task.point task.rival then
        .paid supported booked receipt .exhausted
      else .unpaid supported booked receipt
    else .unreserved supported booked
  else .unsupported supported

private def feePath {cache : Inquiry.Frame task} (event : Owned.Turn task cache.restore) : Inquiry.Leg task cache :=
  ⟨Inquiry.Frame.pack event.final,event.rules,event.past_is_the_literal_actual_word,
    Owned.Turn.knowledge_survives_every_actual_attempt_wait_and_owned_update event,
    Owned.FullPlan.turn task event,
    fun _ prior => Owned.Ancestry.each_paid_or_refused_turn_keeps_every_beliefs_actual_trace task event prior⟩

private theorem event_paid {cache : Inquiry.Frame task} (event : Owned.Turn task cache.restore)
    (funded : event.funded = true) :
    Charge.paid task.quote task.model task.reader (current task cache) task.rival
      (Charge.endAt task.quote task.model task.reader (current task cache) task.rival) := by
  cases event with
  | unsupported | unreserved | unpaid => cases funded
  | paid supported booked receipt walk =>
      exact Payment.a_ready_actual_request_generates_its_own_charge_receipt _ _ _ _ _ receipt

structure Permit (cache : Inquiry.Frame task) : Type where
  live : Driving.Progress.Live cache.shell
  own : Owned.Owns task cache.shell

namespace Handoff
variable {task} (cache : Inquiry.Frame task) (choice : Choice task cache)
theorem live_from_actual_coverage (permit : Permit task cache)
    (covered : Knowledge.Contains cache.views (current task cache)) :
    Driving.Progress.Live (seed cache choice).shell := by
  have remaining := Installation.Chain.fold_remaining (model := task.model) task.point.point task.rival cache.past
  have positive : 0 < (Cut.seed (current task cache).point).remaining := by
    change 0 < (Cut.seed (cache.shell.current task.point task.rival).point).remaining
    rw [Paid.State.current_is_the_actual_control_prefix]
    have amount : (Cut.seed (Splice.install task.point.point task.rival cache.shell.past)).remaining =
        (Cut.seed task.point.point).remaining-cache.shell.past.length := remaining
    rw [amount]
    exact Nat.sub_pos_of_lt permit.live.1
  obtain ⟨representative,inside,matched⟩ := Knowledge.cursor_covered _ _
    (Prefix.Rolling.Receipt.the_actual_local_record_generates_its_own_covered_planning_domain
      cache.views (current task cache) covered task.reader)
  have bound := Continuation.Whole.Complete.each_remaining_horizon_is_generated (domain task cache) representative inside
  rw [matched.horizon] at bound
  change 0 < (Cut.seed (current task cache).point).remaining ∧ 0 < horizon (domain task cache)
  exact ⟨positive,Nat.lt_of_lt_of_le positive bound⟩
end Handoff

structure Waiting (cache : Inquiry.Frame task) where
  path : Inquiry.Leg task cache
  ready : Option (Permit task path.finish)

def wait : Nat → (cache : Inquiry.Frame task) → Waiting task cache
  | 0,cache => ⟨Inquiry.Leg.stay cache,none⟩
  | count+1,cache =>
      if live : Driving.Progress.Live cache.shell then
        if own : Owned.Owns task cache.shell then ⟨Inquiry.Leg.stay cache,some ⟨live,own⟩⟩
        else
          let later := wait count (Inquiry.Frame.advance task cache)
          ⟨(Inquiry.Leg.advance cache).append later.path,later.ready⟩
      else ⟨Inquiry.Leg.stay cache,none⟩

structure Stage (cache : Inquiry.Frame task) where
  event : Owned.Turn task cache.restore
  generated : event = fee task cache
  path : Inquiry.Leg task cache
  ready : Option (Permit task path.finish)
  charged : ready.isSome = true →
    Charge.paid task.quote task.model task.reader (current task cache) task.rival
      (Charge.endAt task.quote task.model task.reader (current task cache) task.rival)

def stage (cache : Inquiry.Frame task) : Stage task cache :=
  let event := fee task cache
  let first := feePath task event
  if paid : event.funded = true then
    let later := wait task (horizon task.domain+1) first.finish
    ⟨event,rfl,first.append later.path,later.ready,fun _ => event_paid task event paid⟩
  else ⟨event,rfl,first,none,by intro impossible;cases impossible⟩

inductive Journey : (task : Owned.Task (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) → Inquiry.Frame task → Type where
  | done {task cache} : Journey task cache
  | carried {task cache} (queried : Inquiry.Result task cache (Inquiry.Receipt task))
      (step : Stage task queried.path.finish) (missing : step.ready = none)
      (later : Journey task step.path.finish) : Journey task cache
  | blocked {task cache} (queried : Inquiry.Result task cache (Inquiry.Receipt task))
      (step : Stage task queried.path.finish) (permit : Permit task step.path.finish) (paid : step.ready = some permit)
      (rejected : ∀ plan,Selection.Rejection task.model (domain task step.path.finish) task.original
        (reference task step.path.finish) plan)
      (generated : compile task step.path.finish = .blocked rejected) : Journey task cache
  | selected {task cache} (queried : Inquiry.Result task cache (Inquiry.Receipt task))
      (step : Stage task queried.path.finish) (permit : Permit task step.path.finish) (paid : step.ready = some permit)
      (choice : Choice task step.path.finish)
      (generated : compile task step.path.finish = .selected choice)
      (later : Journey (continuation task step.path.finish choice) (Handoff.next step.path.finish choice)) : Journey task cache

def run : (count : Nat) → (task : Owned.Task (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) →
    (sender : Fin task.model.source.code.sites) → (cache : Inquiry.Frame task) → Journey task cache
  | 0,_,_,_ => .done
  | count+1,task,sender,cache =>
      let queried := Inquiry.round task sender cache
      let step := stage task queried.path.finish
      match paid : step.ready with
      | none => .carried queried step paid (run count task sender step.path.finish)
      | some permit =>
          match outcome : compile task step.path.finish with
          | .blocked rejected => .blocked queried step permit paid rejected outcome
          | .selected choice => .selected queried step permit paid choice outcome
              (run count (continuation task step.path.finish choice) sender (Handoff.next step.path.finish choice))

namespace Journey
variable {task}
def rules : {task : Owned.Task (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)} → {cache : Inquiry.Frame task} → Journey task cache → List (Prefix.Rule task.model.source.code)
  | _,_,.done => []
  | _,_,.blocked queried step _ _ _ _ => queried.path.word ++ step.path.word
  | _,_,.carried queried step _ later => queried.path.word ++ step.path.word ++ later.rules
  | _,_,.selected queried step _ _ choice _ later =>
      List.append (List.append (List.append queried.path.word step.path.word) (Handoff.word step.path.finish choice)) later.rules

def finish : {task : Owned.Task (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)} → {cache : Inquiry.Frame task} → Journey task cache → View (code := task.model.source.code)
  | task,cache,.done => current task cache
  | task,_,.blocked _ step _ _ _ _ => current task step.path.finish
  | _,_,.carried _ _ _ later => later.finish
  | _,_,.selected _ _ _ _ _ _ later => later.finish

def finalViews : {task : Owned.Task (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)} → {cache : Inquiry.Frame task} → Journey task cache → List (View (code := task.model.source.code))
  | _,cache,.done => cache.views
  | _,_,.blocked _ step _ _ _ _ => step.path.finish.views
  | _,_,.carried _ _ _ later => later.finalViews
  | _,_,.selected _ _ _ _ _ _ later => later.finalViews

theorem literal_history {cache : Inquiry.Frame task} (made : Journey task cache) :
    made.finish = Window.Observed.Transcript.actualView made.rules (current task cache) task.rival := by
  induction made with
  | done => rfl
  | @carried task cache queried step missing later ih =>
      rw [finish,ih,leg_current step.path,leg_current queried.path]
      simp only [rules,actual_append]
  | @blocked task cache queried step audit paid rejected generated =>
      rw [finish,leg_current step.path,leg_current queried.path,←actual_append];rfl
  | @selected task cache queried step audit paid choice generated later ih =>
      rw [finish,ih]
      have handoff : current (continuation task step.path.finish choice) (Handoff.next step.path.finish choice) =
          Window.Observed.Transcript.actualView (Handoff.word step.path.finish choice)
            (current task step.path.finish) task.rival := Handoff.actual_current step.path.finish choice
      calc
        _ = Window.Observed.Transcript.actualView later.rules
            (Window.Observed.Transcript.actualView (Handoff.word step.path.finish choice)
              (current task step.path.finish) task.rival) task.rival :=
          congrArg (fun point : View (code := task.model.source.code) =>
            Window.Observed.Transcript.actualView (later.rules : List (Prefix.Rule task.model.source.code)) point task.rival) handoff
        _ = _ := by
          rw [leg_current step.path,leg_current queried.path]
          exact actual_four queried.path.word step.path.word (Handoff.word step.path.finish choice)
            later.rules (current task cache) task.rival

theorem knowledge {cache : Inquiry.Frame task} (made : Journey task cache)
    (covered : Knowledge.Contains cache.views (current task cache)) :
    Knowledge.Contains made.finalViews made.finish := by
  induction made with
  | done => exact covered
  | carried queried step missing later ih => exact ih (step.path.knowledge (queried.path.knowledge covered))
  | blocked queried step _ _ _ _ => exact step.path.knowledge (queried.path.knowledge covered)
  | selected queried step _ _ choice _ later ih =>
      exact ih (Handoff.knowledge step.path.finish choice (step.path.knowledge (queried.path.knowledge covered)))
end Journey

structure Occurrence (cache : Inquiry.Frame task) (sender : Fin task.model.source.code.sites) (count : Nat) where
  generated : Journey task cache
  exact_generation : generated = run count task sender cache

def occurrence (cache : Inquiry.Frame task) (sender : Fin task.model.source.code.sites) (count : Nat) :
    Occurrence task cache sender count := ⟨run count task sender cache,rfl⟩

namespace Occurrence
variable {task} {cache : Inquiry.Frame task} {sender : Fin task.model.source.code.sites} {count : Nat}
abbrev controls (made : Occurrence task cache sender count) := cache.past ++ made.generated.rules

theorem actual_source (made : Occurrence task cache sender count) :
    made.generated.finish.point = Splice.install task.point.point task.rival made.controls := by
  have actual (word : List (Prefix.Rule task.model.source.code)) (point : View (code := task.model.source.code)) :
      (Window.Observed.Transcript.actualView word point task.rival).point = Splice.install point.point task.rival word := by
    induction word generalizing point with
    | nil => rfl
    | cons rule rest ih => exact ih (Evidence.after point rule task.rival)
  rw [made.generated.literal_history]
  change (Window.Observed.Transcript.actualView made.generated.rules
    (Window.Observed.Transcript.actualView cache.past task.point task.rival) task.rival).point = _
  rw [←actual_append]
  exact actual _ _
end Occurrence


abbrev Generated (sender : Fin task.model.source.code.sites) (rounds : Nat) :=
  Sum (Selection.Rejection task.model task.domain task.original task.baseline task.baseline)
    (Sigma fun cache : Inquiry.Frame task => Occurrence task cache sender rounds)

/-- Initial admission is computed by the task's replaceable verifier. No successful
cache, chosen posterior or successful future is supplied by the caller. -/
def produce (sender : Fin task.model.source.code.sites) (rounds : Nat) : Generated task sender rounds :=
  match Owned.Source.seed task with
  | .rejected reason => .inl reason
  | .accepted cache _ _ _ => .inr ⟨Inquiry.Frame.pack cache,occurrence task (Inquiry.Frame.pack cache) sender rounds⟩

namespace Public
variable (request : PublicTask.Request (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (quotas : List Nat)
  (point : Cursor request.model.source.code) (future : Opponent request.model.source.code)
  (localRounds : Nat) (sender : Fin request.model.source.code.sites) (rounds : Nat)

abbrev Prior := Local.Output request quotas point future localRounds

def Follow (prior : Prior request quotas point future localRounds) : Type := match prior with
  | .inherited _ => Unit
  | .installed fits _ _ choice _ actual _ =>
      Occurrence (PublicTask.Feedback.task request _ fits quotas point future choice)
        (Inquiry.Frame.pack actual.1) sender rounds

def follow (prior : Prior request quotas point future localRounds) : Follow request quotas point future localRounds sender rounds prior :=
  match prior with
  | .inherited _ => ()
  | .installed fits _ _ choice _ actual _ =>
      occurrence (PublicTask.Feedback.task request _ fits quotas point future choice) (Inquiry.Frame.pack actual.1) sender rounds

def produce :=
  let prior := Local.produce request quotas point future localRounds
  Sigma.mk prior (follow request quotas point future localRounds sender rounds prior)

def Sound (prior : Prior request quotas point future localRounds)
    (next : Follow request quotas point future localRounds sender rounds prior) : Prop :=
  prior.Sound ∧ match prior,next with
  | .inherited _,_ => True
  | .installed fits _ _ choice _ _actual _,next =>
      let task := PublicTask.Feedback.task request _ fits quotas point future choice
      Knowledge.Contains next.generated.finalViews next.generated.finish ∧
      next.generated.finish.point = Splice.install task.point.point task.rival next.controls

theorem follows_the_same_source (prior : Prior request quotas point future localRounds) (sound : prior.Sound) :
    Sound request quotas point future localRounds sender rounds prior
      (follow request quotas point future localRounds sender rounds prior) := by
  refine ⟨sound,?_⟩
  cases prior with
  | inherited => trivial
  | installed fits work released choice selected actual generated =>
      let task := PublicTask.Feedback.task request _ fits quotas point future choice
      let made := occurrence task (Inquiry.Frame.pack actual.1) sender rounds
      exact ⟨made.generated.knowledge sound.2.1,made.actual_source⟩

theorem all_public_histories_generate_paid_posterior_choices_and_actual_continuations
    (origin : Distributed.Recall.Information.Origin request.model)
    (stages : List (EventHistory.Stage (code := request.model.source.code)))
    (installed : stages.map Prod.fst = request.installed) :
    let current := EventHistory.execute (EventHistory.ofOrigin request.model request.budget origin) stages
    Sound request quotas current future localRounds sender rounds
      (produce request quotas current future localRounds sender rounds).1
      (produce request quotas current future localRounds sender rounds).2 :=
  follows_the_same_source request quotas _ future localRounds sender rounds _
    (Local.all_public_histories_generate_actual_local_installation request quotas future localRounds origin stages installed)
end Public


end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Local.Inquiry.Planning
