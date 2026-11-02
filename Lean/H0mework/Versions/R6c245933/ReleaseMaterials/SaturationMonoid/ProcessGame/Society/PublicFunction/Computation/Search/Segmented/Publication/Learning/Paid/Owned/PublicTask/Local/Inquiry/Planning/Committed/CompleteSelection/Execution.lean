import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Local.Inquiry.Planning.Committed.CompleteSelection

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 600000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Local.Inquiry.Planning.Committed.CompleteSelection.Execution
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

abbrev Compiler := (cache : Inquiry.Frame task) → CompleteSelection.Outcome task cache

inductive Walk : Inquiry.Frame task → Type where
  | done {cache} : Walk cache
  | carried {cache} (queried : Inquiry.Result task cache (Inquiry.Receipt task))
      (step : Planning.Stage task queried.path.finish) (missing : step.ready = none)
      (later : Walk step.path.finish) : Walk cache
  | blocked {cache} (queried : Inquiry.Result task cache (Inquiry.Receipt task))
      (step : Planning.Stage task queried.path.finish) (permit : Planning.Permit task step.path.finish)
      (paid : step.ready = some permit)
      (rejected : ∀ tail : Complete.FiniteProgram task.model.source.code,CompleteSelection.Rejection task step.path.finish tail)
      (later : Walk (Inquiry.Frame.advance task step.path.finish)) : Walk cache
  | selected {cache} (queried : Inquiry.Result task cache (Inquiry.Receipt task))
      (step : Planning.Stage task queried.path.finish) (permit : Planning.Permit task step.path.finish)
      (paid : step.ready = some permit) (choice : CompleteSelection.Choice task step.path.finish)
      (later : Walk (Committed.acceptedPath task step.path.finish ⟨_,choice.policy.tail⟩ choice.policy.accepted.2).finish) : Walk cache

def run (compiler : Compiler task) : Nat → (sender : Fin task.model.source.code.sites) → (cache : Inquiry.Frame task) → Walk task cache
  | 0,_,_ => .done
  | count+1,sender,cache =>
      let queried := Inquiry.round task sender cache
      let step := Planning.stage task queried.path.finish
      match paid : step.ready with
      | none => .carried queried step paid (run compiler count sender step.path.finish)
      | some permit =>
          match compiler step.path.finish with
          | .blocked rejected => .blocked queried step permit paid rejected
              (run compiler count sender (Inquiry.Frame.advance task step.path.finish))
          | .selected choice => .selected queried step permit paid choice
              (run compiler count sender (Committed.acceptedPath task step.path.finish ⟨_,choice.policy.tail⟩ choice.policy.accepted.2).finish)

namespace Walk
variable {task}
def path : {cache : Inquiry.Frame task} → Walk task cache → Inquiry.Leg task cache
  | cache,.done => Inquiry.Leg.stay cache
  | _,.carried queried step _ later => queried.path.append (step.path.append later.path)
  | _,.blocked queried step _ _ _ later =>
      queried.path.append (step.path.append ((Inquiry.Leg.advance step.path.finish).append later.path))
  | _,.selected queried step _ _ choice later =>
      queried.path.append (step.path.append
        ((Committed.acceptedPath task step.path.finish ⟨_,choice.policy.tail⟩ choice.policy.accepted.2).append later.path))
end Walk

structure Occurrence (compiler : Compiler task) (cache : Inquiry.Frame task)
    (sender : Fin task.model.source.code.sites) (rounds : Nat) where
  generated : Walk task cache
  exact_generation : generated = run task compiler rounds sender cache

def occurrence (compiler : Compiler task) (cache : Inquiry.Frame task)
    (sender : Fin task.model.source.code.sites) (rounds : Nat) : Occurrence task compiler cache sender rounds :=
  ⟨run task compiler rounds sender cache,rfl⟩

namespace Occurrence
variable {task} {compiler : Compiler task} {cache : Inquiry.Frame task}
  {sender : Fin task.model.source.code.sites} {rounds : Nat}
abbrev path (made : Occurrence task compiler cache sender rounds) := made.generated.path.append
  (Committed.drain task (Computation.Cut.seed task.point.point).remaining made.generated.path.finish)
abbrev final (made : Occurrence task compiler cache sender rounds) := made.path.finish
abbrev controls (made : Occurrence task compiler cache sender rounds) := made.final.past

theorem actual_source (made : Occurrence task compiler cache sender rounds) :
    (made.final.current task.point task.rival).point = Splice.install task.point.point task.rival made.controls :=
  Paid.State.current_is_the_actual_control_prefix made.final.shell task.point task.rival

theorem the_generated_chain_completes_its_original_actual_window
    (made : Occurrence task compiler cache sender rounds)
    (covered : Knowledge.Contains (Owned.Source.initialBeliefs task) task.point) :
    made.controls.length = (Computation.Cut.seed task.point.point).remaining := by
  have coverage : Continuation.Covered task.domain task.point.point := by
    simpa [Owned.Source.initialBeliefs,Function.comp_def] using Knowledge.cursor_covered _ _ covered
  obtain ⟨representative,inside,matched⟩ := coverage
  have upper := Continuation.Whole.Complete.each_remaining_horizon_is_generated task.domain representative inside
  rw [matched.horizon] at upper
  exact Committed.drain_complete task _ _ upper (by omega)

theorem the_complete_actual_chain_protects_every_original_responsibility
    (made : Occurrence task compiler cache sender rounds)
    (covered : Knowledge.Contains (Owned.Source.initialBeliefs task) task.point)
    (future : Opponent task.model.source.code) :
    Synthesis.accepts task.model.source.code (economicAxes task.point.point.source task.point.point.cut)
      (actualEvaluation task.model task.point.point task.original (Splice.word made.controls) future)
      (actualEvaluation task.model task.point.point task.original task.baseline future) := by
  have same : actualEvaluation task.model task.point.point task.original (Splice.word made.controls) future =
      actualEvaluation task.model task.point.point task.original made.final.programme future := by
    apply stages_generate_the_same_complete_evaluation
    intro offset inside
    apply Prefix.Commitment.retained_stages task.original made.final.programme made.controls made.final.retained
    rw [made.the_generated_chain_completes_its_original_actual_window covered]
    exact inside
  rw [same]
  apply Observation.public_domain_acceptance_protects_every_covered_actual_source task.model task.point.point task.original
    made.final.programme future task.domain
  · simpa [Owned.Source.initialBeliefs,Function.comp_def] using Knowledge.cursor_covered _ _ covered
  · exact made.final.above
end Occurrence

abbrev Generated (compiler : Compiler task) (sender : Fin task.model.source.code.sites) (rounds : Nat) :=
  Sum (Selection.Rejection task.model task.domain task.original task.baseline task.baseline)
    (Sigma fun cache : Inquiry.Frame task => Occurrence task compiler cache sender rounds)

def produce (compiler : Compiler task) (sender : Fin task.model.source.code.sites) (rounds : Nat) : Generated task compiler sender rounds :=
  match Owned.Source.seed task with
  | .rejected reason => .inl reason
  | .accepted cache _ _ _ => .inr ⟨Inquiry.Frame.pack cache,occurrence task compiler (Inquiry.Frame.pack cache) sender rounds⟩

private theorem original_cursor_covered
    (covered : Knowledge.Contains (Owned.Source.initialBeliefs task) task.point) :
    Continuation.Covered task.domain task.point.point := by
  simpa [Owned.Source.initialBeliefs,Function.comp_def] using Knowledge.cursor_covered _ _ covered

private theorem nondomination_survives {Policy Axis : Type} (axes : List Axis) (benefit : Policy → Axis → ℚ)
    (old next other : Policy) (maximal : ¬ Distributed.Improves axes benefit old other)
    (above : Distributed.NoWorse axes benefit next old) : ¬ Distributed.Improves axes benefit next other := by
  intro strict
  exact maximal ⟨Distributed.noWorse_trans strict.1 above,
    fun reverse => strict.2 (Distributed.noWorse_trans above reverse)⟩

namespace Public
variable (request : PublicTask.Request (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (quotas : List Nat)
  (point : Cursor request.model.source.code) (future : Opponent request.model.source.code)
  (localRounds : Nat) (sender : Fin request.model.source.code.sites) (rounds : Nat)

abbrev Prior := Local.Output request quotas point future localRounds

def Follow (prior : Prior request quotas point future localRounds) : Type := match prior with
  | .inherited _ => Unit
  | .installed fits _ _ choice _ actual _ =>
      let task := PublicTask.Feedback.task request _ fits quotas point future choice
      Occurrence task (CompleteSelection.compile task) (Inquiry.Frame.pack actual.1) sender rounds

def follow (prior : Prior request quotas point future localRounds) : Follow request quotas point future localRounds sender rounds prior :=
  match prior with
  | .inherited _ => ()
  | .installed fits _ _ choice _ actual _ =>
      let task := PublicTask.Feedback.task request _ fits quotas point future choice
      occurrence task (CompleteSelection.compile task) (Inquiry.Frame.pack actual.1) sender rounds

def produce :=
  let prior := Local.produce request quotas point future localRounds
  Sigma.mk prior (follow request quotas point future localRounds sender rounds prior)

def Sound (prior : Prior request quotas point future localRounds)
    (next : Follow request quotas point future localRounds sender rounds prior) : Prop :=
  prior.Sound ∧ match prior,next with
  | .inherited _,_ => True
  | .installed fits _ _ choice _ actual _,next =>
      let task := PublicTask.Feedback.task request _ fits quotas point future choice
      Selection.acceptable request.model task.domain request.original (PaidSearch.reference request _ fits) next.final.programme ∧
      Knowledge.Contains next.final.views (next.final.current task.point task.rival) ∧
      (∃ suffix, next.controls = actual.1.past ++ suffix) ∧
      next.controls.length = (Computation.Cut.seed point).remaining ∧
      (∀ rival : Opponent request.model.source.code,
        Synthesis.accepts request.model.source.code (economicAxes point.source point.cut)
          (actualEvaluation request.model point request.original (Splice.word next.controls) rival)
          (actualEvaluation request.model point request.original (PaidSearch.reference request _ fits) rival)) ∧
      (∀ other ∈ Prefix.candidates request.model task.domain request.original
          (PaidSearch.fees request quotas) (PaidSearch.reference request _ fits),
        ¬ Distributed.Improves (Selection.axes (fuel := horizon task.domain) request.model task.domain)
          (Selection.benefit request.model task.domain request.original) next.final.programme other.protocol)

theorem follows_the_original_whole_responsibility (prior : Prior request quotas point future localRounds)
    (sound : prior.Sound)
    (covered : Knowledge.Contains
      (fiber (PublicTask.views request) request.reader (observation (currentView point) request.reader)) (currentView point)) :
    Sound request quotas point future localRounds sender rounds prior
      (follow request quotas point future localRounds sender rounds prior) := by
  refine ⟨sound,?_⟩
  cases prior with
  | inherited => trivial
  | installed fits work released choice selected actual generated =>
      let task := PublicTask.Feedback.task request _ fits quotas point future choice
      let made := occurrence task (CompleteSelection.compile task) (Inquiry.Frame.pack actual.1) sender rounds
      have initial : Knowledge.Contains (Owned.Source.initialBeliefs task) task.point := by
        have reset := PublicTask.reset_preserves_complete_coverage _ _ covered
        simpa only [task,Owned.Source.initialBeliefs,PublicTask.Feedback.task,PublicTask.domain,List.map_map,
          Function.comp_def,PublicTask.currentView] using reset
      refine ⟨Selection.acceptable_trans _ _ _ _ _ _ made.final.above choice.policy.accepted,
        made.path.knowledge sound.2.1,⟨_,made.path.literal⟩,
        made.the_generated_chain_completes_its_original_actual_window initial,?_,?_⟩
      · intro rival
        have first := made.the_complete_actual_chain_protects_every_original_responsibility initial rival
        have second := Observation.public_domain_acceptance_protects_every_covered_actual_source request.model point
          request.original choice.policy.protocol rival task.domain (original_cursor_covered task initial)
          (PaidSearch.reference request _ fits) choice.policy.accepted
        exact Synthesis.accepts_trans _ _ _ _ _ first second
      · intro other inside
        exact nondomination_survives
          (Selection.axes (fuel := horizon task.domain) task.model task.domain)
          (Selection.benefit task.model task.domain task.original)
          choice.policy.protocol made.final.programme other.protocol (choice.maximal other inside)
          (Selection.acceptance_bounds_every_benefit task.model task.domain task.original
            task.baseline made.final.programme made.final.above)


theorem all_legal_public_histories_generate_complete_paid_chains_with_original_responsibility
    (origin : Distributed.Recall.Information.Origin request.model)
    (stages : List (EventHistory.Stage (code := request.model.source.code)))
    (installed : stages.map Prod.fst = request.installed) :
    let current := EventHistory.execute (EventHistory.ofOrigin request.model request.budget origin) stages
    Sound request quotas current future localRounds sender rounds
      (produce request quotas current future localRounds sender rounds).1
      (produce request quotas current future localRounds sender rounds).2 :=
  follows_the_original_whole_responsibility request quotas _ future localRounds sender rounds _
    (Local.all_public_histories_generate_actual_local_installation request quotas future localRounds origin stages installed)
    (PublicTask.every_actual_receipt_has_a_complete_local_source request origin stages installed)
end Public

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Local.Inquiry.Planning.Committed.CompleteSelection.Execution
