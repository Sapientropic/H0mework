import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.History
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Local.Inquiry.Planning.Committed.CompleteSelection.Execution.Runtime

set_option autoImplicit false
set_option maxRecDepth 65536

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Local.Inquiry.Planning.Committed.CompleteSelection.Observation

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

/-- A presentation of this source's memory syntax, not an extra strategy or successful plan. -/
structure Memory where
  base : Code Party Good Port (Mandate.State Party Technology) Instrument
  capacity : Nat
  same : task.model.source.code = Recall.lift base capacity

variable (memory : Memory task)

abbrev Strategy := History.Strategy memory.base memory.capacity

def rule (strategy : Strategy task memory) : Rule task.model.source.code :=
  memory.same.symm ▸ History.tabulate memory.base memory.capacity strategy

def tail (strategies : List (Strategy task memory)) : Complete.FiniteProgram task.model.source.code :=
  ⟨strategies.length,⟨strategies.map (rule task memory),by simp⟩⟩

variable (cache : Inquiry.Frame task)

theorem every_admissible_observation_strategy_is_actually_in_the_compilers_pool
    (strategies : List (Strategy task memory))
    (valid : admissible task cache (tail task memory strategies)) :
    ∃ candidate ∈ candidates task cache,
      candidate.protocol = wholePlan task cache (tail task memory strategies) :=
  every_admissible_finite_tail_is_generated task cache _ valid

def Contract (choice : Choice task cache) : Prop :=
  (∀ strategies : List (Strategy task memory),admissible task cache (tail task memory strategies) →
    ¬ Distributed.Improves (Selection.axes (fuel := horizon task.domain) task.model task.domain)
      (Selection.benefit task.model task.domain task.original) choice.policy.protocol
      (wholePlan task cache (tail task memory strategies))) ∧
  ((∃ strategies : List (Strategy task memory),admissible task cache (tail task memory strategies) ∧
    Distributed.Improves (Selection.axes (fuel := horizon task.domain) task.model task.domain)
      (Selection.benefit task.model task.domain task.original) cache.programme
      (wholePlan task cache (tail task memory strategies))) →
    Distributed.Improves (Selection.axes (fuel := horizon task.domain) task.model task.domain)
      (Selection.benefit task.model task.domain task.original) cache.programme choice.policy.protocol)

theorem every_actual_choice_covers_complete_local_observation_strategies (choice : Choice task cache) :
    Contract task memory cache choice := by
  constructor
  · intro strategies valid
    exact selected_has_no_admissible_finite_dominator task cache choice _ valid
  · rintro ⟨strategies,valid,better⟩
    exact every_available_admissible_strict_improvement_is_selected task cache choice
      ⟨tail task memory strategies,valid,better⟩

theorem every_rejected_observation_strategy_has_its_original_failure_row
    (rejected : ∀ programme : Complete.FiniteProgram task.model.source.code,Rejection task cache programme)
    (strategies : List (Strategy task memory)) :
    rejectedRowFails task cache (tail task memory strategies) (rejected (tail task memory strategies)) = true :=
  every_rejection_replays_its_own_original_row task cache _ _

def WalkContract : {cache : Inquiry.Frame task} → Execution.Walk task cache → Prop
  | _,.done => True
  | _,.carried _ _ _ later => WalkContract later
  | _,.blocked _ step _ _ rejected later =>
      (∀ strategies : List (Strategy task memory),
        rejectedRowFails task step.path.finish (tail task memory strategies)
          (rejected (tail task memory strategies)) = true) ∧ WalkContract later
  | _,.selected _ step _ _ choice later =>
      Contract task memory step.path.finish choice ∧ WalkContract later

theorem the_complete_actual_feedback_walk_has_full_observation_strategy_coverage
    {cache : Inquiry.Frame task} (walk : Execution.Walk task cache) : WalkContract task memory walk := by
  induction walk with
  | done => trivial
  | carried _ _ _ _ ih => exact ih
  | blocked _ step _ _ rejected _ ih =>
      exact ⟨fun strategies => every_rejected_observation_strategy_has_its_original_failure_row
        task memory step.path.finish rejected strategies,ih⟩
  | selected _ step _ _ choice _ ih =>
      exact ⟨every_actual_choice_covers_complete_local_observation_strategies task memory step.path.finish choice,ih⟩

theorem the_same_actual_root_consumes_the_observation_strategy_contract
    (compiler : Execution.Compiler task) (cache : Inquiry.Frame task)
    (sender : Fin task.model.source.code.sites) (rounds : Nat)
    (made : Execution.Occurrence task compiler cache sender rounds) :
    Execution.Runtime.read task compiler cache sender rounds made made.controls.length = some made ∧
    WalkContract task memory made.generated ∧
    let active := (Execution.Runtime.facade task compiler cache sender rounds made).seed.advance
      (arrival (Execution.Runtime.full task compiler cache sender rounds made))
    HEq ((Execution.Runtime.facade task compiler cache sender rounds made).readoutAt active .inquiry)
      (active.tick.generated.projectionOutcome
        (((Execution.Runtime.facade task compiler cache sender rounds made).installationAt active .inquiry).embed
          ((Execution.Runtime.facade task compiler cache sender rounds made).projectionAt active .inquiry))) ∧
    HEq active.tick.generated.wholeLedgerWriteBack
      (active.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt active.current.visit.current) ∧
    active.tick.nextCurrent = ((Execution.Runtime.facade task compiler cache sender rounds made).seed.advance
      (arrival (Execution.Runtime.full task compiler cache sender rounds made)+1)).current := by
  refine ⟨Execution.Runtime.the_final_named_read_releases_its_source_generated_outcome task compiler cache sender rounds made,
    the_complete_actual_feedback_walk_has_full_observation_strategy_coverage task memory made.generated,?_⟩
  exact Execution.Runtime.all_closed_faces_consume_the_same_full_ledger_and_generated_next
    task compiler cache sender rounds made _ .inquiry

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Local.Inquiry.Planning.Committed.CompleteSelection.Observation
