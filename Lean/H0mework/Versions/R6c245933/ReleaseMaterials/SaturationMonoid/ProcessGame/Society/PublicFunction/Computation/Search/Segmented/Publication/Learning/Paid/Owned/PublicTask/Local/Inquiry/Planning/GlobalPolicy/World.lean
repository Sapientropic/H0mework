import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Local.Inquiry.Planning
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskInput.Work

import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskInput.Work.Actual

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Local.Inquiry.Planning.GlobalPolicy.World
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (task : Owned.Task (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

def units (input : WorldInput task.model.base task.model.scope) : Nat :=
  World.TaskInput.Work.units input (Native.Authority.sourceIndex task.model) task.domain task.futureRequests +
    World.TaskInput.Work.Reconstruction.units input task + World.TaskInput.Work.Actual.units input task

abbrev Batch (input : WorldInput task.model.base task.model.scope) :=
  World.TaskInput.Work.Reconstruction.OriginalBatch input task

def execute (input : WorldInput task.model.base task.model.scope) : Batch task input :=
  World.TaskInput.Work.Reconstruction.executeOriginal input task

/-- Both directories and the stronger outcome belong to the same paid call. -/
structure Selection (input : WorldInput task.model.base task.model.scope) (state : Inquiry.Frame task) where
  private mk ::
  batch : Batch task input
  batch_generated : batch = execute task input
  reconstructed : World.TaskInput.Work.Reconstruction.Batch input task batch
  reconstructed_generated : reconstructed = World.TaskInput.Work.Reconstruction.execute input task batch
  outcome : World.TaskInput.Work.Actual.Outcome input task batch reconstructed state.past state.programme
  outcome_generated : outcome = World.TaskInput.Work.Actual.compile input task batch reconstructed
    state.past state.programme

def select (input : WorldInput task.model.base task.model.scope) (state : Inquiry.Frame task) : Selection task input state :=
  let batch := execute task input
  let reconstructed := World.TaskInput.Work.Reconstruction.execute input task batch
  ⟨batch,rfl,reconstructed,rfl,World.TaskInput.Work.Actual.compile input task batch reconstructed
    state.past state.programme,rfl⟩

def Selection.candidate? {input : WorldInput task.model.base task.model.scope} {state : Inquiry.Frame task}
    (selected : Selection task input state) :=
  World.TaskInput.Work.Actual.candidate? input task selected.batch selected.reconstructed
    state.past state.programme selected.outcome

def Selection.Reviewed {input : WorldInput task.model.base task.model.scope} {state : Inquiry.Frame task}
    (selected : Selection task input state) : Prop :=
  World.TaskInput.Work.Actual.Reviewed input task selected.batch selected.reconstructed
    state.past state.programme selected.outcome

theorem Selection.reviewed {input : WorldInput task.model.base task.model.scope} {state : Inquiry.Frame task}
    (selected : Selection task input state) : selected.Reviewed task :=
  World.TaskInput.Work.Actual.reviewed input task selected.batch selected.reconstructed
    state.past state.programme selected.outcome


variable {input : WorldInput task.model.base task.model.scope} {state : Inquiry.Frame task}
theorem Selection.actual_protection (selected : Selection task input state)
    (candidate : Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Global.Candidate
      (tariff := task.recoveryPricing) (requested := task.futureRequests)
      task.model task.domain task.original state.past state.programme)
    (chosen : selected.candidate? task = some candidate) :
    World.TaskInput.Work.Actual.Protection input task state.past state.programme candidate :=
  World.TaskInput.Work.Actual.selected_has_its_actual_protection input task selected.batch selected.reconstructed
    state.past state.programme candidate selected.outcome chosen

theorem Selection.original_query_protection (selected : Selection task input state)
    (candidate : Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Global.Candidate
      (tariff := task.recoveryPricing) (requested := task.futureRequests)
      task.model task.domain task.original state.past state.programme)
    (chosen : selected.candidate? task = some candidate) :
    World.TaskInput.Work.Actual.QueryProtection input task selected.batch state.past state.programme candidate :=
  World.TaskInput.Work.Actual.selected_keeps_the_original_queries input task selected.batch selected.reconstructed
    state.past state.programme selected.outcome candidate chosen

theorem Selection.received_future_protection (selected : Selection task input state)
    (candidate : Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Global.Candidate
      (tariff := task.recoveryPricing) (requested := task.futureRequests)
      task.model task.domain task.original state.past state.programme)
    (chosen : selected.candidate? task = some candidate) :
    World.TaskInput.Work.Actual.FutureProtection input task state.past state.programme candidate :=
  World.TaskInput.Work.Actual.selected_keeps_the_received_future input task selected.batch selected.reconstructed
    state.past state.programme selected.outcome candidate chosen

/-- The original charge pays the complete finite service directory before any
World window/report is evaluated. Partial payment retains the actual Stage. -/
inductive Gate (cache : Inquiry.Frame task) where
  | unavailable (step : Stage task cache) (generated : step = stage task cache)
      (missing : step.ready = none)
  | legacy (step : Stage task cache) (generated : step = stage task cache)
      (permit : Permit task step.path.finish) (paid : step.ready = some permit)
      (absent : task.worldInput = none)
  | short (step : Stage task cache) (generated : step = stage task cache)
      (permit : Permit task step.path.finish) (paid : step.ready = some permit)
      (input : WorldInput task.model.base task.model.scope) (supplied : task.worldInput = some input)
      (rate : Fin task.model.source.code.actions.length) (declared : task.accountingRate = some rate)
      (missing : ¬ Accounting.covers task (Charge.fee task.quote) task.model.source.code.actions[rate]
        (1 + Accounting.selectionUnits task + units task input))
  | covered (step : Stage task cache) (generated : step = stage task cache)
      (permit : Permit task step.path.finish) (paid : step.ready = some permit)
      (input : WorldInput task.model.base task.model.scope) (supplied : task.worldInput = some input)
      (rate : Fin task.model.source.code.actions.length) (declared : task.accountingRate = some rate)
      (covered : Accounting.covers task (Charge.fee task.quote) task.model.source.code.actions[rate]
        (1 + Accounting.selectionUnits task + units task input))

def preflight (cache : Inquiry.Frame task) : Gate task cache :=
  let step := stage task cache
  match paid : step.ready with
  | none => .unavailable step rfl paid
  | some permit => match supplied : task.worldInput with
      | none => .legacy step rfl permit paid supplied
      | some input => match declared : task.accountingRate with
          | none => False.elim (by
              obtain ⟨rate,found,_⟩ := Stage.every_released_world_input_has_its_actual_prior_charge
                task step (by rw [paid];rfl) input supplied
              rw [declared] at found
              cases found)
          | some rate =>
              if covered : Accounting.covers task (Charge.fee task.quote) task.model.source.code.actions[rate]
                  (1 + Accounting.selectionUnits task + units task input) then
                .covered step rfl permit paid input supplied rate declared covered
              else .short step rfl permit paid input supplied rate declared covered

def Output {cache : Inquiry.Frame task} : Gate task cache → Type
  | .covered step _ _ _ input _ _ _ _ => Selection task input step.path.finish
  | _ => Unit

def consume {cache : Inquiry.Frame task} (gate : Gate task cache) : Output task gate :=
  match gate with
  | .covered step _ _ _ input _ _ _ _ => select task input step.path.finish
  | .unavailable .. | .legacy .. | .short .. => ()

def run (cache : Inquiry.Frame task) : Sigma (fun gate : Gate task cache => Output task gate) :=
  let gate := preflight task cache
  ⟨gate,consume task gate⟩

variable {task}
theorem every_completed_directory_has_its_actual_prior_payment
    {cache : Inquiry.Frame task} (step : Stage task cache) (permit : Permit task step.path.finish)
    (paid : step.ready = some permit) (input : WorldInput task.model.base task.model.scope)
    (rate : Fin task.model.source.code.actions.length)
    (covered : Accounting.covers task (Charge.fee task.quote) task.model.source.code.actions[rate]
      (1 + Accounting.selectionUnits task + units task input)) :
    Charge.paid task.quote task.model task.reader (Planning.current task cache) task.rival
      (Charge.endAt task.quote task.model task.reader (Planning.current task cache) task.rival) ∧
    ∀ good : Good, ((1 + Accounting.selectionUnits task + units task input : Nat) : ℚ) *
      Accounting.quantity task.model.source.code.actions[rate] good ≤ Accounting.debit (Charge.fee task.quote) good :=
  ⟨step.charged (by rw [paid];rfl),fun good => covered.2 good (task.model.source.code.goods_cover good)⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Local.Inquiry.Planning.GlobalPolicy.World
