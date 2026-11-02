import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.Runtime

set_option autoImplicit false
set_option maxRecDepth 65536

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (task : Task (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

theorem each_public_origin_view_generates_its_own_initial_belief
    (actual : View (code := task.model.source.code)) (inside : actual.point ∈ task.domain)
    (origin : actual.origin.val = arrival actual.point) :
    Knowledge.Contains (Source.initialBeliefs task) actual := by
  refine ⟨⟨actual.point,⟨arrival actual.point,by omega⟩⟩,
    List.mem_map.mpr ⟨actual.point,inside,rfl⟩,?_⟩
  exact ⟨Aligned.refl _,origin.symm⟩

theorem advancing_keeps_the_installed_planner (state : Cache task) :
    (advance task state).planner = state.planner := by
  change (Driving.Progress.next state).planner = state.planner
  unfold Driving.Progress.next
  split <;> rfl

theorem committing_keeps_the_installed_planner (state : Cache task)
    (reading : Fin task.model.source.code.signals) (decision : state.Decision task.reader) :
    (state.commit task.reader reading decision).planner = state.planner := by
  cases decision <;> rfl

namespace Walk
variable {task} {state : Cache task}
theorem final_keeps_the_installed_planner (walk : Walk task state) :
    walk.final.planner = state.planner := by
  induction walk with
  | exhausted | terminal => rfl
  | @learned state live owned decision =>
      exact (advancing_keeps_the_installed_planner task _).trans
        (committing_keeps_the_installed_planner task state _ decision)
  | waiting live foreign later ih =>
      exact ih.trans (advancing_keeps_the_installed_planner task _)
end Walk

namespace Turn
variable {task} {state : Cache task}
theorem final_keeps_the_installed_planner (event : Turn task state) :
    event.final.planner = state.planner := by
  cases event with
  | unsupported | unpaid => rfl
  | unreserved =>
      change (if task.continueUnreserved then advance task state else state).planner = state.planner
      by_cases continuing : task.continueUnreserved = true
      · rw [if_pos continuing]
        exact advancing_keeps_the_installed_planner task state
      · rw [if_neg continuing]
  | paid supported booked receipt walk => exact walk.final_keeps_the_installed_planner
end Turn

theorem every_paid_feedback_run_keeps_the_installed_planner (rounds : Nat) (state : Cache task) :
    (run task rounds state).planner = state.planner := by
  induction rounds generalizing state with
  | zero => rfl
  | succ rounds ih =>
      exact (ih (turn task state).final).trans (turn task state).final_keeps_the_installed_planner

theorem every_paid_feedback_trace_keeps_the_installed_planner (rounds : Nat) (state : Cache task) :
    (trace task rounds state).1.planner = state.planner := by
  rw [trace_is_the_original_run_and_reports]
  exact every_paid_feedback_run_keeps_the_installed_planner task rounds state

theorem the_source_seed_installs_its_own_planner :
    match Source.seed task with
    | .rejected _ => True
    | .accepted cache _ _ _ => cache.planner = task.planner := by
  by_cases checked : Selection.acceptable task.model task.domain task.original task.baseline task.baseline
  · simp only [Source.seed,dif_pos checked]
  · cases found : Distributed.inspect (Selection.holds task.model task.domain task.original task.baseline task.baseline)
        (Replanning.rows task.model task.domain) with
    | rejected row generated broken =>
        simp only [Source.seed,dif_neg checked,found]
    | accepted all => exact False.elim (checked all)

theorem every_source_generated_cache_keeps_its_own_planner (rounds : Nat) :
    match Source.generate task rounds with
    | .inl _ => True
    | .inr actual => actual.1.planner = task.planner := by
  have seeded := the_source_seed_installs_its_own_planner task
  unfold Source.generate
  cases made : Source.seed task with
  | rejected => trivial
  | accepted cache empty programme beliefs =>
      rw [made] at seeded
      exact (every_paid_feedback_trace_keeps_the_installed_planner task rounds cache).trans seeded

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned
