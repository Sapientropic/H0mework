import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Normalization.Evaluation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Normalization

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (input : Input model.source.code) (cut : Nat) (active : model.source.feedback? = some input)
  (empty : model.source.continuation = []) (raw : List (Option model.source.code.Policy))
  (rival : Opponent model.source.code) (party : Party) (good : Good)

include empty in
theorem the_original_gross_cost_is_the_full_evaluations_material_reading :
    cost model.source.code (Residual.scheduleAt model.source cut raw) ⟨rival,input.budget⟩
      (Residual.seed model.source input cut) (Cut.horizon model.source input cut) party good =
    (evaluate model input cut active rival raw).value (.material (.debit party good)) := by
  change _ = RawProfile.material model.source input cut rival raw (.debit party good)
  unfold cost RawProfile.material
  apply congrArg List.sum
  apply List.map_congr_left
  intro offset _
  let target := Future.target model.source input cut rival raw
  have current := target.feedback_body_reads_the_actual_local_current (Future.takeover model.source input cut rival) rfl empty (cut+offset)
  rw [Future.the_whole_future_run_is_the_actual_state] at current
  have word := Future.future_word_is_actually_submitted model.source input cut rival raw empty offset
  have address : RawProfile.start model.source cut-1+offset = model.source.history.length+1+(cut+offset) := by
    dsimp only [RawProfile.start]
    omega
  rw [address]
  change model.source.code.law.totalDebit (model.source.code.law.rawItems _ _) party good =
    model.source.code.law.totalDebit (target.actualExecution (model.source.history.length+1+(cut+offset))).interpreted.items party good
  have exactItems := congrArg (fun execution => execution.items)
    (target.actualExecution (model.source.history.length+1+(cut+offset))).interpreted_exact
  change (target.actualExecution (model.source.history.length+1+(cut+offset))).interpreted.items =
    model.source.code.law.rawItems (target.actualExecution (model.source.history.length+1+(cut+offset))).before
      (target.actualExecution (model.source.history.length+1+(cut+offset))).submitted at exactItems
  rw [exactItems,word,← current]

theorem every_original_material_axis_is_compared :
    EconomicAxis.material (.debit party good) ∈ economicAxes model.source cut := by
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_map.mpr
  refine ⟨.debit party good,?_,rfl⟩
  apply List.mem_append_left
  exact List.mem_flatMap.mpr ⟨party,model.source.code.parties_cover party,
    List.mem_flatMap.mpr ⟨good,model.source.code.goods_cover good,by simp⟩⟩

include empty in
theorem full_acceptance_generates_the_original_paid_certificate
    (supported : Source.Supported model.source cut raw (Cut.horizon model.source input cut))
    (reference : Evaluation model.source.code)
    (accepted : Synthesis.accepts model.source.code (economicAxes model.source cut)
      (evaluate model input cut active rival raw) reference)
    (budget : ℚ) (publicBound : reference.value (.material (.debit party good)) ≤ budget) :
    Source.Paid model.source input cut raw (Cut.horizon model.source input cut) party good budget rival := by
  apply Source.original_observed_acceptance_generates_paid_work model.source input cut raw
    (Cut.horizon model.source input cut) party good budget rival supported
  · rw [the_original_gross_cost_is_the_full_evaluations_material_reading model input cut active empty raw rival party good]
    exact (accepted.2.2.2.2 _ (every_original_material_axis_is_compared model cut party good)).trans publicBound
  · exact accepted.1

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Normalization
