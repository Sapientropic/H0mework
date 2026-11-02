import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Flow.Matrix
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Open.Completion.Bounds

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Flow

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (point : Cursor model.source.code) (fallback : Rule model.source.code) (raw : Program model.source.code)
  (rival : Opponent model.source.code)

private abbrev controls := Residual.scheduleAt point.source point.cut (schedule point fallback raw)
private abbrev input : Input model.source.code := ⟨controller point fallback raw rival,point.entry.budget⟩
private abbrev seed := Residual.seed point.source point.entry point.cut
private abbrev state (n : Nat) := Residual.run model.source.code (controls model point fallback raw)
  (input model point fallback raw rival) (seed model point) n
private abbrev items (n : Nat) := model.source.code.law.rawItems (state model point fallback raw rival n).current
  (word model.source.code (controls model point fallback raw n) (input model point fallback raw rival)
    (state model point fallback raw rival n))

private theorem actual_items (n : Nat) :
    ((source point fallback raw rival).actualExecution (Cut.start point.source point.cut-1+n)).interpreted.items =
      items model point fallback raw rival n := by
  let target := source point fallback raw rival
  have current := target.feedback_body_reads_the_actual_local_current (entry point fallback raw rival) rfl rfl (point.cut+n)
  rw [Future.the_whole_future_run_is_the_actual_state] at current
  have submitted := Future.future_word_is_actually_submitted point.source point.entry point.cut
    (controller point fallback raw rival) (schedule point fallback raw) rfl n
  rw [show Cut.start point.source point.cut-1+n = point.source.history.length+1+(point.cut+n) from by
    dsimp only [Cut.start];omega]
  have exactItems := congrArg (fun execution => execution.items)
    (target.actualExecution (point.source.history.length+1+(point.cut+n))).interpreted_exact
  change (target.actualExecution _).interpreted.items = model.source.code.law.rawItems _ _ at exactItems
  rw [exactItems,submitted,← current]

private def debit (count : Nat) (axis : Party × Good) : ℚ :=
  ((List.range count).map fun n => model.source.code.law.totalDebit (items model point fallback raw rival n) axis.1 axis.2).sum
private def credit (count : Nat) (axis : Party × Good) : ℚ :=
  ((List.range count).map fun n => model.source.code.law.totalCredit (items model point fallback raw rival n) axis.1 axis.2).sum

private theorem debit_exact (axis : Party × Good) :
    (Finite.actualEvaluation model point fallback raw rival).value (.material (.debit axis.1 axis.2)) =
      debit model point fallback raw rival (remaining point) axis := by
  change ((List.range (remaining point)).map _).sum = _
  unfold debit
  congr 1
  apply List.map_congr_left
  intro n _
  change model.source.code.law.totalDebit
    ((source point fallback raw rival).actualExecution (Cut.start point.source point.cut-1+n)).interpreted.items axis.1 axis.2 = _
  rw [actual_items]

private theorem credit_exact (axis : Party × Good) :
    -(Finite.actualEvaluation model point fallback raw rival).value (.material (.credit axis.1 axis.2)) =
      credit model point fallback raw rival (remaining point) axis := by
  change -(-((List.range (remaining point)).map _).sum) = _
  rw [neg_neg]
  unfold credit
  congr 1
  apply List.map_congr_left
  intro n _
  change model.source.code.law.totalCredit
    ((source point fallback raw rival).actualExecution (Cut.start point.source point.cut-1+n)).interpreted.items axis.1 axis.2 = _
  rw [actual_items]

private theorem run_balance (count : Nat) (axis : Party × Good) :
    (state model point fallback raw rival count).current.stock axis.1 axis.2 +
      debit model point fallback raw rival count axis = (seed model point).current.stock axis.1 axis.2 +
      credit model point fallback raw rival count axis := by
  induction count with
  | zero => simp [debit,credit,Residual.run]
  | succ count ih =>
    have next := model.source.code.law.actual_next_material_balance
      (state model point fallback raw rival count).current
      (word model.source.code (controls model point fallback raw count) (input model point fallback raw rival)
        (state model point fallback raw rival count)) axis.1 axis.2
    change _ + _ = _ + _
    simp only [debit,credit,List.range_succ,List.map_append,List.sum_append,List.map_singleton,List.sum_singleton] at *
    change (model.source.code.law.next _ _).stock _ _ + _ = _ + _
    linarith

theorem the_complete_actual_inventory_balances_every_material_coordinate (axis : Party × Good) :
    (Finite.actualEvaluation model point fallback raw rival).value (.material (.inventory axis.1 axis.2)) =
      -((seed model point).current.stock axis.1 axis.2) +
        (Finite.actualEvaluation model point fallback raw rival).value (.material (.debit axis.1 axis.2)) +
        (Finite.actualEvaluation model point fallback raw rival).value (.material (.credit axis.1 axis.2)) := by
  have balance := run_balance model point fallback raw rival (remaining point) axis
  rw [← debit_exact,← credit_exact] at balance
  change -((source point fallback raw rival).currentAt (Cut.finish point.source point.entry point.cut)).stock axis.1 axis.2 = _
  rw [show Cut.finish point.source point.entry point.cut = point.source.history.length+2+
    (point.cut+remaining point) from by dsimp only [Cut.finish,Cut.start,remaining];omega]
  rw [(source point fallback raw rival).feedback_current_is_actual (entry point fallback raw rival) rfl rfl,
    Future.the_whole_future_run_is_the_actual_state]
  linarith

variable (domain : List (Cursor model.source.code))

theorem every_complete_actual_raw_run_respects_the_source_envelope
    (checked : sourceCheck model.source.code (Dynamic.menu model domain))
    (world : Replanning.Point model domain)
    (supported : Open.Supported model domain fallback raw)
    (output : Party × Good) :
    -(Finite.actualEvaluation model world.val fallback raw rival).value (.material (.credit output.1 output.2)) ≤
      applyMatrix model.source.code (Dynamic.menu model domain)
        (fun axis => (Finite.actualEvaluation model world.val fallback raw rival).value (.material (.debit axis.1 axis.2))) output := by
  rw [credit_exact]
  have bound := Whole.Complete.each_remaining_horizon_is_generated domain world.val world.property
  have support := supported_schedule world.val fallback raw (fun n inside => supported n (inside.trans_le bound))
  let words := controls model world.val fallback raw
  let entry := input model world.val fallback raw rival
  let initial := seed model world.val
  have original (n : Nat) (inside : n < remaining world.val) :
      ∀ item ∈ items model world.val fallback raw rival n,item.request ∈ Dynamic.requests model.source.code := by
    intro item member
    apply Dynamic.every_actual_submitted_word_uses_primitive_source_requests model.source.code (words n)
      (support n inside) entry (state model world.val fallback raw rival n)
    rw [← model.source.code.law.inventory_requests_exact (state model world.val fallback raw rival n).current 0
      (word model.source.code (words n) entry (state model world.val fallback raw rival n))]
    exact List.mem_map.mpr ⟨item,member,rfl⟩
  have reachable (n : Nat) (inside : n < remaining world.val) :
      ∀ item ∈ items model world.val fallback raw rival n,item.before.technology ∈ Dynamic.menu model domain := by
    have known := Dynamic.every_actual_raw_run_stays_in_the_source_technology_menu model.source.code
      (Dynamic.initialTechnologies model domain) words entry initial
      (Dynamic.every_public_seed_has_its_own_original_technology model domain world) (remaining world.val) support n inside.le
    exact (Dynamic.each_executed_source_word_keeps_all_intermediate_technologies model.source.code
      (Dynamic.initialTechnologies model domain) _ known _
      (Dynamic.every_actual_submitted_word_uses_primitive_source_requests model.source.code (words n)
        (support n inside) entry (state model world.val fallback raw rival n)) 0).2
  have bounded := List.sum_le_sum (l := List.range (remaining world.val))
    (f := fun n => model.source.code.law.totalCredit (items model world.val fallback raw rival n) output.1 output.2)
    (g := fun n => applyMatrix model.source.code (Dynamic.menu model domain)
      (fun axis => model.source.code.law.totalDebit (items model world.val fallback raw rival n) axis.1 axis.2) output)
    (fun n inside => each_original_word_respects_the_source_envelope model.source.code _ checked _
      (original n (List.mem_range.mp inside)) (reachable n (List.mem_range.mp inside)) output
      (List.mem_flatMap.mpr ⟨output.1,model.source.code.parties_cover _,
        List.mem_map.mpr ⟨output.2,model.source.code.goods_cover _,rfl⟩⟩))
  rw [matrix_sum] at bounded
  simpa only [credit,debit_exact,debit,applyMatrix] using bounded

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Flow
