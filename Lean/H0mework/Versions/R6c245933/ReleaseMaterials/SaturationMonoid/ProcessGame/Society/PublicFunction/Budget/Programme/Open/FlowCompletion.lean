import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Flow.Actual
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Flow.Order
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Open.Completion

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Open.FlowCompletion

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code)) (fallback : Rule model.source.code)
  (reference : Program model.source.code)

def settled (row : Evaluation model.source.code) (axis : EconomicAxis model.source.code) : Prop :=
  match axis with
  | .material .admissibility | .unpaid _ _ | .service _ => row.value axis = 0
  | _ => True

instance (row : Evaluation model.source.code) (axis : EconomicAxis model.source.code) : Decidable (settled model row axis) := by
  cases axis with
  | material metric => cases metric <;> unfold settled <;> infer_instance
  | unpaid => unfold settled;infer_instance
  | service => unfold settled;infer_instance

def atFrontier (world : Cursor model.source.code) (row : Evaluation model.source.code) : Prop :=
  Completion.grantDueOnly row.native ∧
    Synthesis.accepts model.source.code (economicAxes world.source world.cut) row row ∧
    (∀ axis ∈ economicAxes world.source world.cut,settled model row axis) ∧
    ∀ axis ∈ Dynamic.Cost.axes model.source.code,
      -row.value (.material (.credit axis.1 axis.2)) = Flow.applyMatrix model.source.code (Dynamic.menu model domain)
        (fun input => row.value (.material (.debit input.1 input.2))) axis ∧
      (row.value (.material (.debit axis.1 axis.2)) = 0 ∨
        ∃ output ∈ Dynamic.Cost.axes model.source.code,0 < Flow.matrix model.source.code (Dynamic.menu model domain) output axis)

instance (world : Cursor model.source.code) (row : Evaluation model.source.code) :
    Decidable (atFrontier model domain world row) := by unfold atFrontier;infer_instance

def finiteCheck : Prop := ∀ world ∈ Replanning.points model domain,
  ∀ table ∈ Finite.tables world.val fallback [reference],
    atFrontier model domain world.val (Finite.tableEvaluation model world.val fallback [reference] reference table)

instance : Decidable (finiteCheck model domain fallback reference) := by unfold finiteCheck;infer_instance

/-- A finite check of original recipes and reference rows, with no bound on raw presentation length. -/
def verify : Bool := decide (Flow.sourceCheck model.source.code (Dynamic.menu model domain) ∧
  Support.SourceSupported model fallback domain reference ∧ finiteCheck model domain fallback reference)

private theorem axes_cover (axis : Party × Good) : axis ∈ Dynamic.Cost.axes model.source.code :=
  List.mem_flatMap.mpr ⟨axis.1,model.source.code.parties_cover _,
    List.mem_map.mpr ⟨axis.2,model.source.code.goods_cover _,rfl⟩⟩

private theorem credit_axis (world : Cursor model.source.code) (axis : Party × Good) :
    EconomicAxis.material (.credit axis.1 axis.2) ∈ economicAxes world.source world.cut := by
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_map.mpr
  refine ⟨.credit axis.1 axis.2,?_,rfl⟩
  apply List.mem_append_left
  exact List.mem_flatMap.mpr ⟨axis.1,model.source.code.parties_cover _,
    List.mem_flatMap.mpr ⟨axis.2,model.source.code.goods_cover _,by simp⟩⟩

variable (checked : verify model domain fallback reference = true)

include checked in
theorem every_original_row_attains_the_generated_source_envelope
    (world : Replanning.Point model domain) (rival : Opponent model.source.code) :
    atFrontier model domain world.val (Finite.actualEvaluation model world.val fallback reference rival) := by
  have all := (of_decide_eq_true checked).2.2
  have row := all world (Replanning.every_point_is_source_generated model domain world)
    (Finite.restrict world.val fallback [reference] rival) (Residual.restriction_is_generated _ _ _ rival)
  rw [Finite.one_external_restriction_preserves_the_complete_evaluation model world.val fallback [reference]
    reference List.mem_cons_self rival] at row
  exact row

include checked in
theorem the_attained_source_envelope_excludes_every_supported_raw_improvement
    (raw : Program model.source.code) (supported : Open.Supported model domain fallback raw)
    (accepted : Bounds.Accepted model domain fallback reference raw) :
    ¬ Open.improves model domain fallback reference raw := by
  intro better
  apply better.2
  intro world rival
  have ideal := every_original_row_attains_the_generated_source_envelope model domain fallback reference checked world rival
  let prior := Finite.actualEvaluation model world.val fallback reference rival
  let next := Finite.actualEvaluation model world.val fallback raw rival
  have same := Flow.an_attained_source_envelope_forces_every_material_input_and_output model.source.code (Dynamic.menu model domain)
    (fun axis => prior.value (.material (.debit axis.1 axis.2)))
    (fun axis => next.value (.material (.debit axis.1 axis.2)))
    (fun axis => -prior.value (.material (.credit axis.1 axis.2)))
    (fun axis => -next.value (.material (.credit axis.1 axis.2)))
    (fun axis => Completion.every_actual_raw_debit_is_nonnegative model world.val fallback raw rival axis.1 axis.2)
    (fun axis => (accepted world rival).2.2.2.2 _ (Bounds.every_material_debit_axis_is_original model world.val axis))
    (fun axis => neg_le_neg ((accepted world rival).2.2.2.2 _ (credit_axis model world.val axis)))
    (Flow.every_complete_actual_raw_run_respects_the_source_envelope model fallback raw rival domain
      (of_decide_eq_true checked).1 world supported)
    (fun axis => (ideal.2.2.2 axis (axes_cover model axis)).1)
    (fun axis => (ideal.2.2.2 axis (axes_cover model axis)).2)
  have sameDebit (party : Party) (good : Good) : next.value (.material (.debit party good)) = prior.value (.material (.debit party good)) :=
    congrFun same.1 (party,good)
  have sameCredit (party : Party) (good : Good) : next.value (.material (.credit party good)) = prior.value (.material (.credit party good)) :=
    neg_inj.mp (congrFun same.2 (party,good))
  refine ⟨Completion.admitted_grants_generate_the_reverse_due_order _ _ ideal.1 (accepted world rival).2.2.2.1.1,?_⟩
  intro axis inside
  cases axis with
  | material metric =>
    cases metric with
    | debit party good => exact (sameDebit party good).symm.le
    | credit party good => exact (sameCredit party good).symm.le
    | inventory party good =>
      rw [Flow.the_complete_actual_inventory_balances_every_material_coordinate model world.val fallback reference rival (party,good),
        Flow.the_complete_actual_inventory_balances_every_material_coordinate model world.val fallback raw rival (party,good)]
      rw [sameDebit party good,sameCredit party good]
    | clock => exact le_of_eq (congrArg (fun profile => profile.control.clock) (accepted world rival).2.2.1).symm
    | admissibility =>
      rw [ideal.2.2.1 _ inside]
      change 0 ≤ (if _ then (0 : ℚ) else 1)
      split <;> norm_num
  | unpaid index holder =>
    rw [ideal.2.2.1 _ inside]
    exact Completion.every_original_unpaid_coordinate_is_nonnegative model world.val fallback raw rival index holder
  | service index =>
    rw [ideal.2.2.1 _ inside]
    exact Nat.cast_nonneg _

structure Receipt where
  source_check : Bool
  generated : source_check = verify model domain fallback reference
  complete : source_check = true

def inspect : Option (Receipt model domain fallback reference) :=
  if checked : verify model domain fallback reference = true then some ⟨_,rfl,checked⟩ else none

theorem every_receipt_has_independent_review (receipt : Receipt model domain fallback reference) :
    verify model domain fallback reference = true := receipt.generated ▸ receipt.complete

theorem every_receipt_covers_the_entire_raw_domain (receipt : Receipt model domain fallback reference) :
    Open.Supported model domain fallback reference ∧ Bounds.Accepted model domain fallback reference reference ∧
      ∀ raw : Program model.source.code,Open.Supported model domain fallback raw →
        Bounds.Accepted model domain fallback reference raw → ¬ Open.improves model domain fallback reference raw := by
  have checked := every_receipt_has_independent_review model domain fallback reference receipt
  exact ⟨(Support.support_exact model fallback domain reference).mp (of_decide_eq_true checked).2.1,
    fun world rival => (every_original_row_attains_the_generated_source_envelope model domain fallback reference checked world rival).2.1,
    the_attained_source_envelope_excludes_every_supported_raw_improvement model domain fallback reference checked⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Open.FlowCompletion
