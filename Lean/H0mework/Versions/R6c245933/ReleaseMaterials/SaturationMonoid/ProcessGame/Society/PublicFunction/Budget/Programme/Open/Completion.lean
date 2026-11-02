import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Open.Completion.Bounds
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Open.Completion.Native
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Open.Support

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Open.Completion

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

def lower (world : Cursor model.source.code) (prior : Evaluation model.source.code) : EconomicAxis model.source.code → ℚ
  | .material (.inventory party good) => -((Residual.seed world.source world.entry world.cut).current.stock party good)
  | .material .clock => prior.value (.material .clock)
  | _ => 0

def atLower (world : Cursor model.source.code) (prior : Evaluation model.source.code) : Prop :=
  grantDueOnly prior.native ∧
  Synthesis.accepts model.source.code (economicAxes world.source world.cut) prior prior ∧
  ∀ axis ∈ economicAxes world.source world.cut,prior.value axis = lower model world prior axis

instance (world : Cursor model.source.code) (prior : Evaluation model.source.code) : Decidable (atLower model world prior) := by
  unfold atLower
  infer_instance

/-- Only primitive source fields and the original finite reference rows are checked. -/
def finiteCheck : Prop := ∀ world ∈ Replanning.points model domain,
  ∀ table ∈ Finite.tables world.val fallback [reference],
    atLower model world.val (Finite.tableEvaluation model world.val fallback [reference] reference table)

instance : Decidable (finiteCheck model domain fallback reference) := by unfold finiteCheck;infer_instance

def verify : Bool := noSupply model.source.code &&
  decide (Support.SourceSupported model fallback domain reference ∧ finiteCheck model domain fallback reference)

variable (checked : verify model domain fallback reference = true)

include checked in
theorem every_reference_row_attains_its_original_source_bounds
    (world : Replanning.Point model domain) (rival : Opponent model.source.code) :
    atLower model world.val (Finite.actualEvaluation model world.val fallback reference rival) := by
  have all := (of_decide_eq_true (Bool.and_eq_true_iff.mp checked).2).2
  have exactRow := all world (Replanning.every_point_is_source_generated model domain world)
    (Finite.restrict world.val fallback [reference] rival) (Residual.restriction_is_generated _ _ _ rival)
  rw [Finite.one_external_restriction_preserves_the_complete_evaluation model world.val fallback [reference]
    reference List.mem_cons_self rival] at exactRow
  exact exactRow

include checked in
theorem the_checked_original_programme_is_fully_accepted : Bounds.Accepted model domain fallback reference reference := by
  intro world rival
  exact (every_reference_row_attains_its_original_source_bounds model domain fallback reference checked world rival).2.1

include checked in
theorem the_actual_source_excludes_every_supported_raw_improvement
    (raw : Program model.source.code) (supported : Open.Supported model domain fallback raw)
    (accepted : Bounds.Accepted model domain fallback reference raw) :
    ¬ Open.improves model domain fallback reference raw := by
  intro better
  apply better.2
  intro world rival
  have ideal := every_reference_row_attains_its_original_source_bounds model domain fallback reference checked world rival
  have origin := (Bool.and_eq_true_iff.mp checked).1
  have localSupport : ∀ n < Cut.horizon world.val.source world.val.entry world.val.cut,
      (stage model.source.code fallback raw n).supported := fun n inside =>
    supported n (inside.trans_le (Whole.Complete.each_remaining_horizon_is_generated domain world.val world.property))
  refine ⟨?_,?_⟩
  · exact admitted_grants_generate_the_reverse_due_order _ _ ideal.1 (accepted world rival).2.2.2.1.1
  · intro axis inside
    rw [ideal.2.2 axis inside]
    cases axis with
    | material metric =>
      cases metric with
      | debit party good => exact every_actual_raw_debit_is_nonnegative model world.val fallback raw rival party good
      | credit party good =>
        rw [the_complete_raw_credit_is_zero model world.val fallback raw rival localSupport origin party good]
        exact le_rfl
      | inventory party good => exact the_complete_raw_inventory_has_its_actual_source_bound model world.val fallback raw rival localSupport origin party good
      | clock =>
        exact le_of_eq (congrArg (fun profile => profile.control.clock) (accepted world rival).2.2.1).symm
      | admissibility => change 0 ≤ (if _ then (0 : ℚ) else 1);split <;> norm_num
    | unpaid index holder => exact every_original_unpaid_coordinate_is_nonnegative model world.val fallback raw rival index holder
    | service index => change 0 ≤ (_ : ℚ);exact Nat.cast_nonneg _

structure Receipt where
  source_check : Bool
  generated : source_check = verify model domain fallback reference
  complete : source_check = true

/-- A receipt is generated only by the finite source test; no raw maximality witness is an input. -/
def inspect : Option (Receipt model domain fallback reference) :=
  if checked : verify model domain fallback reference = true then some ⟨_,rfl,checked⟩ else none

theorem a_generated_completion_receipt_has_independent_review (receipt : Receipt model domain fallback reference) :
    verify model domain fallback reference = true := receipt.generated ▸ receipt.complete

theorem a_generated_completion_receipt_certifies_the_entire_raw_domain (receipt : Receipt model domain fallback reference) :
    Open.Supported model domain fallback reference ∧ Bounds.Accepted model domain fallback reference reference ∧
      ∀ raw : Program model.source.code,Open.Supported model domain fallback raw →
        Bounds.Accepted model domain fallback reference raw → ¬ Open.improves model domain fallback reference raw := by
  have valid := a_generated_completion_receipt_has_independent_review model domain fallback reference receipt
  exact ⟨(Support.support_exact model fallback domain reference).mp
      (of_decide_eq_true (Bool.and_eq_true_iff.mp valid).2).1,
    the_checked_original_programme_is_fully_accepted model domain fallback reference valid,
    the_actual_source_excludes_every_supported_raw_improvement model domain fallback reference valid⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Open.Completion
