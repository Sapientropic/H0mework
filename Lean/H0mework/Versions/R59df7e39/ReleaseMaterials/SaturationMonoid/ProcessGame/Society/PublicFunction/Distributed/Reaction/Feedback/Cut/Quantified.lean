import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Cut.Compiler
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Cut.Transport

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Cut

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (source : Machine Party Good Port Technology Instrument) (input : Input source.code) (cut : Nat)

def AgainstEveryOpponent (new old : Term source input cut) : Prop :=
  ∀ rival : Opponent source.code,
    profile source input cut rival new = profile source input cut rival old ∧
      (∀ metric ∈ Settlement.materials source.code, material source input cut rival new metric ≤ material source input cut rival old metric) ∧
      (∀ index < originalSlots source cut, ∀ holder : Party,
        remaining source input cut rival new index holder ≤ remaining source input cut rival old index holder) ∧
      ∀ index, serviceTime source input cut rival new index ≤ serviceTime source input cut rival old index

def StrictAgainstEveryOpponent (old new : Term source input cut) : Prop :=
  AgainstEveryOpponent source input cut new old ∧ ¬ AgainstEveryOpponent source input cut old new

variable (active : source.feedback? = some input) (empty : source.continuation = [])

include active empty in
theorem finite_comparison_iff_every_future_opponent (new old : Term source input cut) :
    NonRegression source input cut new old ↔ AgainstEveryOpponent source input cut new old := by
  rw [comparison_iff]
  constructor
  · rintro ⟨values, profiles⟩ rival
    let table := Residual.restrict source.code (Residual.seed source input cut) (Residual.schedules source input cut) rival
    have generated := Residual.restriction_is_generated source.code (Residual.seed source input cut) (Residual.schedules source input cut) rival
    have holding (term : Term source input cut) := joint_holdings source input cut rival term active empty
    have receipt (term : Term source input cut) (index : Nat) (holder : Party) :
        remaining source input cut (finiteRival source input cut rival) term index holder =
          remaining source input cut rival term index holder :=
      congrArg (fun matrix => (Settlement.holdingAt matrix index (source.code.parties.idxOf holder)).1) (holding term)
    have service (term : Term source input cut) (index : Fin source.code.task.slots.length) :
        serviceTime source input cut (finiteRival source input cut rival) term index = serviceTime source input cut rival term index :=
      congrArg (fun value : Option Nat => (value.getD (finish source input cut) : ℚ))
        (joint_first_service source input cut rival term active empty (finish source input cut - 1) (by dsimp only [finish, start]; omega) index)
    refine ⟨(joint_profile source input cut rival new active empty).symm.trans
      ((profiles table generated).trans (joint_profile source input cut rival old active empty)), ?_, ?_, ?_⟩
    · intro metric present
      have checked := values (.material table metric) (material_axis_is_generated source input cut table generated metric present)
      change material source input cut (finiteRival source input cut rival) new metric ≤
        material source input cut (finiteRival source input cut rival) old metric at checked
      rw [joint_material source input cut rival new active empty, joint_material source input cut rival old active empty] at checked
      exact checked
    · intro index inside holder
      have checked := values (.unpaid table index holder) (unpaid_axis_is_generated source input cut table generated index inside holder)
      change remaining source input cut (finiteRival source input cut rival) new index holder ≤
        remaining source input cut (finiteRival source input cut rival) old index holder at checked
      rw [receipt new, receipt old] at checked
      exact checked
    · intro index
      have checked := values (.service table index) (service_axis_is_generated source input cut table generated index)
      change serviceTime source input cut (finiteRival source input cut rival) new index ≤
        serviceTime source input cut (finiteRival source input cut rival) old index at checked
      rw [service new, service old] at checked
      exact checked
  · intro all
    refine ⟨?_, fun table _ => (all (opponent source input cut table)).1⟩
    intro axis inside
    obtain ⟨table, generated, inner⟩ := List.mem_flatMap.mp inside
    rcases List.mem_append.mp inner with materialOrService | unpaid
    · rcases List.mem_append.mp materialOrService with material | service
      · obtain ⟨metric, present, rfl⟩ := List.mem_map.mp material
        exact (all (opponent source input cut table)).2.1 metric present
      · obtain ⟨index, _, rfl⟩ := List.mem_map.mp service
        exact (all (opponent source input cut table)).2.2.2 index
    · obtain ⟨index, indexMember, row⟩ := List.mem_flatMap.mp unpaid
      obtain ⟨holder, _, rfl⟩ := List.mem_map.mp row
      exact (all (opponent source input cut table)).2.2.1 index (List.mem_range.mp indexMember) holder

include active empty in
theorem finite_strictness_iff_every_future_opponent (old new : Term source input cut) :
    Better source input cut old new ↔ StrictAgainstEveryOpponent source input cut old new :=
  and_congr (finite_comparison_iff_every_future_opponent source input cut active empty new old)
    (not_congr (finite_comparison_iff_every_future_opponent source input cut active empty old new))

def FeasibleAgainstEveryOpponent (term : Term source input cut) : Prop :=
  ∀ rival : Opponent source.code,
    (Residual.run source.code (Residual.scheduleAt source cut term.val) ⟨rival, input.budget⟩
      (Residual.seed source input cut) (horizon source input cut)).frame.localLegal = true ∧
    ∀ index : Fin source.code.task.slots.length,
      (Identity.firstService (machine source input cut rival term) (finish source input cut - 1) index).isSome = true

include active empty in
theorem feasibility_iff_every_future_opponent (term : Term source input cut) :
    Feasible source input cut term ↔ FeasibleAgainstEveryOpponent source input cut term := by
  constructor
  · intro feasible rival
    let table := Residual.restrict source.code (Residual.seed source input cut) (Residual.schedules source input cut) rival
    have generated := Residual.restriction_is_generated source.code (Residual.seed source input cut) (Residual.schedules source input cut) rival
    have checked := feasible table generated
    have same := Residual.one_restriction_preserves_the_whole_remaining_run source.code (Residual.seed source input cut)
      (Residual.schedules source input cut) _ (List.mem_map.mpr ⟨term.val, term.property, rfl⟩) ⟨rival, input.budget⟩
      (horizon source input cut) (Nat.le_refl _)
    refine ⟨(congrArg (fun state : State source.code => state.frame.localLegal) same).symm.trans checked.1, ?_⟩
    intro index
    exact (congrArg Option.isSome (joint_first_service source input cut rival term active empty
      (finish source input cut - 1) (by dsimp only [finish, start]; omega) index)).symm.trans (checked.2 index)
  · intro all table _
    exact all (opponent source input cut table)

include active empty in
theorem selected_protects_every_actual_future_opponent (reference : Term source input cut)
    (choice : Selection source input cut reference) : AgainstEveryOpponent source input cut choice.policy.term reference :=
  (finite_comparison_iff_every_future_opponent source input cut active empty _ _).mp choice.policy.no_regression

include active empty in
theorem selected_protects_every_original_holders_actual_receipts (reference : Term source input cut)
    (choice : Selection source input cut reference) (rival : Opponent source.code) (index : Nat)
    (inside : index < originalSlots source cut) (holder : Party) :
    received source input cut rival reference index holder ≤ received source input cut rival choice.policy.term index holder := by
  have all := selected_protects_every_actual_future_opponent source input cut active empty reference choice rival
  exact same_rights_and_less_owed_give_more_actual_receipts source input cut rival _ _ all.1 index holder (all.2.2.1 index inside holder)


include active empty in
theorem selected_has_no_feasible_dominator_under_all_future_opponents (reference : Term source input cut)
    (choice : Selection source input cut reference) (other : Term source input cut)
    (feasible : FeasibleAgainstEveryOpponent source input cut other) :
    ¬ StrictAgainstEveryOpponent source input cut choice.policy.term other := by
  intro improves
  exact selected_has_no_feasible_dominator source input cut reference choice other
    ((feasibility_iff_every_future_opponent source input cut active empty other).mpr feasible)
    ((finite_strictness_iff_every_future_opponent source input cut active empty _ _).mpr improves)

include active empty in
theorem every_actual_future_improvement_is_realized (reference : Term source input cut)
    (choice : Selection source input cut reference)
    (available : ∃ term : Term source input cut, FeasibleAgainstEveryOpponent source input cut term ∧
      StrictAgainstEveryOpponent source input cut reference term) :
    StrictAgainstEveryOpponent source input cut reference choice.policy.term := by
  apply (finite_strictness_iff_every_future_opponent source input cut active empty _ _).mp
  apply every_available_improvement_is_realized source input cut reference choice
  obtain ⟨term, feasible, improves⟩ := available
  exact ⟨term, (feasibility_iff_every_future_opponent source input cut active empty _).mpr feasible,
    (finite_strictness_iff_every_future_opponent source input cut active empty _ _).mpr improves⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Cut
