import H0mework.Fock.CopyGraph.GrowthBalance
import H0mework.Probability.Recovery.Collision

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphGrowth

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability SourceUniformFibreVariance
open SourceHistoryGrowth SourceOwnedObservationHistory
open SourceCopyProgram (Index)
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

omit [MeasurableSingletonClass Observed] in
theorem old_exact (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (value : Space (observed (historyPMF depth) (oldRead depth read))) :
    oldResidual depth index read (oldAction depth index read value) = 0 := by
  have source := SourceConditionalGraphDecoder.reconstruction depth depth index (oldRead depth read)
    (oldAction depth index read value)
  rw [SourceConditionalGraphDecoder.decode_action] at source
  exact add_left_cancel (source.trans (add_zero _).symm)

theorem tagged_exact (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (value : Space (observed (historyPMF depth) (oldRead depth read))) :
    taggedResidual depth index read (oldAction depth index read value) = 0 := by
  rw [← retained_action depth index read value]
  have source := SourceConditionalGraphDecoder.reconstruction (depth + 1) (depth + 1)
    (FamilyModel.Fock.oldIndex depth index) (taggedRead depth read)
    (taggedAction depth index read (retainedLift depth read value))
  rw [SourceConditionalGraphDecoder.decode_action] at source
  exact add_left_cancel (source.trans (add_zero _).symm)

theorem birth_on_old (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (value : Space (observed (historyPMF depth) (oldRead depth read))) :
    birthGain depth index read (oldAction depth index read value) = 0 := by
  have source := birth_residual depth index read (oldAction depth index read value)
  rw [old_exact, tagged_exact, zero_add] at source
  exact source.symm

theorem old_target_loss (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (value : Space (observed (historyPMF depth) (oldRead depth read))) :
    newResidual depth index read (oldAction depth index read value) =
      forgettingLoss depth index read (oldAction depth index read value) := by
  rw [forgetting_residual, tagged_exact, zero_add]

theorem collision_retained_lower (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (actor : Fin (depth + 1)) (collision : read actor.val = read (depth + 1))
    (value : Space (observed (historyPMF depth) (oldRead depth read))) :
    (historyPMF (depth + 1) (includeActor (Nat.le_succ depth) actor)).toReal *
        ‖(Real.sqrt (fraction depth (depth + 1)))⁻¹ • value (oldRead depth read actor)‖ ^ 2 / 2 ≤
      ‖newResidual depth index read (oldAction depth index read value)‖ ^ 2 := by
  let lifted := normalizedInclusion (Nat.le_succ depth) (pullback (historyPMF depth) (oldRead depth read) value)
  have distinct : includeActor (Nat.le_succ depth) actor ≠ Fin.last (depth + 1) := by
    intro same
    have values := congrArg (fun current : Fin (depth + 2) => current.val) same
    change actor.val = depth + 1 at values
    have inside := actor.isLt
    omega
  have same : newRead depth read (includeActor (Nat.le_succ depth) actor) =
      newRead depth read (Fin.last (depth + 1)) := collision
  have equalWeight : (historyPMF (depth + 1) (includeActor (Nat.le_succ depth) actor)).toReal =
      (historyPMF (depth + 1) (Fin.last (depth + 1))).toReal := by rw [source_weight, source_weight]
  have paid := equal_weight_pair_lower_bound (historyPMF (depth + 1)) (newRead depth read)
    (fun current => lifted current) (optimalDecoder (historyPMF (depth + 1)) (newRead depth read) (fun current => lifted current))
    (includeActor (Nat.le_succ depth) actor) (Fin.last (depth + 1)) distinct same equalWeight
  have restored : taskValue (historyPMF (depth + 1)) (fun current => lifted current) = lifted :=
    MeasureTheory.Lp.toLp_coeFn lifted (task_memLp (historyPMF (depth + 1)) _)
  rw [optimal_attains, restored] at paid
  dsimp only [lifted] at paid
  rw [normalized_prior, normalized_new, sub_zero, pullback_at _ _ _ actor (source_positive depth actor)] at paid
  have retained := SourceConditionalGraphDecoder.retained_lower (depth + 1) (depth + 1)
    (FamilyModel.Fock.oldIndex depth index) (newRead depth read) lifted
  change _ ≤ ‖newResidual depth index read
    (SourceConditionalGraph.copyRead (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) lifted)‖ ^ 2 at retained
  dsimp only [lifted] at retained
  rw [tick_copy_read, ← SourceConditionalGraphDecoder.action_source] at retained
  exact paid.trans retained

theorem collision_cost (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (actor : Fin (depth + 1)) (collision : read actor.val = read (depth + 1))
    (value : Space (observed (historyPMF depth) (oldRead depth read))) :
    ‖value (oldRead depth read actor)‖ ^ 2 / (2 * (depth + 1 : ℝ)) ≤
      ‖newResidual depth index read (oldAction depth index read value)‖ ^ 2 := by
  have paid := collision_retained_lower depth index read actor collision value
  rw [source_weight, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr (fraction_pos depth (depth + 1)))),
    mul_pow, inv_pow, Real.sq_sqrt (fraction_pos depth (depth + 1)).le, fraction] at paid
  simp only [Nat.cast_add, Nat.cast_one] at paid
  convert paid using 1
  field_simp

end
end SourceGraphGrowth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
