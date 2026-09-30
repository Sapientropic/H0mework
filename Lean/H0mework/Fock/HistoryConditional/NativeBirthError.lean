import H0mework.Fock.HistoryConditional.NativeBirthUpdate

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalNativeBirth

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceConditionalModel (Actors nextRead positive)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
variable {Key : Type*} [DecidableEq Key]

def total (runtime : LivingRuntimeState process) (read : Nat → Key) : ℝ :=
  ∑ actor : Actors runtime, ‖SourceConditionalInventory.values (inventoryBound runtime) actor -
    SourceConditionalNativePosterior.decoder runtime read (read actor.val)‖ ^ 2

theorem total_decomposition (runtime : LivingRuntimeState process) (read : Nat → Key)
    (guess : Key → SourceJointClockGraph.Carrier) :
    (∑ actor : Actors runtime, ‖SourceConditionalInventory.values (inventoryBound runtime) actor - guess (read actor.val)‖ ^ 2) =
      total runtime read + ∑ actor : Actors runtime,
        ‖SourceConditionalNativePosterior.decoder runtime read (read actor.val) - guess (read actor.val)‖ ^ 2 := by
  let source := historyPMF (inventoryBound runtime)
  let query : Actors runtime → Key := fun actor => read actor.val
  let values : Actors runtime → SourceJointClockGraph.Carrier :=
    fun actor => SourceConditionalVector.realizeModel runtime (nextRead runtime actor)
  have means (actor : Actors runtime) :
      SourceVectorMoment.mean (SourceConditionalHistory.conditional source query (query actor)
        (SourceWeightedRecovery.observed_supported source query actor (positive runtime actor))) values =
          SourceConditionalNativePosterior.decoder runtime read (query actor) :=
    (SourceConditionalNativePosterior.decoder_mean runtime read (read actor.val)
      (SourceWeightedRecovery.observed_supported source query actor (positive runtime actor))).symm
  have fine := SourceVectorMoment.conditional_error source query (positive runtime) values
    (SourceConditionalNativePosterior.decoder runtime read)
  simp only [means, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, Finset.sum_const_zero, add_zero] at fine
  have coarse := SourceVectorMoment.conditional_error source query (positive runtime) values guess
  rw [← fine] at coarse
  simp only [means] at coarse
  dsimp only [source, query, values] at coarse
  have paid := congrArg (fun value : ℝ => ((inventoryBound runtime + 1 : Nat) : ℝ) * value) coarse
  simp only [mul_add, SourceConditionalInventory.sum_count, ← SourceConditionalInventory.values_original] at paid
  dsimp only [total]
  with_reducible exact paid

omit [DecidableEq Key] in
theorem total_append (runtime : LivingRuntimeState process) (read : Nat → Key)
    (guess : Key → SourceJointClockGraph.Carrier) :
    (∑ actor : Actors runtime.tick.next,
      ‖SourceConditionalInventory.values (inventoryBound runtime.tick.next) actor - guess (read actor.val)‖ ^ 2) =
    (∑ actor : Actors runtime,
      ‖SourceConditionalInventory.values (inventoryBound runtime) actor - guess (read actor.val)‖ ^ 2) +
      ‖SourceConditionalInventory.born (inventoryBound runtime) - guess (read (inventoryBound runtime + 1))‖ ^ 2 := by
  change (∑ actor : Fin (inventoryBound runtime.tick.next + 1),
    ‖SourceConditionalInventory.values (inventoryBound runtime.tick.next) actor - guess (read actor.val)‖ ^ 2) = _
  rw [SourceActualImageStep.next_bound, Fin.sum_univ_castSucc]
  rfl

theorem next_bias (runtime : LivingRuntimeState process) (read : Nat → Key) :
    (∑ actor : Actors runtime, ‖SourceConditionalNativePosterior.decoder runtime read (read actor.val) -
        SourceConditionalNativePosterior.decoder runtime.tick.next read (read actor.val)‖ ^ 2) =
      (SourceConditionalNativeObservers.generate read (inventoryBound runtime) (read (inventoryBound runtime + 1))).1 *
        ‖SourceConditionalNativePosterior.decoder runtime read (read (inventoryBound runtime + 1)) -
          SourceConditionalNativePosterior.decoder runtime.tick.next read (read (inventoryBound runtime + 1))‖ ^ 2 := by
  have count := congrArg (fun value : Nat => (value : ℝ))
    (SourceConditionalNativePosterior.count_sum read (inventoryBound runtime) (read (inventoryBound runtime + 1)))
  push_cast at count
  rw [count, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro actor _
  by_cases same : read actor.val = read (inventoryBound runtime + 1)
  · rw [same, if_pos rfl, one_mul]
  · rw [decoder_next, if_neg same, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), if_neg same, zero_mul]

theorem minimum_difference (runtime : LivingRuntimeState process) (read : Nat → Key) :
    total runtime.tick.next read = total runtime read +
      (SourceConditionalNativeObservers.generate read (inventoryBound runtime) (read (inventoryBound runtime + 1))).1 *
        ‖SourceConditionalNativePosterior.decoder runtime read (read (inventoryBound runtime + 1)) -
          SourceConditionalNativePosterior.decoder runtime.tick.next read (read (inventoryBound runtime + 1))‖ ^ 2 +
      ‖SourceConditionalInventory.born (inventoryBound runtime) -
        SourceConditionalNativePosterior.decoder runtime.tick.next read (read (inventoryBound runtime + 1))‖ ^ 2 := by
  rw [total, total_append, total_decomposition, next_bias]

end
end SourceConditionalNativeBirth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
