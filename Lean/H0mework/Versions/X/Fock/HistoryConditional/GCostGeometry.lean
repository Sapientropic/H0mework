import H0mework.Versions.X.Fock.HistoryConditional.GCostCost

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGInformationCost

open SourceGeneratedRuntimeHistoryProbability
open SourceConditionalInventory (values)
open SourceOwnedObservationHistory.SourceShift (H basis place successor_orthogonal)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section

abbrev hilbertRead : SourceJointClockGraph.Carrier →L[ℂ] H :=
  SourceMassCompletion.firstRead.comp SourceJointClockGraph.joint

theorem actual_hilbert (bound : Nat) (index : Fin (bound + 1)) :
    hilbertRead (values bound index) = basis (index.val + 1) := by
  change SourceCopyTimeModel.hilbert (SourceCopyNativeModelStep.sourceValue (runtimeAt (index.val + 1))) = _
  rw [SourceConditionalVector.native_form, runtimeAt_state]
  rfl

theorem actual_mass (bound : Nat) (index : Fin (bound + 1)) : SourceVectorMoment.massMap (values bound index) = 1 := by
  change SourceVectorMoment.massMap (SourceCopyNativeModelStep.sourceValue (runtimeAt (index.val + 1))) = 1
  rw [SourceConditionalVector.native_form]
  rfl

theorem actual_clock (bound : Nat) (index : Fin (bound + 1)) :
    SourceJointClockGraph.clock (values bound index) = (index.val : ℂ) + 2 := by
  change SourceJointClockGraph.clock (SourceCopyNativeModelStep.sourceValue (runtimeAt (index.val + 1))) = _
  rw [SourceConditionalVector.native_form, runtimeAt_state]
  change ((index.val + 1 : Nat) : ℂ) + 1 = _
  push_cast
  ring

def synthesis (bound : Nat) : (Fin (bound + 1) → ℂ) →ₗ[ℂ] H :=
  ∑ index, (LinearMap.proj index).smulRight (basis (index.val + 1))

def sourceProjection (bound : Nat) : SourceJointClockGraph.Carrier →ₗ[ℂ] H :=
  ∑ index : Fin (bound + 1), (coordinateRead (index.val + 1)).toLinearMap.smulRight (basis (index.val + 1))

theorem source_projection (bound : Nat) (index : Fin (bound + 1)) :
    sourceProjection bound (values bound index) = hilbertRead (values bound index) := by
  rw [actual_hilbert, sourceProjection, LinearMap.sum_apply]
  change (∑ actor : Fin (bound + 1), coordinateRead (actor.val + 1) (values bound index) • basis (actor.val + 1)) = _
  simp only [coordinate_actual]
  rw [Finset.sum_eq_single index]
  · simp
  · intro other _ different
    rw [if_neg (Ne.symm different)]
    exact zero_smul _ _
  · intro absent
    exact (absent (Finset.mem_univ _)).elim

theorem synthesis_norm (bound : Nat) (value : Fin (bound + 1) → ℂ) :
    ‖synthesis bound value‖ ^ 2 = ∑ index, ‖value index‖ ^ 2 := by
  have family := successor_orthogonal.comp (f := (Fin.val : Fin (bound + 1) → Nat)) Fin.val_injective
  have source := family.norm_sum value Finset.univ
  simp only [synthesis, LinearMap.sum_apply]
  change ‖∑ index, value index • basis (index.val + 1)‖ ^ 2 = _
  have point (index : Fin (bound + 1)) : value index • basis (index.val + 1) = place (index.val + 1) (value index) := by
    change value index • place (index.val + 1) 1 = _
    rw [← map_smul]
    simp only [smul_eq_mul, mul_one]
  simp only [point]
  simpa only [Finset.mem_univ, forall_const, Finset.sum_const_zero, Finset.sum_ite_irrel, if_true] using source

theorem centered_hilbert (bound : Nat) (p : PMF (Fin (bound + 1))) (index : Fin (bound + 1)) :
    hilbertRead (values bound index - SourceVectorMoment.mean p (values bound)) =
      sourceProjection bound (values bound index - SourceVectorMoment.mean p (values bound)) := by
  simp only [map_sub, SourceVectorMoment.mean, map_sum, map_smul, source_projection]

theorem centered_mass (bound : Nat) (p : PMF (Fin (bound + 1))) (index : Fin (bound + 1)) :
    SourceVectorMoment.massMap (values bound index - SourceVectorMoment.mean p (values bound)) = 0 := by
  rw [map_sub, actual_mass, SourceVectorMoment.mass_const p (values bound) 1 (actual_mass bound), sub_self]

theorem centered_norm (bound : Nat) (p : PMF (Fin (bound + 1))) (index : Fin (bound + 1)) :
    ‖values bound index - SourceVectorMoment.mean p (values bound)‖ ^ 2 =
      (∑ actor : Fin (bound + 1), ‖coordinateRead (actor.val + 1) (values bound index - SourceVectorMoment.mean p (values bound))‖ ^ 2) +
      ‖SourceJointClockGraph.clock (values bound index - SourceVectorMoment.mean p (values bound))‖ ^ 2 := by
  rw [SourceJointClockGraph.norm_sq, WithLp.prod_norm_sq_eq_of_L2]
  change (‖hilbertRead (values bound index - SourceVectorMoment.mean p (values bound))‖ ^ 2 +
    ‖SourceVectorMoment.massMap (values bound index - SourceVectorMoment.mean p (values bound))‖ ^ 2) + _ = _
  rw [centered_mass, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero, centered_hilbert]
  have projection (value : SourceJointClockGraph.Carrier) :
      sourceProjection bound value = synthesis bound (fun actor => coordinateRead (actor.val + 1) value) := by
    simp only [sourceProjection, synthesis, LinearMap.sum_apply]
    rfl
  rw [projection, synthesis_norm]

end
end SourceGInformationCost
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
