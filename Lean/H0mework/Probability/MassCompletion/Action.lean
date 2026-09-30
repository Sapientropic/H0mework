import H0mework.Probability.MassCompletion.Mean

/-! The same source successor acts on both generated coordinates and preserves the recovered mass. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceMassCompletion

open SourceOwnedObservationHistory.SourceShift SourceSuccessorBoundary

noncomputable section

def action : Joint →ₗᵢ[ℂ] Joint := shift.withLpProdMap 2 (LinearIsometry.id : ℂ →ₗᵢ[ℂ] ℂ)

theorem firstRead_action (value : Joint) : firstRead (action value) = shift (firstRead value) := rfl

theorem massRead_action (value : Joint) : massRead (action value) = massRead value := rfl

theorem action_source (word : Nat →₀ ℂ) : action (jointRead word) = jointRead (push ℂ word) := by
  apply (WithLp.linearEquiv 2 ℂ (H × ℂ)).injective
  apply Prod.ext
  · exact (readWord_push word).symm
  · exact (mass_push ℂ word).symm

def difference : Joint →L[ℂ] Joint := action.toContinuousLinearMap - ContinuousLinearMap.id ℂ Joint

theorem firstRead_difference (value : Joint) :
    firstRead (difference value) = SourceOwnedObservationHistory.SourceShift.difference (firstRead value) := by
  change firstRead (action value - value) = shift (firstRead value) - firstRead value
  rw [map_sub, firstRead_action]

theorem massRead_difference (value : Joint) : massRead (difference value) = 0 := by
  change massRead (action value - value) = 0
  rw [map_sub, massRead_action, sub_self]

theorem boundary_source (word : Nat →₀ ℂ) :
    jointRead (SourceSuccessorBoundary.boundary ℂ word) = difference (jointRead word) := by
  change jointRead (push ℂ word - word) = action (jointRead word) - jointRead word
  rw [map_sub, action_source]

theorem source_norm_sq (word : Nat →₀ ℂ) :
    ‖jointRead word‖ ^ 2 = ‖readWord word‖ ^ 2 + ‖mass ℂ word‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 (jointRead word)

theorem mean_joint_norm_sq (bound : Nat) : ‖jointRead (meanWord bound)‖ ^ 2 = 1 / (bound + 1 : ℝ) + 1 := by
  rw [source_norm_sq, mass_meanWord]
  change ‖mean bound‖ ^ 2 + ‖(1 : ℂ)‖ ^ 2 = _
  rw [mean_norm_sq, norm_one, one_pow]

theorem mean_joint_ne_zero (bound : Nat) : jointRead (meanWord bound) ≠ 0 := by
  intro vanished
  have preserved := massRead_source (meanWord bound)
  rw [vanished, map_zero, mass_meanWord] at preserved
  exact zero_ne_one preserved

theorem generated_limit_fixed : action (WithLp.toLp 2 ((0 : H), (1 : ℂ))) = WithLp.toLp 2 (0, 1) := by
  apply (WithLp.linearEquiv 2 ℂ (H × ℂ)).injective
  apply Prod.ext
  · exact map_zero shift
  · rfl

theorem generated_limit_difference_zero : difference (WithLp.toLp 2 ((0 : H), (1 : ℂ))) = 0 := by
  change action (WithLp.toLp 2 ((0 : H), (1 : ℂ))) - WithLp.toLp 2 (0, 1) = 0
  rw [generated_limit_fixed, sub_self]

end
end SourceMassCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
