import H0mework.Realization.HilbertTransfer.Retained

/-! Isometry composition conserves the two generated residuals as an orthogonal source sum. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace IsometricRetainedTransfer

open scoped InnerProductSpace

noncomputable section

universe u v w

variable {Source : Type u} {Mid : Type v} {Target : Type w}
variable [NormedAddCommGroup Source] [InnerProductSpace ℂ Source] [CompleteSpace Source]
variable [NormedAddCommGroup Mid] [InnerProductSpace ℂ Mid] [CompleteSpace Mid]
variable [NormedAddCommGroup Target] [InnerProductSpace ℂ Target] [CompleteSpace Target]
variable (first : Mid →ₗᵢ[ℂ] Source) (second : Target →ₗᵢ[ℂ] Mid)

theorem transfer_comp :
    transfer (first.comp second) = (transfer second).comp (transfer first) := by
  change (first.toContinuousLinearMap.comp second.toContinuousLinearMap).adjoint = _
  exact ContinuousLinearMap.adjoint_comp _ _

theorem residual_comp (value : Source) :
    residual (first.comp second) value =
      residual first value + first (residual second (transfer first value)) := by
  change value - first (second (transfer (first.comp second) value)) = _
  rw [transfer_comp]
  change value - first (second (transfer second (transfer first value))) =
    (value - first (transfer first value)) +
      first (transfer first value - second (transfer second (transfer first value)))
  rw [map_sub]
  abel

theorem residual_comp_orthogonal (value : Source) :
    ⟪residual first value, first (residual second (transfer first value))⟫_ℂ = 0 :=
  inner_eq_zero_symm.mp (residual_orthogonal first value (residual second (transfer first value)))

theorem residual_comp_energy (value : Source) :
    ‖residual (first.comp second) value‖ ^ 2 = ‖residual first value‖ ^ 2 +
      ‖residual second (transfer first value)‖ ^ 2 := by
  rw [residual_comp]
  have energy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (residual first value) (first (residual second (transfer first value)))
    (residual_comp_orthogonal first second value)
  simpa only [LinearIsometry.norm_map, sq] using energy

theorem retained_comp_energy (value : Source) :
    ‖value‖ ^ 2 = ‖transfer second (transfer first value)‖ ^ 2 + ‖residual first value‖ ^ 2 +
      ‖residual second (transfer first value)‖ ^ 2 := by
  have energy := energy_decomposition (first.comp second) value
  rw [transfer_comp, residual_comp_energy] at energy
  change ‖value‖ ^ 2 = ‖transfer second (transfer first value)‖ ^ 2 +
    (‖residual first value‖ ^ 2 + ‖residual second (transfer first value)‖ ^ 2) at energy
  exact energy.trans (add_assoc _ _ _).symm

end
end IsometricRetainedTransfer
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
