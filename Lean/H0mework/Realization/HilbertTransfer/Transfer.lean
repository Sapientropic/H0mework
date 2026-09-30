import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! The shared Hilbert consumer retains the full fibre of an already generated isometry. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace IsometricRetainedTransfer

open scoped InnerProductSpace

noncomputable section

universe u v

variable {Current : Type u} {Next : Type v}
variable [NormedAddCommGroup Current] [InnerProductSpace ℂ Current] [CompleteSpace Current]
variable [NormedAddCommGroup Next] [InnerProductSpace ℂ Next] [CompleteSpace Next]
variable (pullback : Next →ₗᵢ[ℂ] Current)

def transfer : Current →L[ℂ] Next :=
  pullback.toContinuousLinearMap.adjoint

def residual : Current →L[ℂ] Current :=
  ContinuousLinearMap.id ℂ _ - pullback.toContinuousLinearMap.comp
    (transfer pullback)

theorem transfer_pullback (value : Next) :
    transfer pullback (pullback value) = value :=
  DFunLike.congr_fun pullback.adjoint_comp_self value

theorem pullback_transfer_add_residual (value : Current) :
    pullback (transfer pullback value) + residual pullback value = value := by
  change _ + (value - _) = value
  exact add_sub_cancel _ _

theorem transfer_residual (value : Current) :
    transfer pullback (residual pullback value) = 0 := by
  change transfer pullback (value - pullback (transfer pullback value)) = 0
  rw [map_sub, transfer_pullback, sub_self]

theorem residual_orthogonal (value : Current) (next : Next) :
    ⟪pullback next, residual pullback value⟫_ℂ = 0 := by
  change ⟪pullback.toContinuousLinearMap next, residual pullback value⟫_ℂ = 0
  rw [← ContinuousLinearMap.adjoint_inner_right]
  change ⟪next, transfer pullback (residual pullback value)⟫_ℂ = 0
  rw [transfer_residual, inner_zero_right]

theorem energy_decomposition (value : Current) :
    ‖value‖ ^ 2 = ‖transfer pullback value‖ ^ 2 + ‖residual pullback value‖ ^ 2 := by
  have energy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (pullback (transfer pullback value)) (residual pullback value)
    (residual_orthogonal pullback value (transfer pullback value))
  simpa only [pullback_transfer_add_residual, LinearIsometry.norm_map, sq] using energy

theorem transfer_norm_le (value : Current) :
    ‖transfer pullback value‖ ≤ ‖value‖ := by
  have energy := energy_decomposition pullback value
  nlinarith only [energy, sq_nonneg ‖residual pullback value‖, norm_nonneg value,
    norm_nonneg (transfer pullback value)]

theorem residual_zero_iff (value : Current) :
    residual pullback value = 0 ↔ value ∈ pullback.toLinearMap.range := by
  constructor
  · intro vanished
    refine ⟨transfer pullback value, ?_⟩
    change pullback (transfer pullback value) = value
    simpa only [vanished, add_zero] using pullback_transfer_add_residual pullback value
  · rintro ⟨next, rfl⟩
    change pullback next -
      pullback (transfer pullback (pullback next)) = 0
    rw [transfer_pullback, sub_self]

theorem transfer_fibre_iff (left right : Current) :
    transfer pullback left = transfer pullback right ↔
      left - right ∈ pullback.toLinearMap.rangeᗮ := by
  change _ ↔ left - right ∈ pullback.toContinuousLinearMap.rangeᗮ
  rw [ContinuousLinearMap.orthogonal_range]
  change transfer pullback left = transfer pullback right ↔
    transfer pullback (left - right) = 0
  rw [map_sub, sub_eq_zero]


end
end IsometricRetainedTransfer
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
