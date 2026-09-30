import H0mework.Realization.HilbertTransfer.Transfer

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

abbrev ResidualSpace := ↥(pullback.toLinearMap.rangeᗮ)

def retainedResidual : Current →ₗ[ℂ] (ResidualSpace pullback) :=
  (residual pullback).toLinearMap.codRestrict _ (by
    intro value next member
    obtain ⟨source, rfl⟩ := member
    exact residual_orthogonal pullback value source)

def split : Current →ₗ[ℂ]
    Next × (ResidualSpace pullback) :=
  (transfer pullback).toLinearMap.prod (retainedResidual pullback)

def reconstruct : Next × (ResidualSpace pullback) →ₗ[ℂ]
    Current :=
  pullback.toLinearMap.comp (LinearMap.fst ℂ _ _) +
    (pullback.toLinearMap.rangeᗮ).subtype.comp (LinearMap.snd ℂ _ _)

theorem reconstruct_split (value : Current) :
    reconstruct pullback (split pullback value) = value :=
  pullback_transfer_add_residual pullback value

theorem transfer_of_residual (value : (ResidualSpace pullback)) :
    transfer pullback value = 0 := by
  have member := value.property
  change value.val ∈ pullback.toContinuousLinearMap.rangeᗮ at member
  rw [ContinuousLinearMap.orthogonal_range] at member
  exact member

theorem split_reconstruct (value : Next × (ResidualSpace pullback)) :
    split pullback (reconstruct pullback value) = value := by
  apply Prod.ext
  · change transfer pullback (pullback value.1 + value.2.val) = value.1
    rw [map_add, transfer_pullback, transfer_of_residual, add_zero]
  · apply Subtype.ext
    change residual pullback (pullback value.1 + value.2.val) = value.2.val
    change (pullback value.1 + value.2.val) -
      pullback (transfer pullback (pullback value.1 + value.2.val)) = _
    rw [map_add, transfer_pullback, transfer_of_residual, add_zero, add_sub_cancel_left]

def retainedUpdate : Current ≃ₗ[ℂ]
    Next × (ResidualSpace pullback) :=
  LinearEquiv.ofLinearMap (split pullback) (reconstruct pullback)
    (LinearMap.ext (split_reconstruct pullback))
    (LinearMap.ext (reconstruct_split pullback))

theorem retainedUpdate_energy (value : Current) :
    ‖value‖ ^ 2 = ‖(retainedUpdate pullback value).1‖ ^ 2 +
      ‖(retainedUpdate pullback value).2‖ ^ 2 :=
  energy_decomposition pullback value


end
end IsometricRetainedTransfer
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
