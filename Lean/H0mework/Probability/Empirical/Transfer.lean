import H0mework.Probability.Empirical.Step
import H0mework.Realization.HilbertTransfer.Transfer

/-! Forward transfer retains exactly the current-history information invisible to the next field. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedEmpiricalHilbert

open SourceGeneratedScalarCofinalTopology.NativeProbability
open scoped InnerProductSpace

noncomputable section

universe u

variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}
variable {B : Type u} [AddCommGroup B] (read : process.State → B)
variable (runtime : LivingRuntimeState process) (bound : Nat)

abbrev transfer : Space read runtime bound →L[ℂ] Space read runtime.tick.next bound :=
  IsometricRetainedTransfer.transfer (pullback read runtime bound)

abbrev residual : Space read runtime bound →L[ℂ] Space read runtime bound :=
  IsometricRetainedTransfer.residual (pullback read runtime bound)

theorem transfer_pullback (value : Space read runtime.tick.next bound) :
    transfer read runtime bound (pullback read runtime bound value) = value :=
  IsometricRetainedTransfer.transfer_pullback (pullback read runtime bound) value

theorem pullback_transfer_add_residual (value : Space read runtime bound) :
    pullback read runtime bound (transfer read runtime bound value) + residual read runtime bound value = value :=
  IsometricRetainedTransfer.pullback_transfer_add_residual (pullback read runtime bound) value

theorem transfer_residual (value : Space read runtime bound) :
    transfer read runtime bound (residual read runtime bound value) = 0 :=
  IsometricRetainedTransfer.transfer_residual (pullback read runtime bound) value

theorem residual_orthogonal (value : Space read runtime bound) (next : Space read runtime.tick.next bound) :
    ⟪pullback read runtime bound next, residual read runtime bound value⟫_ℂ = 0 :=
  IsometricRetainedTransfer.residual_orthogonal (pullback read runtime bound) value next

theorem energy_decomposition (value : Space read runtime bound) :
    ‖value‖ ^ 2 = ‖transfer read runtime bound value‖ ^ 2 + ‖residual read runtime bound value‖ ^ 2 :=
  IsometricRetainedTransfer.energy_decomposition (pullback read runtime bound) value

theorem transfer_norm_le (value : Space read runtime bound) :
    ‖transfer read runtime bound value‖ ≤ ‖value‖ :=
  IsometricRetainedTransfer.transfer_norm_le (pullback read runtime bound) value

theorem residual_zero_iff (value : Space read runtime bound) :
    residual read runtime bound value = 0 ↔ value ∈ (pullback read runtime bound).toLinearMap.range :=
  IsometricRetainedTransfer.residual_zero_iff (pullback read runtime bound) value

theorem transfer_fibre_iff (left right : Space read runtime bound) :
    transfer read runtime bound left = transfer read runtime bound right ↔
      left - right ∈ (pullback read runtime bound).toLinearMap.rangeᗮ :=
  IsometricRetainedTransfer.transfer_fibre_iff (pullback read runtime bound) left right

end
end SourceGeneratedEmpiricalHilbert
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
