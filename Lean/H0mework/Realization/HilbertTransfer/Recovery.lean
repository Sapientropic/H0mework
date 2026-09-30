import H0mework.Realization.HilbertTransfer.Transfer

/-! The existing retained isometry gives the common decoder error geometry. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace IsometricRetainedTransfer

open scoped InnerProductSpace

noncomputable section

universe u v

variable {Source : Type u} {Observed : Type v}
variable [NormedAddCommGroup Source] [InnerProductSpace ℂ Source] [CompleteSpace Source]
variable [NormedAddCommGroup Observed] [InnerProductSpace ℂ Observed] [CompleteSpace Observed]

theorem decoder_error_decomposition (pullback : Observed →ₗᵢ[ℂ] Source) (value : Source) (decoder : Observed) :
    ‖value - pullback decoder‖ ^ 2 = ‖residual pullback value‖ ^ 2 + ‖transfer pullback value - decoder‖ ^ 2 := by
  have reconstructed : pullback (transfer pullback value - decoder) + residual pullback value = value - pullback decoder := by
    rw [map_sub]
    calc
      _ = (pullback (transfer pullback value) + residual pullback value) - pullback decoder := by abel
      _ = _ := congrArg (· - pullback decoder) (pullback_transfer_add_residual pullback value)
  have energy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (pullback (transfer pullback value - decoder)) (residual pullback value)
    (residual_orthogonal pullback value (transfer pullback value - decoder))
  rw [reconstructed, pullback.norm_map] at energy
  simpa only [sq] using energy.trans (add_comm _ _)

end
end IsometricRetainedTransfer
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
