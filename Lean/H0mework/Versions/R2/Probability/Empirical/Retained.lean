import H0mework.Versions.R2.Probability.Empirical.Transfer
import H0mework.Realization.HilbertTransfer.Retained

/-! The actual next value and its full source residual reconstruct every current-history vector. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedEmpiricalHilbert

open scoped InnerProductSpace

noncomputable section

universe u

variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}
variable {B : Type u} [AddCommGroup B] (read : process.State → B)
variable (runtime : LivingRuntimeState process) (bound : Nat)

abbrev ResidualSpace :=
  IsometricRetainedTransfer.ResidualSpace (pullback read runtime bound)

abbrev retainedResidual : Space read runtime bound →ₗ[ℂ] ResidualSpace read runtime bound :=
  IsometricRetainedTransfer.retainedResidual (pullback read runtime bound)

abbrev split : Space read runtime bound →ₗ[ℂ]
    Space read runtime.tick.next bound × ResidualSpace read runtime bound :=
  IsometricRetainedTransfer.split (pullback read runtime bound)

abbrev reconstruct : Space read runtime.tick.next bound × ResidualSpace read runtime bound →ₗ[ℂ]
    Space read runtime bound :=
  IsometricRetainedTransfer.reconstruct (pullback read runtime bound)

theorem reconstruct_split (value : Space read runtime bound) :
    reconstruct read runtime bound (split read runtime bound value) = value :=
  IsometricRetainedTransfer.reconstruct_split (pullback read runtime bound) value

theorem transfer_of_residual (value : ResidualSpace read runtime bound) :
    transfer read runtime bound value = 0 :=
  IsometricRetainedTransfer.transfer_of_residual (pullback read runtime bound) value

theorem split_reconstruct (value : Space read runtime.tick.next bound × ResidualSpace read runtime bound) :
    split read runtime bound (reconstruct read runtime bound value) = value :=
  IsometricRetainedTransfer.split_reconstruct (pullback read runtime bound) value

abbrev retainedUpdate : Space read runtime bound ≃ₗ[ℂ]
    Space read runtime.tick.next bound × ResidualSpace read runtime bound :=
  IsometricRetainedTransfer.retainedUpdate (pullback read runtime bound)

theorem retainedUpdate_energy (value : Space read runtime bound) :
    ‖value‖ ^ 2 = ‖(retainedUpdate read runtime bound value).1‖ ^ 2 +
      ‖(retainedUpdate read runtime bound value).2‖ ^ 2 :=
  IsometricRetainedTransfer.retainedUpdate_energy (pullback read runtime bound) value

end
end SourceGeneratedEmpiricalHilbert
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
