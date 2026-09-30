import H0mework.Probability.Empirical.ObservedSource
import H0mework.Realization.ObservationActions.DependentHilbert
import H0mework.Realization.HilbertTransfer.Recovery

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionObservationHistory.Dependent.Runtime

open SourceGeneratedEmpiricalHilbert SourceGeneratedScalarDifferentialResidual
open scoped InnerProductSpace

noncomputable section

variable {N : WorldRelationNetwork.{0}} {process : SourceNativeLivingRootProcess N}
variable {B : Type} [AddCommGroup B] (read : process.State → B) (bound : Nat)
variable (cotest : ∀ runtime : LivingRuntimeState process, Space read runtime bound)

local instance recoveryClosed (runtime : LivingRuntimeState process) :
    IsClosed (LinearMap.ker (source read bound cotest runtime) : Set (Space read runtime bound)) :=
  kernel_closed (fun r : LivingRuntimeState process => r.tick.next)
    (fun r => transfer read r bound) (fun r => innerSL ℂ (cotest r)) runtime

local instance recoveryComplete (runtime : LivingRuntimeState process) :
    CompleteSpace (LinearMap.ker (source read bound cotest runtime)) :=
  (recoveryClosed read bound cotest runtime).isComplete.completeSpace_coe

abbrev realizationAt (runtime : LivingRuntimeState process) :=
  embedding (fun r : LivingRuntimeState process => r.tick.next)
    (fun r => transfer read r bound) (fun r => innerSL ℂ (cotest r)) runtime

def recoveredPullback (runtime : LivingRuntimeState process) :
    ResidualCarrier (source read bound cotest runtime.tick.next) →ₗᵢ[ℂ] Space read runtime bound :=
  (pullback read runtime bound).comp (realizationAt read bound cotest runtime.tick.next)

theorem recovered_transfer (runtime : LivingRuntimeState process) (value : Space read runtime bound) :
    IsometricRetainedTransfer.transfer (recoveredPullback read bound cotest runtime) value =
      next read bound cotest runtime (canonicalResidual (source read bound cotest runtime) value) := by
  have square := congrArg (fun operation : Space read runtime bound →L[ℂ]
      ResidualCarrier (source read bound cotest runtime.tick.next) => operation value)
    (IsometricRetainedTransfer.transfer_comp (pullback read runtime bound)
      (realizationAt read bound cotest runtime.tick.next))
  exact square.trans ((transfer_embedding (fun r : LivingRuntimeState process => r.tick.next)
    (fun r => transfer read r bound) (fun r => innerSL ℂ (cotest r)) runtime.tick.next
    (transfer read runtime bound value)).trans (next_source read bound cotest runtime value).symm)

theorem complete_reconstruction (runtime : LivingRuntimeState process) (value : Space read runtime bound) :
    recoveredPullback read bound cotest runtime
        (next read bound cotest runtime (canonicalResidual (source read bound cotest runtime) value)) +
      (residual read runtime bound value + pullback read runtime bound
        (IsometricRetainedTransfer.residual (realizationAt read bound cotest runtime.tick.next)
          (transfer read runtime bound value))) = value := by
  have reconstruction := IsometricRetainedTransfer.pullback_transfer_add_residual
    (recoveredPullback read bound cotest runtime) value
  rw [recovered_transfer] at reconstruction
  exact (congrArg (fun tail => recoveredPullback read bound cotest runtime
      (next read bound cotest runtime (canonicalResidual (source read bound cotest runtime) value)) + tail)
    (IsometricRetainedTransfer.residual_comp (pullback read runtime bound)
      (realizationAt read bound cotest runtime.tick.next) value).symm).trans reconstruction

theorem complete_energy (runtime : LivingRuntimeState process) (value : Space read runtime bound) :
    ‖value‖ ^ 2 =
      ‖next read bound cotest runtime (canonicalResidual (source read bound cotest runtime) value)‖ ^ 2 +
        ‖residual read runtime bound value‖ ^ 2 +
          ‖IsometricRetainedTransfer.residual (realizationAt read bound cotest runtime.tick.next)
            (transfer read runtime bound value)‖ ^ 2 := by
  have energy := IsometricRetainedTransfer.retained_comp_energy (pullback read runtime bound)
    (realizationAt read bound cotest runtime.tick.next) value
  have actual := (transfer_embedding (fun r : LivingRuntimeState process => r.tick.next)
    (fun r => transfer read r bound) (fun r => innerSL ℂ (cotest r)) runtime.tick.next
    (transfer read runtime bound value)).trans (next_source read bound cotest runtime value).symm
  exact energy.trans (congrArg (fun observed => ‖observed‖ ^ 2 +
    ‖residual read runtime bound value‖ ^ 2 +
      ‖IsometricRetainedTransfer.residual (realizationAt read bound cotest runtime.tick.next)
        (transfer read runtime bound value)‖ ^ 2) actual)

theorem decoder_error (runtime : LivingRuntimeState process) (value : Space read runtime bound)
    (decoder : ResidualCarrier (source read bound cotest runtime.tick.next)) :
    ‖value - recoveredPullback read bound cotest runtime decoder‖ ^ 2 =
      ‖residual read runtime bound value‖ ^ 2 +
        ‖IsometricRetainedTransfer.residual (realizationAt read bound cotest runtime.tick.next)
          (transfer read runtime bound value)‖ ^ 2 +
        ‖next read bound cotest runtime (canonicalResidual (source read bound cotest runtime) value) - decoder‖ ^ 2 := by
  have error := IsometricRetainedTransfer.decoder_error_decomposition
    (recoveredPullback read bound cotest runtime) value decoder
  rw [recovered_transfer] at error
  exact (error.trans (congrArg (fun loss => loss +
    ‖next read bound cotest runtime (canonicalResidual (source read bound cotest runtime) value) - decoder‖ ^ 2)
    (IsometricRetainedTransfer.residual_comp_energy (pullback read runtime bound)
      (realizationAt read bound cotest runtime.tick.next) value)))

end
end SourceGeneratedActionObservationHistory.Dependent.Runtime
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
