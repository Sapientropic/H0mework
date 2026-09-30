import H0mework.Probability.Empirical.ObservedRecovery
import H0mework.Fock.SourceHistory.ConditionalTransfer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionObservationHistory.Dependent.Installed

open SourceGeneratedEmpiricalHilbert SourceGeneratedScalarDifferentialResidual
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

variable {B : Type} [AddCommGroup B] (read : process.State → B) (depth : Nat)
variable (cotest : ∀ current : LivingRuntimeState process, Space read current depth)

local instance installedClosed (current : LivingRuntimeState process) :
    IsClosed (LinearMap.ker (Runtime.source read depth cotest current) : Set (Space read current depth)) :=
  kernel_closed (fun r : LivingRuntimeState process => r.tick.next)
    (fun r => transfer read r depth) (fun r => innerSL ℂ (cotest r)) current

local instance installedComplete (current : LivingRuntimeState process) :
    CompleteSpace (LinearMap.ker (Runtime.source read depth cotest current)) :=
  (installedClosed read depth cotest current).isComplete.completeSpace_coe

/-- The source window advances once; its last actor retains the original literal native next. -/
theorem runtime_observation_consumed (value : Space read runtimeSeed depth)
    (decoder : ResidualCarrier (Runtime.source read depth cotest runtimeSeed.tick.next)) :
    type_of% (Runtime.next_source read depth cotest runtimeSeed value) ∧
      type_of% (Runtime.next_conditional read depth cotest runtimeSeed value) ∧
      type_of% (Runtime.complete_reconstruction read depth cotest runtimeSeed value) ∧
      type_of% (Runtime.complete_energy read depth cotest runtimeSeed value) ∧
      type_of% (Runtime.decoder_error read depth cotest runtimeSeed value decoder) ∧
      type_of% (SourceConditionalTransfer.Installed.runtime_transfer_factorizes read depth value) :=
  ⟨Runtime.next_source read depth cotest runtimeSeed value,
    Runtime.next_conditional read depth cotest runtimeSeed value,
    Runtime.complete_reconstruction read depth cotest runtimeSeed value,
    Runtime.complete_energy read depth cotest runtimeSeed value,
    Runtime.decoder_error read depth cotest runtimeSeed value decoder,
    SourceConditionalTransfer.Installed.runtime_transfer_factorizes read depth value⟩

end
end SourceGeneratedActionObservationHistory.Dependent.Installed
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
