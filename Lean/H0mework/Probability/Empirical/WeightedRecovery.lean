import H0mework.Probability.Recovery.Error
import H0mework.Probability.Empirical.Error
import H0mework.Realization.HistoryTopology.Compactness

/-! The original runtime transfer and recovery error consume the common source-weighted core. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWeightedRecovery.Runtime

open SourceGeneratedRuntimeHistoryProbability SourceConditionalTransfer
open SourceGeneratedScalarCofinalTopology.NativeProbability

noncomputable section

universe u

variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}
variable {B : Type u} [AddCommGroup B] (read : process.State → B)
variable (runtime : LivingRuntimeState process) (bound : Nat)

local instance : UniformSpace (Field read) := fieldUniform read
local instance : MeasurableSpace (Field read) := fieldBorel read
local instance : BorelSpace (Field read) := ⟨rfl⟩
local instance : T2Space (Field read) := field_t2 read

def sourceTask (value : SourceGeneratedEmpiricalHilbert.Space read runtime bound) (index : Fin (bound + 1)) : ℂ :=
  value (fieldSample read runtime bound index)

theorem transfer_is_weighted_optimum (value : SourceGeneratedEmpiricalHilbert.Space read runtime bound)
    (atom : Field read) (supported : atom ∈ (fieldPMF read runtime.tick.next bound).support) :
    SourceGeneratedEmpiricalHilbert.transfer read runtime bound value atom =
      optimalDecoder (historyPMF bound) (nextAtom read runtime bound) (sourceTask read runtime bound value) atom := by
  have sourceSupport : atom ∈ (observed (historyPMF bound) (nextAtom read runtime bound)).support := by
    change atom ∈ ((historyPMF bound).map (nextAtom read runtime bound)).support
    rw [← nextPMF_from_indices]
    exact supported
  exact (transfer_at_atom read runtime bound value atom supported).trans
    (optimal_is_conditional (historyPMF bound) (nextAtom read runtime bound)
      (sourceTask read runtime bound value) atom sourceSupport).symm

theorem runtime_error_from_shared_geometry (value : SourceGeneratedEmpiricalHilbert.Space read runtime bound)
    (decoder : Field read → ℂ) :
    SourceConditionalRecovery.sourceError read runtime bound value decoder =
      ‖SourceGeneratedEmpiricalHilbert.residual read runtime bound value‖ ^ 2 +
        SourceConditionalRecovery.decoderError read runtime bound
          (SourceGeneratedEmpiricalHilbert.transfer read runtime bound value) decoder := by
  rw [SourceConditionalRecovery.sourceError_eq_norm, SourceConditionalRecovery.decoderError_eq_norm]
  exact IsometricRetainedTransfer.decoder_error_decomposition
    (SourceGeneratedEmpiricalHilbert.pullback read runtime bound) value
    (SourceConditionalRecovery.decoderValue read runtime bound decoder)

end
end SourceWeightedRecovery.Runtime
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
