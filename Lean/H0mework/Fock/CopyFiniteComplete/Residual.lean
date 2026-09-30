import H0mework.Fock.CopyFiniteComplete.Decoder

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFiniteCompleteGraph

open SourceGeneratedAcquisitionContinuation SourceGeneratedJointClockGraph
open SourceGeneratedActionWords.Fock SourceGeneratedActionWords.Fock.Dynamic
open SourceCopyProgram (Index)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
attribute [local instance] SourceCompleteGraph.completeUniform SourceCompleteGraph.completeMeasurable
  SourceCompleteGraph.completeBorel SourceCompleteGraph.completeT2 windowMeasurable

theorem residual_value (model : Nat) (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (target : SourceJointClockGraph.Carrier) :
    SourceConditionalGraphDecoder.residual (inventoryBound runtime) (inventoryBound runtime) index
      (Hilbert.read model (inventoryBound runtime)) target =
      SourceConditionalGraphDecoder.residual (inventoryBound runtime) (inventoryBound runtime) index (query runtime) target := by
  have full := SourceConditionalGraphDecoder.original_reconstruction (inventoryBound runtime) (inventoryBound runtime) index
    (Hilbert.read model (inventoryBound runtime)) target
  have finite := SourceConditionalGraphDecoder.original_reconstruction (inventoryBound runtime) (inventoryBound runtime) index
    (query runtime) target
  rw [decoder_value] at full
  exact add_left_cancel (full.trans finite.symm)

theorem residual_linear (model : Nat) (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    SourceConditionalGraphDecoder.residual (inventoryBound runtime) (inventoryBound runtime) index
      (Hilbert.read model (inventoryBound runtime)) =
      SourceConditionalGraphDecoder.residual (inventoryBound runtime) (inventoryBound runtime) index (query runtime) := by
  apply ContinuousLinearMap.ext
  exact residual_value model runtime index

theorem finite_boundary_nonzero (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    SourceConditionalGraphDecoder.residual (inventoryBound runtime) (inventoryBound runtime) index (query runtime)
      SourceCompleteGraph.boundary ≠ 0 := by
  rw [← residual_value (inventoryBound runtime)]
  exact SourceCompleteGraph.boundary_residual_nonzero _ _ _ index

end
end SourceFiniteCompleteGraph
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
