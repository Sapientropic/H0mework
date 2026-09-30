import H0mework.Fock.CopyGraph.SharedNextUpdate
import H0mework.Fock.CopyGraph.SharedNext.Effect

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopySharedNext

open SourceCopyCurrentCoordinates (maximumIndex shared jointModelEquiv)
open SourceCopyNativeModelStep (sourceValue)
open SourceCopyTimeModel (finitePhases time)
open SourceGeneratedAcquisitionContinuation SourceGeneratedActionWords.Fock SourceGeneratedActionWords.Fock.Dynamic
open SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
attribute [local instance] SourceCompleteGraph.completeUniform SourceCompleteGraph.completeMeasurable
  SourceCompleteGraph.completeBorel SourceCompleteGraph.completeT2

theorem native_packet_source (runtime : LivingRuntimeState process) (phase : Fin ((maximumIndex runtime.tick.next).val + 1)) :
    nativePacket runtime phase = SourceCopyTemporalBoundary.observer runtime.tick.next (maximumIndex runtime.tick.next) 0
      (sourceValue (runtime.tick.next.advance phase.val)) :=
  congrArg (SourceCopyTemporalBoundary.observer runtime.tick.next (maximumIndex runtime.tick.next) 0)
    (SourceCopyTimeModel.time_native runtime.tick.next phase.val)

theorem native_model_update (runtime : LivingRuntimeState process) :
    updateModel runtime ((jointModelEquiv runtime).symm (shared runtime)) (nativePacket runtime) =
      (jointModelEquiv runtime.tick.next).symm (shared runtime.tick.next) := by
  rw [updateModel, LinearEquiv.apply_symm_apply]
  exact congrArg (jointModelEquiv runtime.tick.next).symm (update_native runtime)

theorem native_forcing (runtime : LivingRuntimeState process) (phase : Fin ((maximumIndex runtime.tick.next).val + 1)) :
    SourceColumnForcing.forcing (inventoryBound runtime.tick.next) (inventoryBound runtime.tick.next) (maximumIndex runtime.tick.next)
      (Hilbert.read 0 (inventoryBound runtime.tick.next))
      (SourceCopyGraph.action (inventoryBound runtime.tick.next) (maximumIndex runtime.tick.next) (nativePacket runtime phase)) =
      SourceColumnForcing.forcing (inventoryBound runtime.tick.next) (inventoryBound runtime.tick.next) (maximumIndex runtime.tick.next)
        (Hilbert.read 0 (inventoryBound runtime.tick.next)) (sourceValue (runtime.tick.next.advance phase.val)) :=
  (packet_forcing runtime.tick.next (maximumIndex runtime.tick.next) 0 (Hilbert.read 0 (inventoryBound runtime.tick.next))
    (sourceValue runtime.tick.next) phase).trans
      (congrArg (SourceColumnForcing.forcing (inventoryBound runtime.tick.next) (inventoryBound runtime.tick.next) (maximumIndex runtime.tick.next)
        (Hilbert.read 0 (inventoryBound runtime.tick.next))) (SourceCopyTimeModel.time_native runtime.tick.next phase.val))

theorem native_conditional (runtime : LivingRuntimeState process) (phase : Fin ((maximumIndex runtime.tick.next).val + 1))
    (atom : Complete.Carrier 0)
    (supported : atom ∈ (observed (historyPMF (inventoryBound runtime.tick.next)) (Hilbert.read 0 (inventoryBound runtime.tick.next))).support) :
    SourceColumnForcing.forcing (inventoryBound runtime.tick.next) (inventoryBound runtime.tick.next) (maximumIndex runtime.tick.next)
      (Hilbert.read 0 (inventoryBound runtime.tick.next))
      (SourceCopyGraph.action (inventoryBound runtime.tick.next) (maximumIndex runtime.tick.next) (nativePacket runtime phase)) atom =
      SourceWeightedRecovery.conditionalMean (historyPMF (inventoryBound runtime.tick.next)) (Hilbert.read 0 (inventoryBound runtime.tick.next))
        (SourceColumnForcing.samples (inventoryBound runtime.tick.next) (inventoryBound runtime.tick.next) (maximumIndex runtime.tick.next)
          (sourceValue (runtime.tick.next.advance phase.val))) atom supported := by
  rw [native_forcing]
  exact SourceColumnForcing.forcing_conditional _ _ _ _ _ atom supported

end
end SourceCopySharedNext
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
