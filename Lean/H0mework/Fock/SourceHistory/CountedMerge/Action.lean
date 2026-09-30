import H0mework.Fock.SourceHistory.CountedMerge.Representation
import H0mework.Fock.SourceHistory.CountedRecovery.Table

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCountedMerge

open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open SourceRetainedReceiver (At)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
variable {Fine Coarse : Type*} [DecidableEq Fine] [DecidableEq Coarse]

theorem next_simulates (runtime : LivingRuntimeState process)
    (table : SourceCountedObservation.Table Fine) (frame : At runtime Fine)
    (read : Nat → Fine) (forget : Fine → Coarse)
    (source : SourceCountedObservation.Simulates (inventoryBound runtime) (maximumIndex runtime).val table frame)
    (native : frame.native = SourceConditionalNativeObservers.generate read (inventoryBound runtime))
    (keys : frame.keys = SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)) :
    SourceCountedObservation.Simulates (inventoryBound runtime.tick.next) (maximumIndex runtime.tick.next).val
      (SourceCountedObservation.step (inventoryBound runtime) (mergeTable table forget) (forget (read runtime.tick.next.state)))
      (SourceRetainedCoarsening.merge (inventoryBound runtime.tick.next) (maximumIndex runtime.tick.next).val
        (SourceRetainedReceiver.next runtime frame (read runtime.tick.next.state)) forget) := by
  rw [SourceRetainedCoarsening.merge_next runtime frame read forget native keys]
  exact SourceCountedRecovery.step_next_simulates runtime (mergeTable table forget)
    (SourceRetainedCoarsening.merge (inventoryBound runtime) (maximumIndex runtime).val frame forget)
    (merge_simulates _ _ table frame source forget) _

end SourceCountedMerge
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
