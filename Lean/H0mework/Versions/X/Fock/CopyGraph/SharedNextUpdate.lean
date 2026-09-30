import H0mework.Versions.X.Fock.CopyGraph.SharedNextData
import H0mework.Versions.X.Fock.CopyGraph.CurrentCoordinatesShared

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopySharedNext

open SourceCopyCurrentCoordinates (Coordinates maximumIndex sourceRead shared expand)
open SourceCopyRecordedRecurrence (cutoff)
open SourceCopyTimeModel (finitePhases time hilbert mass)
open SourceCopyNativeModelStep (sourceValue)
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem update_native (runtime : LivingRuntimeState process) :
    update runtime (shared runtime) (finitePhases runtime.tick.next (maximumIndex runtime.tick.next) 0 (sourceValue runtime.tick.next)) =
      shared runtime.tick.next := by
  have generated := update_source runtime (sourceValue runtime)
  rw [SourceCopyNativeModelStep.source_value_next] at generated
  simpa only [SourceCopyCurrentCoordinates.shared_source] using generated

theorem updated_family (runtime : LivingRuntimeState process) :
    expand runtime.tick.next
      (update runtime (shared runtime) (finitePhases runtime.tick.next (maximumIndex runtime.tick.next) 0 (sourceValue runtime.tick.next))) =
        SourceCopyLiveModelFamily.next runtime (SourceCopyLiveModelFamily.family runtime) := by
  rw [update_native, SourceCopyCurrentCoordinates.shared_family, SourceCopyLiveModelFamily.family_next]


end
end SourceCopySharedNext
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
