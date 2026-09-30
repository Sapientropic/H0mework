import H0mework.Versions.X.Fock.HistoryConditional.MinimumSharedNextInitial
import H0mework.Versions.X.Fock.CopyGraph.SharedNextUpdate

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceMinimumSharedNext

open SourceCopyCurrentCoordinates (maximumIndex expand)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem family_next (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0) :
    expand runtime.tick.next
      (SourceOperatorObservationAcquisition.decode runtime.tick.next (maximumIndex runtime.tick.next) (next_nonunit runtime) 0
        (step runtime nonunit (native runtime))) =
      SourceCopyLiveModelFamily.next runtime (SourceCopyLiveModelFamily.family runtime) := by
  rw [step_source, native, SourceOperatorObservationAcquisition.decode_source,
    ← SourceCopyCurrentCoordinates.shared_source, SourceCopyCurrentCoordinates.shared_family, SourceCopyLiveModelFamily.family_next]

end
end SourceMinimumSharedNext
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
