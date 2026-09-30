import H0mework.Versions.X.Fock.HistoryConditional.MinimumSharedNextSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceMinimumSharedNext

open SourceCopyCurrentCoordinates (maximumIndex realize shared)
open SourceCopyTemporalBoundary (recordedPrefix)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def initial : Window runtimeSeed.tick.next :=
  recordedPrefix runtimeSeed.tick.next (maximumIndex runtimeSeed.tick.next) 0 ((maximumIndex runtimeSeed.tick.next).val + 1)
    (realize runtimeSeed.tick.next (maximumIndex runtimeSeed.tick.next) 0
      (SourceCopyNativeSharedUpdate.step runtimeSeed (shared runtimeSeed)))

theorem initial_source : initial = native runtimeSeed.tick.next := by
  rw [initial, SourceCopyCurrentCoordinates.shared_source, SourceCopyNativeSharedUpdate.step_source,
    SourceCopyNativeSharedUpdate.source_realize]
  rfl

theorem initial_next : step runtimeSeed.tick.next (next_nonunit runtimeSeed) initial =
    native runtimeSeed.tick.next.tick.next := by
  rw [initial_source, step_source]

end
end SourceMinimumSharedNext
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
