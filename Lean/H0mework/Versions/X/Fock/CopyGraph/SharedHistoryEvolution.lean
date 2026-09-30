import H0mework.Versions.X.Fock.CopyGraph.SharedNextSourceStepSource
import H0mework.Versions.X.Fock.CopyGraph.SharedNextData

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopySharedHistory

open SourceCopyCurrentCoordinates (Coordinates maximumIndex sourceRead)
open SourceCopySharedNext (update nativePacket)
open SourceCopyNativeModelStep (sourceValue)
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def evolve (runtime : LivingRuntimeState process) (initial : Coordinates runtime (maximumIndex runtime) 0) :
    (stage : Nat) → Coordinates (runtime.advance stage) (maximumIndex (runtime.advance stage)) 0 :=
  Nat.rec (motive := fun stage => Coordinates (runtime.advance stage) (maximumIndex (runtime.advance stage)) 0)
    initial (fun stage previous => update (runtime.advance stage) previous (nativePacket (runtime.advance stage)))

theorem evolve_step (runtime : LivingRuntimeState process) (initial : Coordinates runtime (maximumIndex runtime) 0) (stage : Nat) :
    evolve runtime initial (stage + 1) =
      update (runtime.advance stage) (evolve runtime initial stage) (nativePacket (runtime.advance stage)) := rfl

theorem evolve_source (runtime : LivingRuntimeState process) (stage : Nat) :
    evolve runtime (sourceRead runtime (maximumIndex runtime) 0 (sourceValue runtime)) stage =
      sourceRead (runtime.advance stage) (maximumIndex (runtime.advance stage)) 0 (sourceValue (runtime.advance stage)) := by
  induction stage with
  | zero => rfl
  | succ stage previous =>
    rw [evolve_step, previous, nativePacket]
    have source := SourceCopySharedNext.update_source (runtime.advance stage) (sourceValue (runtime.advance stage))
    rw [SourceCopyNativeModelStep.source_value_next] at source
    exact source

def canonical (runtime : LivingRuntimeState process) : Coordinates runtime (maximumIndex runtime) 0 :=
  Eq.mp (congrArg (fun current : LivingRuntimeState process => Coordinates current (maximumIndex current) 0) (runtime_eq runtime).symm)
    (SourceCopyNativeSharedUpdate.trajectory runtimeSeed
      (sourceRead runtimeSeed (maximumIndex runtimeSeed) 0 (sourceValue runtimeSeed)) runtime.state)

theorem canonical_source (runtime : LivingRuntimeState process) :
    canonical runtime = sourceRead runtime (maximumIndex runtime) 0 (sourceValue runtime) := by
  have transport : ∀ (first second : LivingRuntimeState process) (same : first = second),
      Eq.mp (congrArg (fun current : LivingRuntimeState process => Coordinates current (maximumIndex current) 0) same)
        (sourceRead first (maximumIndex first) 0 (sourceValue first)) =
          sourceRead second (maximumIndex second) 0 (sourceValue second) := by
    intro first second same
    cases same
    rfl
  rw [canonical, SourceCopyNativeSharedUpdate.trajectory_source]
  exact transport _ _ (runtime_eq runtime).symm

end
end SourceCopySharedHistory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
