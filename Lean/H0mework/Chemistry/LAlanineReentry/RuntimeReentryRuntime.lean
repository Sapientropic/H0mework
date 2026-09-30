import H0mework.Chemistry.LAlanineReentry.RuntimeRuntimeAction

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Reentry.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root Propagation.Interface
noncomputable section

def reentryProcessCurrent (visit : RootVisit reentryLivingRoot.toAuthoritativeRoot.toRoot) :
    SourceNativeLivingRootCurrentAt N := ⟨ReentryV, reentryLivingRoot, .finite visit⟩

def reentryRuntimeProcess : SourceNativeLivingRootProcess N where
  State := RootVisit reentryLivingRoot.toAuthoritativeRoot.toRoot
  stateAt := reentryProcessCurrent
  stateAt_injective := by
    intro left right equality
    change (⟨ReentryV, reentryLivingRoot, .finite left⟩ : SourceNativeLivingRootCurrentAt N) =
      ⟨ReentryV, reentryLivingRoot, .finite right⟩ at equality
    injection equality with _ _ visitEq
    exact SourceNativeTemporalVisitAt.finite_injective visitEq
  initial := reentryLivingRoot.toAuthoritativeRoot.toRoot.initialVisit
  successorAt := by
    intro visit
    refine ⟨visit.next (reentryCompiled_next visit.current), ?_, ?_⟩
    · rcases visit with ⟨current, history⟩
      cases current <;> rfl
    · rcases visit with ⟨current, history⟩
      cases current <;> exact HEq.rfl

def reentryRuntimeFacade : SourceNativeLivingRuntimeFacade N where
  process := reentryRuntimeProcess
  FaceAt := fun _ => ReentryProjection
  componentAt := fun _ _ => reentryProjectionLaw
  installationAt := fun _ _ => .ofEq rfl
  projectionAt := fun _ projection => projection

def reentryRuntimeSeed : LivingRuntimeState reentryRuntimeProcess := reentryRuntimeFacade.seed
def reentryRuntimeAfterFirst : LivingRuntimeState reentryRuntimeProcess := reentryRuntimeSeed.tick.next

theorem reentryRuntime_response (runtime : LivingRuntimeState reentryRuntimeProcess) :
    reentryResponse runtime.state.current = reentrySourceResult := by
  have keeps : ∀ {state : reentryRuntimeProcess.State}, SourceNativeRuntimeReachableAt reentryRuntimeProcess state →
      reentryResponse state.current = reentrySourceResult := by
    intro state reachable
    induction reachable with
    | initial => rfl
    | step prior kept => exact kept
  exact keeps runtime.reachable

theorem reentryRuntime_ready_exact (runtime : LivingRuntimeState reentryRuntimeProcess)
    (result : ReentryResult) (ready : runtime.state.current = .ready result) : result = reentrySourceResult := by
  have generated := reentryRuntime_response runtime
  rw [ready] at generated
  exact generated

theorem reentryRuntime_nextCurrent (runtime : LivingRuntimeState reentryRuntimeProcess) :
    runtime.tick.next.state.current = .ready reentrySourceResult :=
  congrArg ReentryCurrent.ready (reentryRuntime_response runtime)

theorem reentryRuntime_nextHeld (runtime : LivingRuntimeState reentryRuntimeProcess) :
    reentryHeld runtime.tick.next.state.current = Producer.exactTarget :=
  congrArg JointNext.Runtime.JointResult.held (reentryRuntime_response runtime)

theorem reentryRuntimeFirst_generated :
    reentryResponse reentryRuntimeAfterFirst.state.current = generatedReentryAction.answer := rfl

theorem reentryRuntime_seedClock :
    reentryPhysicalTime reentryRuntimeSeed.state.current = 2 * Propagation.Producer.nativeClockStep := reentryParent_clock

theorem reentryRuntime_nextClock (runtime : LivingRuntimeState reentryRuntimeProcess) :
    reentryPhysicalTime runtime.tick.next.state.current = 3 * Propagation.Producer.nativeClockStep := by
  change (reentryResponse runtime.state.current).clock = _
  rw [reentryRuntime_response]
  exact Continuation.targetClock_exact

theorem reentryRuntimeFace_factorizes (runtime : LivingRuntimeState reentryRuntimeProcess) (projection : ReentryProjection) :
    type_of% (reentryRuntimeFacade.readoutAt_factorizes runtime projection) := reentryRuntimeFacade.readoutAt_factorizes runtime projection

theorem reentryRuntime_face_installed (runtime : LivingRuntimeState reentryRuntimeProcess) (projection : ReentryProjection) :
    reentryRuntimeFacade.readoutAt runtime projection = reentryProjectionLaw.outcomeAt projection (reentryEmitted runtime.state.current) := rfl

theorem reentryRuntime_sourceCertificate :
    type_of% (reentryRuntimeFace_factorizes reentryRuntimeSeed .firstReentry) ∧ Producer.reentryClosure := by
  refine ⟨reentryRuntimeFace_factorizes reentryRuntimeSeed .firstReentry, ?_⟩
  rcases reentryRuntimeFacade.readoutAt reentryRuntimeSeed .firstReentry with ⟨_, delivered⟩ | inactive
  · exact delivered.down
  · exact PEmpty.elim inactive

theorem reentryRuntime_nextReentry_inactive (runtime : LivingRuntimeState reentryRuntimeProcess) :
    reentryRuntimeFacade.readoutAt runtime.tick.next .firstReentry =
      (.inr PUnit.unit : SourceNativeProjectionFiberAt reentryProjectionLaw .firstReentry (reentryEmitted runtime.tick.next.state.current)) := rfl

theorem reentryRuntime_next_readonly (runtime : LivingRuntimeState reentryRuntimeProcess) :
    reentryNext runtime.tick.next.state.current = runtime.tick.next.state.current ∧
      IsEmpty (ReentryV.NativeWriteAt runtime.tick.next.state.current) := ⟨rfl, ⟨fun write => nomatch write⟩⟩

theorem reentryRuntime_readiness_installed (runtime : LivingRuntimeState reentryRuntimeProcess) :
    reentryRuntimeFacade.readoutAt runtime.tick.next .readiness =
      (.inl ⟨PUnit.unit, (reentrySourceResult,
        ⟨(reentryRuntime_next_readonly runtime).1, (reentryRuntime_next_readonly runtime).2⟩)⟩ :
        SourceNativeProjectionFiberAt reentryProjectionLaw .readiness (reentryEmitted runtime.tick.next.state.current)) := by
  rw [← reentryRuntime_response runtime]
  rfl

theorem reentryRuntime_wholeLedger_installed (runtime : LivingRuntimeState reentryRuntimeProcess) :
    reentryRuntimeFacade.readoutAt runtime .wholeLedger =
      (.inl ⟨PUnit.unit, reentryLedgerCompiler.compile (reentryEmitted runtime.state.current)⟩ :
        SourceNativeProjectionFiberAt reentryProjectionLaw .wholeLedger (reentryEmitted runtime.state.current)) := rfl

end
end LAlanine40K2025.Reentry.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
