import H0mework.Chemistry.LAlanineJointNext.RuntimeRuntimeAction

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.JointNext.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root Propagation.Interface
noncomputable section

def jointProcessCurrent (visit : RootVisit jointLivingRoot.toAuthoritativeRoot.toRoot) :
    SourceNativeLivingRootCurrentAt N := ⟨JointV, jointLivingRoot, .finite visit⟩

def jointRuntimeProcess : SourceNativeLivingRootProcess N where
  State := RootVisit jointLivingRoot.toAuthoritativeRoot.toRoot
  stateAt := jointProcessCurrent
  stateAt_injective := by
    intro left right equality
    change (⟨JointV, jointLivingRoot, .finite left⟩ : SourceNativeLivingRootCurrentAt N) =
      ⟨JointV, jointLivingRoot, .finite right⟩ at equality
    injection equality with _ _ visitEq
    exact SourceNativeTemporalVisitAt.finite_injective visitEq
  initial := jointLivingRoot.toAuthoritativeRoot.toRoot.initialVisit
  successorAt := by
    intro visit
    refine ⟨visit.next (jointCompiled_next visit.current), ?_, ?_⟩
    · rcases visit with ⟨current, history⟩
      cases current <;> rfl
    · rcases visit with ⟨current, history⟩
      cases current <;> exact HEq.rfl

def jointRuntimeFacade : SourceNativeLivingRuntimeFacade N where
  process := jointRuntimeProcess
  FaceAt := fun _ => JointProjection
  componentAt := fun _ _ => jointProjectionLaw
  installationAt := fun _ _ => .ofEq rfl
  projectionAt := fun _ projection => projection

def jointRuntimeSeed : LivingRuntimeState jointRuntimeProcess := jointRuntimeFacade.seed
def jointRuntimeAfterFirst : LivingRuntimeState jointRuntimeProcess := jointRuntimeSeed.tick.next

theorem jointRuntime_response (runtime : LivingRuntimeState jointRuntimeProcess) :
    jointResponse runtime.state.current = jointSourceResult := by
  have keeps : ∀ {state : jointRuntimeProcess.State}, SourceNativeRuntimeReachableAt jointRuntimeProcess state →
      jointResponse state.current = jointSourceResult := by
    intro state reachable
    induction reachable with
    | initial => rfl
    | step prior kept => exact kept
  exact keeps runtime.reachable

theorem jointRuntime_ready_exact (runtime : LivingRuntimeState jointRuntimeProcess)
    (result : JointResult) (ready : runtime.state.current = .ready result) : result = jointSourceResult := by
  have generated := jointRuntime_response runtime
  rw [ready] at generated
  exact generated

theorem jointRuntime_nextCurrent (runtime : LivingRuntimeState jointRuntimeProcess) :
    runtime.tick.next.state.current = .ready jointSourceResult :=
  congrArg JointCurrent.ready (jointRuntime_response runtime)

theorem jointRuntime_nextHeld (runtime : LivingRuntimeState jointRuntimeProcess) :
    jointHeld runtime.tick.next.state.current = Producer.exactTarget :=
  congrArg JointResult.held (jointRuntime_response runtime)

theorem jointRuntimeFirst_generated :
    jointResponse jointRuntimeAfterFirst.state.current = generatedJointAction.answer := rfl

theorem jointRuntime_seedClock : jointPhysicalTime jointRuntimeSeed.state.current = Propagation.Producer.nativeClockStep :=
  jointParent_clock

theorem jointRuntime_nextClock (runtime : LivingRuntimeState jointRuntimeProcess) :
    jointPhysicalTime runtime.tick.next.state.current = 2 * Propagation.Producer.nativeClockStep := by
  change (jointResponse runtime.state.current).clock = _
  rw [jointRuntime_response]
  exact Interface.targetClock_exact

theorem jointRuntimeFace_factorizes (runtime : LivingRuntimeState jointRuntimeProcess) (projection : JointProjection) :
    type_of% (jointRuntimeFacade.readoutAt_factorizes runtime projection) := jointRuntimeFacade.readoutAt_factorizes runtime projection

theorem jointRuntime_face_installed (runtime : LivingRuntimeState jointRuntimeProcess) (projection : JointProjection) :
    jointRuntimeFacade.readoutAt runtime projection = jointProjectionLaw.outcomeAt projection (jointEmitted runtime.state.current) := rfl

theorem jointRuntime_sourceCertificate :
    type_of% (jointRuntimeFace_factorizes jointRuntimeSeed .firstJoint) ∧ Producer.jointClosure := by
  refine ⟨jointRuntimeFace_factorizes jointRuntimeSeed .firstJoint, ?_⟩
  rcases jointRuntimeFacade.readoutAt jointRuntimeSeed .firstJoint with ⟨_, delivered⟩ | inactive
  · exact delivered.down
  · exact PEmpty.elim inactive

theorem jointRuntime_nextJoint_inactive (runtime : LivingRuntimeState jointRuntimeProcess) :
    jointRuntimeFacade.readoutAt runtime.tick.next .firstJoint =
      (.inr PUnit.unit : SourceNativeProjectionFiberAt jointProjectionLaw .firstJoint (jointEmitted runtime.tick.next.state.current)) := rfl

theorem jointRuntime_next_readonly (runtime : LivingRuntimeState jointRuntimeProcess) :
    jointNext runtime.tick.next.state.current = runtime.tick.next.state.current ∧
      IsEmpty (JointV.NativeWriteAt runtime.tick.next.state.current) := ⟨rfl, ⟨fun write => nomatch write⟩⟩

theorem jointRuntime_readiness_installed (runtime : LivingRuntimeState jointRuntimeProcess) :
    jointRuntimeFacade.readoutAt runtime.tick.next .readiness =
      (.inl ⟨PUnit.unit, (jointSourceResult,
        ⟨(jointRuntime_next_readonly runtime).1, (jointRuntime_next_readonly runtime).2⟩)⟩ :
        SourceNativeProjectionFiberAt jointProjectionLaw .readiness (jointEmitted runtime.tick.next.state.current)) := by
  rw [← jointRuntime_response runtime]
  rfl

theorem jointRuntime_wholeLedger_installed (runtime : LivingRuntimeState jointRuntimeProcess) :
    jointRuntimeFacade.readoutAt runtime .wholeLedger =
      (.inl ⟨PUnit.unit, jointLedgerCompiler.compile (jointEmitted runtime.state.current)⟩ :
        SourceNativeProjectionFiberAt jointProjectionLaw .wholeLedger (jointEmitted runtime.state.current)) := rfl

end
end LAlanine40K2025.JointNext.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
