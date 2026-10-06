import H0mework.Versions.AB.Chemistry.LAlanineElectronicFrame.RuntimeElectronicFrameAction

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.ElectronicFrame.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root Propagation.Interface
noncomputable section

def electronicFrameProcessCurrent (visit : RootVisit electronicFrameLivingRoot.toAuthoritativeRoot.toRoot) :
    SourceNativeLivingRootCurrentAt N := ⟨ElectronicFrameV, electronicFrameLivingRoot, .finite visit⟩

def electronicFrameRuntimeProcess : SourceNativeLivingRootProcess N where
  State := RootVisit electronicFrameLivingRoot.toAuthoritativeRoot.toRoot
  stateAt := electronicFrameProcessCurrent
  stateAt_injective := by
    intro left right equality
    change (⟨ElectronicFrameV, electronicFrameLivingRoot, .finite left⟩ : SourceNativeLivingRootCurrentAt N) =
      ⟨ElectronicFrameV, electronicFrameLivingRoot, .finite right⟩ at equality
    injection equality with _ _ visitEq
    exact SourceNativeTemporalVisitAt.finite_injective visitEq
  initial := electronicFrameLivingRoot.toAuthoritativeRoot.toRoot.initialVisit
  successorAt := by
    intro visit
    refine ⟨visit.next (electronicFrameCompiled_next visit.current), ?_, ?_⟩
    · rcases visit with ⟨current, history⟩
      cases current <;> rfl
    · rcases visit with ⟨current, history⟩
      cases current <;> exact HEq.rfl

def electronicFrameRuntimeFacade : SourceNativeLivingRuntimeFacade N where
  process := electronicFrameRuntimeProcess
  FaceAt := fun _ => ElectronicFrameProjection
  componentAt := fun _ _ => electronicFrameProjectionLaw
  installationAt := fun _ _ => .ofEq rfl
  projectionAt := fun _ projection => projection

def electronicFrameRuntimeSeed : LivingRuntimeState electronicFrameRuntimeProcess := electronicFrameRuntimeFacade.seed
def electronicFrameRuntimeAfterFirst : LivingRuntimeState electronicFrameRuntimeProcess := electronicFrameRuntimeSeed.tick.next

theorem electronicFrameRuntime_nextHeld (runtime : LivingRuntimeState electronicFrameRuntimeProcess) :
    electronicFrameHeld runtime.tick.next.state.current = Source.heldStateTransport Producer.heldMatrix := by
  have keeps : ∀ {state : electronicFrameRuntimeProcess.State}, SourceNativeRuntimeReachableAt electronicFrameRuntimeProcess state →
      electronicFrameHeld (electronicFrameNext state.current) = Source.heldStateTransport Producer.heldMatrix := by
    intro state reachable
    induction reachable with
    | initial => rfl
    | @step state prior kept =>
        change electronicFrameHeld (electronicFrameNext (electronicFrameNext state.current)) = _
        exact (congrArg electronicFrameHeld (electronicFrameNext_idempotent state.current)).trans kept
  exact keeps runtime.reachable

theorem electronicFrameRuntime_ready_exact (runtime : LivingRuntimeState electronicFrameRuntimeProcess)
    (held : Matrix Basis Basis ℂ) (ready : runtime.state.current = .ready held) :
    held = Source.heldStateTransport Producer.heldMatrix := by
  have generated := electronicFrameRuntime_nextHeld runtime
  change electronicFrameHeld (electronicFrameNext runtime.state.current) = _ at generated
  rw [ready] at generated
  exact generated

theorem electronicFrameRuntime_nextCurrent (runtime : LivingRuntimeState electronicFrameRuntimeProcess) :
    runtime.tick.next.state.current = .ready (Source.heldStateTransport Producer.heldMatrix) := by
  change electronicFrameNext runtime.state.current = _
  cases ready : runtime.state.current with
  | ingress => rfl
  | ready held => exact congrArg ElectronicFrameCurrent.ready (electronicFrameRuntime_ready_exact runtime held ready)

theorem electronicFrameRuntimeFirst_generated :
    electronicFrameHeld electronicFrameRuntimeAfterFirst.state.current = generatedElectronicFrameAction.answer := rfl

theorem electronicFrameRuntime_clock (runtime : LivingRuntimeState electronicFrameRuntimeProcess) :
    electronicFramePhysicalTime runtime.state.current = Propagation.Producer.nativeClockStep :=
  electronicFramePhysicalTime_eq _

theorem electronicFrameRuntimeFace_factorizes (runtime : LivingRuntimeState electronicFrameRuntimeProcess)
    (projection : ElectronicFrameProjection) :
    type_of% (electronicFrameRuntimeFacade.readoutAt_factorizes runtime projection) :=
  electronicFrameRuntimeFacade.readoutAt_factorizes runtime projection

theorem electronicFrameRuntime_face_installed (runtime : LivingRuntimeState electronicFrameRuntimeProcess)
    (projection : ElectronicFrameProjection) : electronicFrameRuntimeFacade.readoutAt runtime projection =
      electronicFrameProjectionLaw.outcomeAt projection (electronicFrameEmitted runtime.state.current) := rfl

theorem electronicFrameRuntime_firstFrame_installed :
    electronicFrameRuntimeFacade.readoutAt electronicFrameRuntimeSeed .firstFrame =
      (.inl ⟨PUnit.unit, ⟨Producer.sourceGeneratedElectronicFrame⟩⟩ :
        SourceNativeProjectionFiberAt electronicFrameProjectionLaw .firstFrame (electronicFrameEmitted .ingress)) := rfl

theorem electronicFrameRuntime_sourceCertificate :
    type_of% (electronicFrameRuntimeFace_factorizes electronicFrameRuntimeSeed .firstFrame) ∧ Producer.frameClosure := by
  refine ⟨electronicFrameRuntimeFace_factorizes electronicFrameRuntimeSeed .firstFrame, ?_⟩
  rcases electronicFrameRuntimeFacade.readoutAt electronicFrameRuntimeSeed .firstFrame with ⟨_, delivered⟩ | inactive
  · exact delivered.down
  · exact PEmpty.elim inactive

theorem electronicFrameRuntime_nextFrame_inactive (runtime : LivingRuntimeState electronicFrameRuntimeProcess) :
    electronicFrameRuntimeFacade.readoutAt runtime.tick.next .firstFrame =
      (.inr PUnit.unit : SourceNativeProjectionFiberAt electronicFrameProjectionLaw .firstFrame
        (electronicFrameEmitted runtime.tick.next.state.current)) := rfl

theorem electronicFrameRuntime_next_readonly (runtime : LivingRuntimeState electronicFrameRuntimeProcess) :
    electronicFrameNext runtime.tick.next.state.current = runtime.tick.next.state.current ∧
      IsEmpty (ElectronicFrameV.NativeWriteAt runtime.tick.next.state.current) := by
  exact ⟨electronicFrameNext_idempotent runtime.state.current,
    electronicFrameNext_no_native_write runtime.state.current⟩

theorem electronicFrameRuntime_readiness_installed (runtime : LivingRuntimeState electronicFrameRuntimeProcess) :
    electronicFrameRuntimeFacade.readoutAt runtime.tick.next .readiness =
      (.inl ⟨PUnit.unit, (Source.heldStateTransport Producer.heldMatrix,
        ⟨(electronicFrameRuntime_next_readonly runtime).1, (electronicFrameRuntime_next_readonly runtime).2⟩)⟩ :
        SourceNativeProjectionFiberAt electronicFrameProjectionLaw .readiness
          (electronicFrameEmitted runtime.tick.next.state.current)) := by
  have content : electronicFrameWrittenHeld runtime.state.current = Source.heldStateTransport Producer.heldMatrix :=
    electronicFrameRuntime_nextHeld runtime
  rw [← content]
  rfl

theorem electronicFrameRuntime_wholeLedger_installed (runtime : LivingRuntimeState electronicFrameRuntimeProcess) :
    electronicFrameRuntimeFacade.readoutAt runtime .wholeLedger =
      (.inl ⟨PUnit.unit, electronicFrameLedgerCompiler.compile (electronicFrameEmitted runtime.state.current)⟩ :
        SourceNativeProjectionFiberAt electronicFrameProjectionLaw .wholeLedger (electronicFrameEmitted runtime.state.current)) := rfl

end
end LAlanine40K2025.ElectronicFrame.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
