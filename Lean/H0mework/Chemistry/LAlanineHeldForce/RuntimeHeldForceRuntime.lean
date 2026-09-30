import H0mework.Chemistry.LAlanineHeldForce.RuntimeHeldForceAction

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.HeldForce.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root Propagation.Interface
noncomputable section

def heldForceProcessCurrent (visit : RootVisit heldForceLivingRoot.toAuthoritativeRoot.toRoot) :
    SourceNativeLivingRootCurrentAt N := ⟨HeldForceV, heldForceLivingRoot, .finite visit⟩

def heldForceRuntimeProcess : SourceNativeLivingRootProcess N where
  State := RootVisit heldForceLivingRoot.toAuthoritativeRoot.toRoot
  stateAt := heldForceProcessCurrent
  stateAt_injective := by
    intro left right equality
    change (⟨HeldForceV, heldForceLivingRoot, .finite left⟩ : SourceNativeLivingRootCurrentAt N) =
      ⟨HeldForceV, heldForceLivingRoot, .finite right⟩ at equality
    injection equality with _ _ visitEq
    exact SourceNativeTemporalVisitAt.finite_injective visitEq
  initial := heldForceLivingRoot.toAuthoritativeRoot.toRoot.initialVisit
  successorAt := by
    intro visit
    refine ⟨visit.next (heldForceCompiled_next visit.current), ?_, ?_⟩
    · rcases visit with ⟨current, history⟩
      cases current <;> rfl
    · rcases visit with ⟨current, history⟩
      cases current <;> exact HEq.rfl

def heldForceRuntimeFacade : SourceNativeLivingRuntimeFacade N where
  process := heldForceRuntimeProcess
  FaceAt := fun _ => HeldForceProjection
  componentAt := fun _ _ => heldForceProjectionLaw
  installationAt := fun _ _ => .ofEq rfl
  projectionAt := fun _ projection => projection

def heldForceRuntimeSeed : LivingRuntimeState heldForceRuntimeProcess := heldForceRuntimeFacade.seed
def heldForceRuntimeAfterFirst : LivingRuntimeState heldForceRuntimeProcess := heldForceRuntimeSeed.tick.next

theorem heldForceRuntime_response (runtime : LivingRuntimeState heldForceRuntimeProcess) :
    heldForceResponse runtime.state.current = heldForceSourceResult := by
  have keeps : ∀ {state : heldForceRuntimeProcess.State}, SourceNativeRuntimeReachableAt heldForceRuntimeProcess state →
      heldForceResponse state.current = heldForceSourceResult := by
    intro state reachable
    induction reachable with
    | initial => rfl
    | step prior kept => exact kept
  exact keeps runtime.reachable

theorem heldForceRuntime_ready_exact (runtime : LivingRuntimeState heldForceRuntimeProcess)
    (response : HeldForceResult) (ready : runtime.state.current = .ready response) :
    response = heldForceSourceResult := by
  have generated := heldForceRuntime_response runtime
  rw [ready] at generated
  exact generated

theorem heldForceRuntime_nextCurrent (runtime : LivingRuntimeState heldForceRuntimeProcess) :
    runtime.tick.next.state.current = .ready heldForceSourceResult :=
  congrArg HeldForceCurrent.ready (heldForceRuntime_response runtime)

theorem heldForceRuntime_held (runtime : LivingRuntimeState heldForceRuntimeProcess) :
    heldForceHeld runtime.state.current = Producer.exactHeld := by
  have retained : heldForceHeld runtime.state.current = (heldForceResponse runtime.state.current).held := by
    cases runtime.state.current <;> rfl
  rw [retained, heldForceRuntime_response]
  rfl

theorem heldForceRuntimeFirst_generated :
    heldForceResponse heldForceRuntimeAfterFirst.state.current = generatedHeldForceAction.answer := rfl

theorem heldForceRuntime_clock (runtime : LivingRuntimeState heldForceRuntimeProcess) :
    heldForcePhysicalTime runtime.state.current = Propagation.Producer.nativeClockStep := heldForcePhysicalTime_eq _

theorem heldForceRuntimeFace_factorizes (runtime : LivingRuntimeState heldForceRuntimeProcess)
    (projection : HeldForceProjection) : type_of% (heldForceRuntimeFacade.readoutAt_factorizes runtime projection) :=
  heldForceRuntimeFacade.readoutAt_factorizes runtime projection

theorem heldForceRuntime_face_installed (runtime : LivingRuntimeState heldForceRuntimeProcess)
    (projection : HeldForceProjection) : heldForceRuntimeFacade.readoutAt runtime projection =
      heldForceProjectionLaw.outcomeAt projection (heldForceEmitted runtime.state.current) := rfl

theorem heldForceRuntime_sourceCertificate :
    type_of% (heldForceRuntimeFace_factorizes heldForceRuntimeSeed .firstForce) ∧ Producer.heldForceClosure := by
  refine ⟨heldForceRuntimeFace_factorizes heldForceRuntimeSeed .firstForce, ?_⟩
  rcases heldForceRuntimeFacade.readoutAt heldForceRuntimeSeed .firstForce with ⟨_, delivered⟩ | inactive
  · exact delivered.down
  · exact PEmpty.elim inactive

theorem heldForceRuntime_nextForce_inactive (runtime : LivingRuntimeState heldForceRuntimeProcess) :
    heldForceRuntimeFacade.readoutAt runtime.tick.next .firstForce =
      (.inr PUnit.unit : SourceNativeProjectionFiberAt heldForceProjectionLaw .firstForce
        (heldForceEmitted runtime.tick.next.state.current)) := rfl

theorem heldForceRuntime_next_readonly (runtime : LivingRuntimeState heldForceRuntimeProcess) :
    heldForceNext runtime.tick.next.state.current = runtime.tick.next.state.current ∧
      IsEmpty (HeldForceV.NativeWriteAt runtime.tick.next.state.current) :=
  ⟨rfl, ⟨fun write => nomatch write⟩⟩

theorem heldForceRuntime_readiness_installed (runtime : LivingRuntimeState heldForceRuntimeProcess) :
    heldForceRuntimeFacade.readoutAt runtime.tick.next .readiness =
      (.inl ⟨PUnit.unit, (heldForceSourceResult,
        ⟨(heldForceRuntime_next_readonly runtime).1, (heldForceRuntime_next_readonly runtime).2⟩)⟩ :
        SourceNativeProjectionFiberAt heldForceProjectionLaw .readiness
          (heldForceEmitted runtime.tick.next.state.current)) := by
  rw [← heldForceRuntime_response runtime]
  rfl

theorem heldForceRuntime_wholeLedger_installed (runtime : LivingRuntimeState heldForceRuntimeProcess) :
    heldForceRuntimeFacade.readoutAt runtime .wholeLedger =
      (.inl ⟨PUnit.unit, heldForceLedgerCompiler.compile (heldForceEmitted runtime.state.current)⟩ :
        SourceNativeProjectionFiberAt heldForceProjectionLaw .wholeLedger (heldForceEmitted runtime.state.current)) := rfl

end
end LAlanine40K2025.HeldForce.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
