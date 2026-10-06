import H0mework.Versions.AB.Chemistry.LAlanineInertia.RuntimeInertiaAction

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Inertia.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root
noncomputable section

def inertiaProcessCurrent (visit : RootVisit inertiaLivingRoot.toAuthoritativeRoot.toRoot) :
    SourceNativeLivingRootCurrentAt N := ⟨InertiaV, inertiaLivingRoot, .finite visit⟩

def inertiaRuntimeProcess : SourceNativeLivingRootProcess N where
  State := RootVisit inertiaLivingRoot.toAuthoritativeRoot.toRoot
  stateAt := inertiaProcessCurrent
  stateAt_injective := by
    intro left right equality
    change (⟨InertiaV, inertiaLivingRoot, .finite left⟩ : SourceNativeLivingRootCurrentAt N) =
      ⟨InertiaV, inertiaLivingRoot, .finite right⟩ at equality
    injection equality with _ _ visitEq
    exact SourceNativeTemporalVisitAt.finite_injective visitEq
  initial := inertiaLivingRoot.toAuthoritativeRoot.toRoot.initialVisit
  successorAt := by
    intro visit
    refine ⟨visit.next (inertiaCompiled_next visit.current), ?_, ?_⟩
    · rcases visit with ⟨current, history⟩
      cases current <;> rfl
    · rcases visit with ⟨current, history⟩
      cases current <;> exact HEq.rfl

def inertiaRuntimeFacade : SourceNativeLivingRuntimeFacade N where
  process := inertiaRuntimeProcess
  FaceAt := fun _ => InertiaProjection
  componentAt := fun _ _ => inertiaProjectionLaw
  installationAt := fun _ _ => .ofEq rfl
  projectionAt := fun _ projection => projection

def inertiaRuntimeSeed : LivingRuntimeState inertiaRuntimeProcess := inertiaRuntimeFacade.seed
def inertiaRuntimeAfterFirst : LivingRuntimeState inertiaRuntimeProcess := inertiaRuntimeSeed.tick.next

theorem inertiaRuntime_material_source (runtime : LivingRuntimeState inertiaRuntimeProcess) :
    inertiaReadout runtime.state.current = Source.stepReadout := by
  have keeps : ∀ {state : inertiaRuntimeProcess.State}, SourceNativeRuntimeReachableAt inertiaRuntimeProcess state →
      inertiaReadout state.current = Source.stepReadout := by
    intro state reachable
    induction reachable with
    | initial => rfl
    | step prior kept => exact kept
  exact keeps runtime.reachable

theorem inertiaRuntime_nextClock (runtime : LivingRuntimeState inertiaRuntimeProcess) :
    inertiaPhysicalTime runtime.tick.next.state.current = Propagation.Producer.nativeClockStep := by
  change (inertiaReadout runtime.state.current).duration = _
  rw [inertiaRuntime_material_source]
  exact Producer.duration_eq_nativeClock

theorem inertiaRuntimeFirst_generated :
    inertiaReadout inertiaRuntimeAfterFirst.state.current = generatedInertiaAction.answer := rfl

theorem inertiaRuntime_firstFrame : inertiaFrame inertiaRuntimeAfterFirst.state.current = Source.stepReadout.target := rfl

theorem inertiaRuntime_firstEnergyLedger :
    inertiaCurrentLedger inertiaRuntimeAfterFirst.state.current = Source.stepReadout.targetLedger := rfl

theorem inertiaRuntime_firstClock : inertiaPhysicalTime inertiaRuntimeAfterFirst.state.current =
    Propagation.Producer.nativeClockStep := Producer.duration_eq_nativeClock

theorem inertiaRuntimeFace_factorizes (runtime : LivingRuntimeState inertiaRuntimeProcess) (projection : InertiaProjection) :
    type_of% (inertiaRuntimeFacade.readoutAt_factorizes runtime projection) :=
  inertiaRuntimeFacade.readoutAt_factorizes runtime projection

theorem inertiaRuntime_face_installed (runtime : LivingRuntimeState inertiaRuntimeProcess) (projection : InertiaProjection) :
    inertiaRuntimeFacade.readoutAt runtime projection =
      inertiaProjectionLaw.outcomeAt projection (inertiaEmitted runtime.state.current) := rfl

theorem inertiaRuntime_firstStep_installed :
    inertiaRuntimeFacade.readoutAt inertiaRuntimeSeed .firstStep =
      (.inl ⟨PUnit.unit, ⟨Producer.sourceGeneratedFirstStep⟩⟩ :
        SourceNativeProjectionFiberAt inertiaProjectionLaw .firstStep (inertiaEmitted .ingress)) := rfl

theorem inertiaRuntime_sourceCertificate :
    type_of% (inertiaRuntimeFace_factorizes inertiaRuntimeSeed .firstStep) ∧ Producer.firstStepClosure := by
  refine ⟨inertiaRuntimeFace_factorizes inertiaRuntimeSeed .firstStep, ?_⟩
  rcases inertiaRuntimeFacade.readoutAt inertiaRuntimeSeed .firstStep with ⟨_, delivered⟩ | inactive
  · exact delivered.down
  · exact PEmpty.elim inactive

theorem inertiaRuntime_nextStep_inactive (runtime : LivingRuntimeState inertiaRuntimeProcess) :
    inertiaRuntimeFacade.readoutAt runtime.tick.next .firstStep =
      (.inr PUnit.unit : SourceNativeProjectionFiberAt inertiaProjectionLaw .firstStep
        (inertiaEmitted runtime.tick.next.state.current)) := rfl

theorem inertiaRuntime_next_readonly (runtime : LivingRuntimeState inertiaRuntimeProcess) :
    inertiaNext runtime.tick.next.state.current = runtime.tick.next.state.current ∧
      inertiaPhysicalTime runtime.tick.next.tick.next.state.current = inertiaPhysicalTime runtime.tick.next.state.current ∧
      IsEmpty (InertiaV.NativeWriteAt runtime.tick.next.state.current) :=
  ⟨rfl, rfl, inertiaReadiness_no_native_write _⟩

theorem inertiaRuntime_readiness_installed (runtime : LivingRuntimeState inertiaRuntimeProcess) :
    inertiaRuntimeFacade.readoutAt runtime.tick.next .readiness =
      (.inl ⟨PUnit.unit, (inertiaReadout runtime.state.current,
        ⟨rfl, rfl, inertiaReadiness_no_native_write _⟩)⟩ :
        SourceNativeProjectionFiberAt inertiaProjectionLaw .readiness (inertiaEmitted runtime.tick.next.state.current)) := rfl

theorem inertiaRuntime_readonly_mode (runtime : LivingRuntimeState inertiaRuntimeProcess) :
    (inertiaSource.toRootSource.actual.compile (inertiaEmitted runtime.tick.next.state.current)).kind =
      .continuedTransport := rfl

theorem inertiaRuntime_wholeLedger_installed (runtime : LivingRuntimeState inertiaRuntimeProcess) :
    inertiaRuntimeFacade.readoutAt runtime .wholeLedger =
      (.inl ⟨PUnit.unit, inertiaLedgerCompiler.compile (inertiaEmitted runtime.state.current)⟩ :
        SourceNativeProjectionFiberAt inertiaProjectionLaw .wholeLedger (inertiaEmitted runtime.state.current)) := rfl

end
end LAlanine40K2025.Inertia.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
