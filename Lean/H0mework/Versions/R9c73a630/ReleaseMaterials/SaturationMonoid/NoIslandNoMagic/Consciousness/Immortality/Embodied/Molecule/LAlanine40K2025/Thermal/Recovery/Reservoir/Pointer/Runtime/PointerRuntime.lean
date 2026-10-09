import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Runtime.PointerProgram

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Recovery.Runtime Propagation.Producer
noncomputable section

def pointerProcessCurrent (visit : RootVisit pointerLivingRoot.toAuthoritativeRoot.toRoot) :
    SourceNativeLivingRootCurrentAt RecoveryN := ⟨PointerV, pointerLivingRoot, .finite visit⟩

def pointerRuntimeProcess : SourceNativeLivingRootProcess RecoveryN where
  State := RootVisit pointerLivingRoot.toAuthoritativeRoot.toRoot
  stateAt := pointerProcessCurrent
  stateAt_injective := by
    intro left right equality
    change (⟨PointerV, pointerLivingRoot, .finite left⟩ : SourceNativeLivingRootCurrentAt RecoveryN) =
      ⟨PointerV, pointerLivingRoot, .finite right⟩ at equality
    injection equality with _ _ visitEq
    exact SourceNativeTemporalVisitAt.finite_injective visitEq
  initial := pointerLivingRoot.toAuthoritativeRoot.toRoot.initialVisit
  successorAt := fun visit => ⟨visit.next rfl, rfl, HEq.rfl⟩

def pointerRuntimeFacade : SourceNativeLivingRuntimeFacade RecoveryN where
  process := pointerRuntimeProcess
  FaceAt := fun _ => PointerProjection
  componentAt := fun _ _ => pointerProjectionLaw
  installationAt := fun _ _ => .ofEq rfl
  projectionAt := fun _ projection => projection

def pointerRuntimeSeed : LivingRuntimeState pointerRuntimeProcess := pointerRuntimeFacade.seed
def pointerRuntimeAfterFirst : LivingRuntimeState pointerRuntimeProcess := pointerRuntimeSeed.tick.next

theorem pointerRuntimeFirst_generated :
    pointerCurrentState pointerRuntimeAfterFirst.state.current = generatedPointerAction.answer := rfl

theorem pointerRuntimeNext_joint (runtime : LivingRuntimeState pointerRuntimeProcess) :
    (pointerCurrentState runtime.tick.next.state.current).joint =
      Quantum.conjugation (pointerControlRead runtime.state.current).action (pointerCurrentState runtime.state.current).joint := by
  exact (pointerNext_joint runtime.state.current).trans
    (congrArg (fun U => Quantum.conjugation U (pointerCurrentState runtime.state.current).joint)
      (pointerControl_action runtime.state.current).symm)

theorem pointerRuntime_next_is_load (runtime : LivingRuntimeState pointerRuntimeProcess) :
    pointerCurrentState runtime.tick.next.tick.next.state.current =
      Live.loadNext (pointerCurrentState runtime.tick.next.state.current) := rfl

theorem pointerRuntime_nextClock (runtime : LivingRuntimeState pointerRuntimeProcess) :
    (pointerCurrentState runtime.tick.next.state.current).localClock =
      (pointerCurrentState runtime.state.current).localClock + nativeClockStep := pointerNext_clock runtime.state.current

theorem pointerRuntime_firstClock :
    (pointerCurrentState pointerRuntimeAfterFirst.state.current).localClock = 6 * nativeClockStep := Live.first_clock

theorem pointerRuntimeFace_factorizes (runtime : LivingRuntimeState pointerRuntimeProcess) (projection : PointerProjection) :
    type_of% (pointerRuntimeFacade.readoutAt_factorizes runtime projection) :=
  pointerRuntimeFacade.readoutAt_factorizes runtime projection

theorem pointerRuntime_face_is_installed (runtime : LivingRuntimeState pointerRuntimeProcess) (projection : PointerProjection) :
    pointerRuntimeFacade.readoutAt runtime projection =
      pointerProjectionLaw.outcomeAt projection (pointerEmitted runtime.state.current) := rfl

theorem pointerRuntime_wholeLedger_is_installed (runtime : LivingRuntimeState pointerRuntimeProcess) :
    pointerRuntimeFacade.readoutAt runtime .wholeLedger =
      (.inl ⟨PUnit.unit, pointerLedgerCompiler.compile (pointerEmitted runtime.state.current)⟩ :
        SourceNativeProjectionFiberAt pointerProjectionLaw .wholeLedger (pointerEmitted runtime.state.current)) := rfl

theorem pointerRuntime_netAccount_is_installed (runtime : LivingRuntimeState pointerRuntimeProcess) :
    pointerRuntimeFacade.readoutAt runtime .netAccount =
      (.inl ⟨PUnit.unit, (pointerEventWork runtime.state.current, pointerAccumulatedWork runtime.state.current,
        ⟨pointerNext_netAccount runtime.state.current⟩)⟩ :
        SourceNativeProjectionFiberAt pointerProjectionLaw .netAccount (pointerEmitted runtime.state.current)) := rfl

theorem pointerRuntime_firstMeasurement_is_installed :
    pointerRuntimeFacade.readoutAt pointerRuntimeSeed .firstMeasurement =
      (.inl ⟨PUnit.unit, ⟨sourceGeneratedPointerInstrument⟩⟩ :
        SourceNativeProjectionFiberAt pointerProjectionLaw .firstMeasurement (pointerEmitted .ingress)) := rfl

theorem pointerRuntime_nextMeasurement_is_inactive (runtime : LivingRuntimeState pointerRuntimeProcess) :
    pointerRuntimeFacade.readoutAt runtime.tick.next .firstMeasurement =
      (.inr PUnit.unit : SourceNativeProjectionFiberAt pointerProjectionLaw .firstMeasurement
        (pointerEmitted runtime.tick.next.state.current)) := rfl

theorem pointerRuntime_instrumentCertificate :
    type_of% (pointerRuntimeFace_factorizes pointerRuntimeSeed .firstMeasurement) ∧
      type_of% sourceGeneratedPointerInstrument := by
  refine ⟨pointerRuntimeFace_factorizes pointerRuntimeSeed .firstMeasurement, ?_⟩
  rcases pointerRuntimeFacade.readoutAt pointerRuntimeSeed .firstMeasurement with ⟨_, delivered⟩ | inactive
  · exact delivered.down
  · exact PEmpty.elim inactive

theorem pointerRuntime_memory :
    Measurement.sourceMeasurementDecode Load.Source.loadTotalHamiltonian
      (zeroRead (pointerCurrentState pointerRuntimeAfterFirst.state.current).joint) =
        Collision.energy Load.Source.loadTotalHamiltonian Source.received.joint := by
  change Measurement.sourceMeasurementDecode Load.Source.loadTotalHamiltonian (zeroRead Live.first.joint) = _
  rw [Live.first_joint]
  exact pointerRuntime_instrumentCertificate.2.2.2.2.1

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
