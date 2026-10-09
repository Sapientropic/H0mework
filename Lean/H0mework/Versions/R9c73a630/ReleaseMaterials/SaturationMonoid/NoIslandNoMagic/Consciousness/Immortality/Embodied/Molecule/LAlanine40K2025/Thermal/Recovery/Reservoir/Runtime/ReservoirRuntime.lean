import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Runtime.ReservoirProgram

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Recovery.Runtime Propagation.Producer
noncomputable section

def reservoirProcessCurrent (visit : RootVisit reservoirLivingRoot.toAuthoritativeRoot.toRoot) :
    SourceNativeLivingRootCurrentAt RecoveryN := ⟨ReservoirV, reservoirLivingRoot, .finite visit⟩

def reservoirRuntimeProcess : SourceNativeLivingRootProcess RecoveryN where
  State := RootVisit reservoirLivingRoot.toAuthoritativeRoot.toRoot
  stateAt := reservoirProcessCurrent
  stateAt_injective := by
    intro left right equality
    change (⟨ReservoirV, reservoirLivingRoot, .finite left⟩ : SourceNativeLivingRootCurrentAt RecoveryN) =
      ⟨ReservoirV, reservoirLivingRoot, .finite right⟩ at equality
    injection equality with _ _ visitEq
    exact SourceNativeTemporalVisitAt.finite_injective visitEq
  initial := reservoirLivingRoot.toAuthoritativeRoot.toRoot.initialVisit
  successorAt := fun visit => ⟨visit.next rfl, rfl, HEq.rfl⟩

def reservoirRuntimeFacade : SourceNativeLivingRuntimeFacade RecoveryN where
  process := reservoirRuntimeProcess
  FaceAt := fun _ => ReservoirProjection
  componentAt := fun _ _ => reservoirProjectionLaw
  installationAt := fun _ _ => .ofEq rfl
  projectionAt := fun _ projection => projection

def reservoirRuntimeSeed : LivingRuntimeState reservoirRuntimeProcess := reservoirRuntimeFacade.seed
def reservoirRuntimeAfterFirst : LivingRuntimeState reservoirRuntimeProcess := reservoirRuntimeSeed.tick.next

theorem reservoirRuntimeFirst_generated :
    reservoirCurrentState reservoirRuntimeAfterFirst.state.current = generatedReservoirAction.answer := rfl

theorem reservoirRuntimeNext_joint (runtime : LivingRuntimeState reservoirRuntimeProcess) :
    (reservoirCurrentState runtime.tick.next.state.current).joint =
      Quantum.conjugation (reservoirControlRead runtime.state.current).action (reservoirCurrentState runtime.state.current).joint :=
  reservoirNext_joint runtime.state.current

theorem reservoirRuntime_next_is_load (runtime : LivingRuntimeState reservoirRuntimeProcess) :
    reservoirCurrentState runtime.tick.next.tick.next.state.current =
      Current.loadNext (reservoirCurrentState runtime.tick.next.state.current) := rfl

theorem reservoirRuntime_nextClock (runtime : LivingRuntimeState reservoirRuntimeProcess) :
    (reservoirCurrentState runtime.tick.next.state.current).localClock =
      (reservoirCurrentState runtime.state.current).localClock + nativeClockStep := reservoirNext_clock runtime.state.current

theorem reservoirRuntime_firstClock :
    (reservoirCurrentState reservoirRuntimeAfterFirst.state.current).localClock = 5 * nativeClockStep := Producer.first_clock

theorem reservoirRuntimeFace_factorizes (runtime : LivingRuntimeState reservoirRuntimeProcess) (projection : ReservoirProjection) :
    type_of% (reservoirRuntimeFacade.readoutAt_factorizes runtime projection) :=
  reservoirRuntimeFacade.readoutAt_factorizes runtime projection

theorem reservoirRuntime_face_is_installed (runtime : LivingRuntimeState reservoirRuntimeProcess) (projection : ReservoirProjection) :
    reservoirRuntimeFacade.readoutAt runtime projection =
      reservoirProjectionLaw.outcomeAt projection (reservoirEmitted runtime.state.current) := rfl

theorem reservoirRuntime_wholeLedger_is_installed (runtime : LivingRuntimeState reservoirRuntimeProcess) :
    reservoirRuntimeFacade.readoutAt runtime .wholeLedger =
      (.inl ⟨PUnit.unit, reservoirLedgerCompiler.compile (reservoirEmitted runtime.state.current)⟩ :
        SourceNativeProjectionFiberAt reservoirProjectionLaw .wholeLedger (reservoirEmitted runtime.state.current)) := rfl

theorem reservoirRuntime_netAccount_is_installed (runtime : LivingRuntimeState reservoirRuntimeProcess) :
    reservoirRuntimeFacade.readoutAt runtime .netAccount =
      (.inl ⟨PUnit.unit, (reservoirEventWork runtime.state.current, reservoirAccumulatedWork runtime.state.current,
        ⟨reservoirNext_netAccount runtime.state.current⟩)⟩ :
        SourceNativeProjectionFiberAt reservoirProjectionLaw .netAccount (reservoirEmitted runtime.state.current)) := rfl

theorem reservoirRuntime_firstSupply_is_installed :
    reservoirRuntimeFacade.readoutAt reservoirRuntimeSeed .firstSupply =
      (.inl ⟨PUnit.unit, ⟨Producer.sourceGeneratedFiniteReservoir, BodyKernel.sourceGeneratedBodyReadoutKernel,
        Measurement.sourceGeneratedBodyMeasurement⟩⟩ :
        SourceNativeProjectionFiberAt reservoirProjectionLaw .firstSupply (reservoirEmitted .ingress)) := rfl

theorem reservoirRuntime_nextSupply_is_inactive (runtime : LivingRuntimeState reservoirRuntimeProcess) :
    reservoirRuntimeFacade.readoutAt runtime.tick.next .firstSupply =
      (.inr PUnit.unit : SourceNativeProjectionFiberAt reservoirProjectionLaw .firstSupply
        (reservoirEmitted runtime.tick.next.state.current)) := rfl

theorem reservoirRuntime_controlCertificate :
    type_of% (reservoirRuntimeFace_factorizes reservoirRuntimeSeed .firstSupply) ∧
      type_of% Producer.sourceGeneratedFiniteReservoir := by
  refine ⟨reservoirRuntimeFace_factorizes reservoirRuntimeSeed .firstSupply, ?_⟩
  rcases reservoirRuntimeFacade.readoutAt reservoirRuntimeSeed .firstSupply with ⟨_, delivered⟩ | inactive
  · exact delivered.down.1
  · exact PEmpty.elim inactive

theorem reservoirRuntime_bodyKernelCertificate :
    type_of% (reservoirRuntimeFace_factorizes reservoirRuntimeSeed .firstSupply) ∧
      type_of% BodyKernel.sourceGeneratedBodyReadoutKernel := by
  refine ⟨reservoirRuntimeFace_factorizes reservoirRuntimeSeed .firstSupply, ?_⟩
  rcases reservoirRuntimeFacade.readoutAt reservoirRuntimeSeed .firstSupply with ⟨_, delivered⟩ | inactive
  · exact delivered.down.2.1
  · exact PEmpty.elim inactive

theorem reservoirRuntime_body_consumer (consumer : BodyKernel.bodyConsumers.Consumer) :
    BodyKernel.source_body_kernel_exact.factor consumer
      ⟨Incidence.bodyRead (reservoirCurrentState reservoirRuntimeAfterFirst.state.current).joint,
        Source.received.joint, BodyKernel.sourceBodyChannel_actual⟩ =
      BodyKernel.bodyConsumers.read consumer Source.received.joint :=
  reservoirRuntime_bodyKernelCertificate.2.2.2.2 consumer

theorem reservoirRuntime_strict_gains :
    6 < Readout.pcEnergy (reservoirCurrentState reservoirRuntimeAfterFirst.state.current) -
      Readout.pcEnergy (reservoirCurrentState reservoirRuntimeSeed.state.current) ∧
    6 < Readout.pcCapacity (reservoirCurrentState reservoirRuntimeAfterFirst.state.current) -
      Readout.pcCapacity (reservoirCurrentState reservoirRuntimeSeed.state.current) ∧
    6 < Readout.donorEnergy (reservoirCurrentState reservoirRuntimeSeed.state.current) -
      Readout.donorEnergy (reservoirCurrentState reservoirRuntimeAfterFirst.state.current) := by
  rcases reservoirRuntime_controlCertificate.2 with ⟨_, _, _, _, _, gain, capacity, debit, _⟩
  exact ⟨gain, capacity, debit⟩

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
