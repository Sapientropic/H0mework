import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Runtime.ReservoirIngress

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion
open Recovery.Runtime Charging.Runtime
noncomputable section

structure ReservoirActionReceiptAt
    (event : ExactTemporalCausalRootEventAt recoveryLivingRoot.toAuthoritativeRoot.toLedgerRoot chargingParentVisit)
    (answer : Current.State) : Type 3 where
  sourceExact : event = chargingParentEvent
  actualAnswer : answer = reservoirCurrentState reservoirFirstSuccessor.targetCurrent
  receivedBody : Incidence.bodyRead Current.initial.joint =
    (recoveryCurrentState recoveryRuntimeAfterFirst.state.current).joint
  controlClosure : type_of% Producer.sourceGeneratedFiniteReservoir
  bodyReadoutKernel : type_of% BodyKernel.sourceGeneratedBodyReadoutKernel
  bodyMeasurement : type_of% Measurement.sourceGeneratedBodyMeasurement
  netAccount :
    (Thermo.freeEnergy answer - Thermo.freeEnergy Current.initial) +
      (Current.entropyProduction answer - Current.entropyProduction Current.initial) = Physical.sourceWork Current.initial

def reservoirActionTargetAt
    (event : ExactTemporalCausalRootEventAt recoveryLivingRoot.toAuthoritativeRoot.toLedgerRoot chargingParentVisit) :
    SourceNativeSequentialActualActionTargetAt recoveryLivingRoot chargingParentVisit event
      chargingParentEntry chargingParentAuthority := by
  rw [event.eq_generated]
  exact
    { TargetN := RecoveryN
      translation := chargingTranslation
      TargetV := ReservoirV
      targetRoot := reservoirLivingRoot
      targetTheory := TheoryState.rootSemantic RecoveryN
      lawSurface_heq := HEq.rfl
      targetTheory_rootSemantic := { compile := id, commuting := fun _ => rfl }
      occurrencePresentation := reservoirOccurrencePresentation
      occurrence_commutes := rfl
      initialSupport_heq := HEq.rfl
      initialOpenLedger := chargingTranslation.oldOpenLedger chargingSourceSupport
      initialOpenLedger_heq := HEq.rfl
      initialLedger_responsibility_commutes := fun _ => rfl
      initialLedger_claim_commutes := fun _ => rfl
      initialLedger_budget_conservative := fun _ => Nat.le_refl _
      initialLedgerNoFresh := chargingIngress_no_fresh_rows _
      translatedSourceEntryRow := by
        rw [reservoirTranslatedEntry_exact]
        exact reservoirInitialEntryRow
      firstSuccessor := reservoirFirstSuccessor
      canonical_targetNextVisit_eq := rfl
      Answer := Current.State
      answer := reservoirCurrentState reservoirFirstSuccessor.targetCurrent
      Receipt := ReservoirActionReceiptAt chargingParentEvent
      receipt :=
        { sourceExact := rfl
          actualAnswer := rfl
          receivedBody := Current.initial_body
          controlClosure := Producer.sourceGeneratedFiniteReservoir
          bodyReadoutKernel := BodyKernel.sourceGeneratedBodyReadoutKernel
          bodyMeasurement := Measurement.sourceGeneratedBodyMeasurement
          netAccount := Thermo.supply_net_account Current.initial } }

def reservoirActionProgram : SourceNativeSequentialActualActionProgramAt recoveryLivingRoot chargingParentVisit
    chargingParentEntry chargingParentAuthority where
  targetAt := reservoirActionTargetAt

def generatedReservoirAction : SourceGeneratedSequentialActualActionAt reservoirActionProgram chargingParentEvent :=
  reservoirActionProgram.generate chargingParentEvent

theorem generatedReservoirAction_answer : generatedReservoirAction.answer = Current.supplyNext Current.initial := rfl

def generatedReservoirAction_receipt : ReservoirActionReceiptAt chargingParentEvent (Current.supplyNext Current.initial) :=
  generatedReservoirAction.receipt

theorem generatedReservoirAction_next : generatedReservoirAction.target.targetAnswerAndNext.nextCurrent =
    ⟨ReservoirV, reservoirAuthoritativeRoot, generatedReservoirAction.target.targetVisit⟩ :=
  generatedReservoirAction.target.targetAnswerAndNext_next_eq

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
