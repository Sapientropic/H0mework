import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Runtime.PointerIngress

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion
open Recovery.Runtime Reservoir.Runtime Charging.Runtime
noncomputable section

structure PointerActionReceiptAt
    (event : ExactTemporalCausalRootEventAt reservoirLivingRoot.toAuthoritativeRoot.toLedgerRoot pointerParentVisit)
    (answer : Live.State) : Type 3 where
  sourceExact : event = pointerParentEvent
  parentRow : pointerParentGenerated.GeneratedEntryRowAt pointerParentEntry
  actualAnswer : answer = pointerCurrentState pointerFirstSuccessor.targetCurrent
  receivedCurrent : received = reservoirCurrentState pointerParentVisit.current
  preparedCurrent : sourceInitial = prepared (reservoirCurrentState pointerParentVisit.current).joint
  instrumentClosure : type_of% sourceGeneratedPointerInstrument
  oldEntropy : type_of% Live.initial_entropyProduction
  oldFreeEnergy : type_of% Live.initial_freeEnergy
  netAccount :
    (Live.freeEnergy answer - Live.freeEnergy Live.initial) +
      (Live.entropyProduction answer - Live.entropyProduction Live.initial) = Live.measurementWork Live.initial

def pointerActionTargetAt
    (event : ExactTemporalCausalRootEventAt reservoirLivingRoot.toAuthoritativeRoot.toLedgerRoot pointerParentVisit) :
    SourceNativeSequentialActualActionTargetAt reservoirLivingRoot pointerParentVisit event
      pointerParentEntry pointerParentAuthority := by
  rw [event.eq_generated]
  exact
    { TargetN := RecoveryN
      translation := chargingTranslation
      TargetV := PointerV
      targetRoot := pointerLivingRoot
      targetTheory := TheoryState.rootSemantic RecoveryN
      lawSurface_heq := HEq.rfl
      targetTheory_rootSemantic := { compile := id, commuting := fun _ => rfl }
      occurrencePresentation := pointerOccurrencePresentation
      occurrence_commutes := rfl
      initialSupport_heq := HEq.rfl
      initialOpenLedger := chargingTranslation.oldOpenLedger reservoirSupport
      initialOpenLedger_heq := HEq.rfl
      initialLedger_responsibility_commutes := fun _ => rfl
      initialLedger_claim_commutes := fun _ => rfl
      initialLedger_budget_conservative := fun _ => Nat.le_refl _
      initialLedgerNoFresh := pointerParentTranslation_no_fresh
      translatedSourceEntryRow := by
        rw [pointerTranslatedEntry_exact]
        exact pointerInitialEntryRow
      firstSuccessor := pointerFirstSuccessor
      canonical_targetNextVisit_eq := rfl
      Answer := Live.State
      answer := pointerCurrentState pointerFirstSuccessor.targetCurrent
      Receipt := PointerActionReceiptAt pointerParentEvent
      receipt :=
        { sourceExact := rfl
          parentRow := pointerParentEntryRow
          actualAnswer := rfl
          receivedCurrent := pointer_received_is_parent
          preparedCurrent := pointerParent_prepared_joint
          instrumentClosure := sourceGeneratedPointerInstrument
          oldEntropy := Live.initial_entropyProduction
          oldFreeEnergy := Live.initial_freeEnergy
          netAccount := Live.measureNext_net_account Live.initial } }

def pointerActionProgram : SourceNativeSequentialActualActionProgramAt reservoirLivingRoot pointerParentVisit
    pointerParentEntry pointerParentAuthority where
  targetAt := pointerActionTargetAt

def generatedPointerAction : SourceGeneratedSequentialActualActionAt pointerActionProgram pointerParentEvent :=
  pointerActionProgram.generate pointerParentEvent

theorem generatedPointerAction_answer : generatedPointerAction.answer = Live.first := rfl

def generatedPointerAction_receipt : PointerActionReceiptAt pointerParentEvent Live.first :=
  generatedPointerAction.receipt

theorem generatedPointerAction_next : generatedPointerAction.target.targetAnswerAndNext.nextCurrent =
    ⟨PointerV, pointerAuthoritativeRoot, generatedPointerAction.target.targetVisit⟩ :=
  generatedPointerAction.target.targetAnswerAndNext_next_eq

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
