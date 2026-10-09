import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Runtime.LoadActionIngress

/-! # Sequential actual action installs the thermal environment from the powered occurrence -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Load.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Producer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Source

noncomputable section

structure LoadActionReceiptAt
    (event : ExactTemporalCausalRootEventAt Powered.Runtime.poweredLivingRoot.toAuthoritativeRoot.toLedgerRoot loadParentVisit)
    (answer : LoadState) : Type 3 where
  sourceExact : event = loadParentEvent
  actualAnswer : answer = loadCurrentState loadFirstSuccessor.targetCurrent
  receivedPoweredCurrent : type_of% loadInitialJoint_receives_actual
  initialJoint : type_of% loadInitialState_received
  energyBalance : (pcEnergy answer.joint - pcEnergy loadInitialState.joint) +
    (environmentEnergy answer.joint - environmentEnergy loadInitialState.joint) +
    (boundaryEnergy answer.joint - boundaryEnergy loadInitialState.joint) = 0

def loadActionTargetAt
    (event : ExactTemporalCausalRootEventAt Powered.Runtime.poweredLivingRoot.toAuthoritativeRoot.toLedgerRoot loadParentVisit) :
    SourceNativeSequentialActualActionTargetAt Powered.Runtime.poweredLivingRoot loadParentVisit event
      loadParentEntry loadParentAuthority := by
  rw [event.eq_generated]
  exact
    { TargetN := LoadN
      translation := loadTranslation
      TargetV := LoadV
      targetRoot := loadLivingRoot
      targetTheory := TheoryState.rootSemantic LoadN
      lawSurface_heq := HEq.rfl
      targetTheory_rootSemantic := { compile := id, commuting := fun _ => rfl }
      occurrencePresentation := loadOccurrencePresentation
      occurrence_commutes := rfl
      initialSupport_heq := HEq.rfl
      initialOpenLedger := loadTranslation.oldOpenLedger loadSourceSupport
      initialOpenLedger_heq := HEq.rfl
      initialLedger_responsibility_commutes := fun _ => rfl
      initialLedger_claim_commutes := fun _ => rfl
      initialLedger_budget_conservative := fun _ => Nat.le_refl _
      initialLedgerNoFresh := loadIngress_no_fresh_rows _
      translatedSourceEntryRow := by
        rw [loadTranslatedEntry_exact]
        exact loadInitialEntryRow
      firstSuccessor := loadFirstSuccessor
      canonical_targetNextVisit_eq := rfl
      Answer := LoadState
      answer := loadCurrentState loadFirstSuccessor.targetCurrent
      Receipt := LoadActionReceiptAt loadParentEvent
      receipt :=
        { sourceExact := rfl
          actualAnswer := rfl
          receivedPoweredCurrent := loadInitialJoint_receives_actual
          initialJoint := loadInitialState_received
          energyBalance := loadStateNext_energyBalance loadInitialState } }

def loadActionProgram : SourceNativeSequentialActualActionProgramAt Powered.Runtime.poweredLivingRoot loadParentVisit
    loadParentEntry loadParentAuthority where
  targetAt := loadActionTargetAt

def generatedLoadAction : SourceGeneratedSequentialActualActionAt loadActionProgram loadParentEvent :=
  loadActionProgram.generate loadParentEvent

theorem generatedLoadAction_answer : generatedLoadAction.answer = loadStateNext loadInitialState := rfl

def generatedLoadAction_receipt : LoadActionReceiptAt loadParentEvent (loadStateNext loadInitialState) :=
  generatedLoadAction.receipt

theorem generatedLoadAction_next : generatedLoadAction.target.targetAnswerAndNext.nextCurrent =
    ⟨LoadV, loadAuthoritativeRoot, generatedLoadAction.target.targetVisit⟩ :=
  generatedLoadAction.target.targetAnswerAndNext_next_eq

end

end LAlanine40K2025.Thermal.Load.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
