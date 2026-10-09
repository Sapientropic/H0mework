import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Powered.Runtime.PoweredActionIngress

/-! # Sequential actual action installs the finite controller from the field occurrence -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Powered.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Powered.Producer

noncomputable section

structure PoweredActionReceiptAt
    (event : ExactTemporalCausalRootEventAt Work.Runtime.fieldLivingRoot.toAuthoritativeRoot.toLedgerRoot poweredParentVisit)
    (answer : PoweredState) : Type 3 where
  sourceExact : event = poweredParentEvent
  actualAnswer : answer = poweredCurrentState poweredFirstSuccessor.targetCurrent
  receivedFieldCurrent : type_of% sourceInitialState_received
  initialCharge : poweredControllerEnergy sourceInitialState = 2
  energyBalance : (poweredPairEnergy answer - poweredPairEnergy sourceInitialState) +
    (poweredControllerEnergy answer - poweredControllerEnergy sourceInitialState) = 0

def poweredActionTargetAt
    (event : ExactTemporalCausalRootEventAt Work.Runtime.fieldLivingRoot.toAuthoritativeRoot.toLedgerRoot poweredParentVisit) :
    SourceNativeSequentialActualActionTargetAt Work.Runtime.fieldLivingRoot poweredParentVisit event
      poweredParentEntry poweredParentAuthority := by
  rw [event.eq_generated]
  exact
    { TargetN := PoweredN
      translation := poweredTranslation
      TargetV := PoweredV
      targetRoot := poweredLivingRoot
      targetTheory := TheoryState.rootSemantic PoweredN
      lawSurface_heq := HEq.rfl
      targetTheory_rootSemantic := { compile := id, commuting := fun _ => rfl }
      occurrencePresentation := poweredOccurrencePresentation
      occurrence_commutes := rfl
      initialSupport_heq := HEq.rfl
      initialOpenLedger := poweredTranslation.oldOpenLedger poweredSourceSupport
      initialOpenLedger_heq := HEq.rfl
      initialLedger_responsibility_commutes := fun _ => rfl
      initialLedger_claim_commutes := fun _ => rfl
      initialLedger_budget_conservative := fun _ => Nat.le_refl _
      initialLedgerNoFresh := poweredIngress_no_fresh_rows _
      translatedSourceEntryRow := by
        rw [poweredTranslatedEntry_exact]
        exact poweredInitialEntryRow
      firstSuccessor := poweredFirstSuccessor
      canonical_targetNextVisit_eq := rfl
      Answer := PoweredState
      answer := poweredCurrentState poweredFirstSuccessor.targetCurrent
      Receipt := PoweredActionReceiptAt poweredParentEvent
      receipt :=
        { sourceExact := rfl
          actualAnswer := rfl
          receivedFieldCurrent := sourceInitialState_received
          initialCharge := sourceInitialState_energy
          energyBalance := poweredStateNext_energyBalance sourceInitialState } }

def poweredActionProgram : SourceNativeSequentialActualActionProgramAt Work.Runtime.fieldLivingRoot poweredParentVisit
    poweredParentEntry poweredParentAuthority where
  targetAt := poweredActionTargetAt

def generatedPoweredAction : SourceGeneratedSequentialActualActionAt poweredActionProgram poweredParentEvent :=
  poweredActionProgram.generate poweredParentEvent

theorem generatedPoweredAction_answer : generatedPoweredAction.answer = poweredStateNext sourceInitialState := rfl

def generatedPoweredAction_receipt : PoweredActionReceiptAt poweredParentEvent (poweredStateNext sourceInitialState) :=
  generatedPoweredAction.receipt

theorem generatedPoweredAction_next : generatedPoweredAction.target.targetAnswerAndNext.nextCurrent =
    ⟨PoweredV, poweredAuthoritativeRoot, generatedPoweredAction.target.targetVisit⟩ :=
  generatedPoweredAction.target.targetAnswerAndNext_next_eq

end

end LAlanine40K2025.Thermal.Powered.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
