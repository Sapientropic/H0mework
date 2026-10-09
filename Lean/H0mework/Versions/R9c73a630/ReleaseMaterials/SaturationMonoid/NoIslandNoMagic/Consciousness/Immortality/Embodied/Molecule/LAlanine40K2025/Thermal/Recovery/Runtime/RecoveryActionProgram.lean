import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Runtime.RecoveryActionIngress

/-! # The remembered load occurrence generates its controlled recovery answer and literal next -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion
open Load.Producer Recovery.Producer Recovery.StrictRefill

noncomputable section

structure RecoveryActionReceiptAt
    (event : ExactTemporalCausalRootEventAt Load.Runtime.loadLivingRoot.toAuthoritativeRoot.toLedgerRoot recoveryParentVisit)
    (answer : LoadState) : Type 3 where
  sourceExact : event = recoveryParentEvent
  actualAnswer : answer = recoveryCurrentState recoveryFirstSuccessor.targetCurrent
  receivedActualLoad : type_of% recoveryReceived_actual
  physicalRecovery : type_of% sourceGeneratedRecovery
  strictRefill : type_of% sourceGeneratedStrictRefill
  netAccount :
    (loadBindingAccountedFreeEnergy answer - loadBindingAccountedFreeEnergy recoveryReceivedState) +
      (loadEntropyProduction answer - loadEntropyProduction recoveryReceivedState) = recoveryWork recoveryReceivedState

def recoveryActionTargetAt
    (event : ExactTemporalCausalRootEventAt Load.Runtime.loadLivingRoot.toAuthoritativeRoot.toLedgerRoot recoveryParentVisit) :
    SourceNativeSequentialActualActionTargetAt Load.Runtime.loadLivingRoot recoveryParentVisit event
      recoveryParentEntry recoveryParentAuthority := by
  rw [event.eq_generated]
  exact
    { TargetN := RecoveryN
      translation := recoveryTranslation
      TargetV := RecoveryV
      targetRoot := recoveryLivingRoot
      targetTheory := TheoryState.rootSemantic RecoveryN
      lawSurface_heq := HEq.rfl
      targetTheory_rootSemantic := { compile := id, commuting := fun _ => rfl }
      occurrencePresentation := recoveryOccurrencePresentation
      occurrence_commutes := rfl
      initialSupport_heq := HEq.rfl
      initialOpenLedger := recoveryTranslation.oldOpenLedger recoverySourceSupport
      initialOpenLedger_heq := HEq.rfl
      initialLedger_responsibility_commutes := fun _ => rfl
      initialLedger_claim_commutes := fun _ => rfl
      initialLedger_budget_conservative := fun _ => Nat.le_refl _
      initialLedgerNoFresh := recoveryIngress_no_fresh_rows _
      translatedSourceEntryRow := by
        rw [recoveryTranslatedEntry_exact]
        exact recoveryInitialEntryRow
      firstSuccessor := recoveryFirstSuccessor
      canonical_targetNextVisit_eq := rfl
      Answer := LoadState
      answer := recoveryCurrentState recoveryFirstSuccessor.targetCurrent
      Receipt := RecoveryActionReceiptAt recoveryParentEvent
      receipt :=
        { sourceExact := rfl
          actualAnswer := rfl
          receivedActualLoad := recoveryReceived_actual
          physicalRecovery := sourceGeneratedRecovery
          strictRefill := sourceGeneratedStrictRefill
          netAccount := recoveryStep_netAccount recoveryReceivedState } }

def recoveryActionProgram : SourceNativeSequentialActualActionProgramAt Load.Runtime.loadLivingRoot recoveryParentVisit
    recoveryParentEntry recoveryParentAuthority where
  targetAt := recoveryActionTargetAt

def generatedRecoveryAction : SourceGeneratedSequentialActualActionAt recoveryActionProgram recoveryParentEvent :=
  recoveryActionProgram.generate recoveryParentEvent

theorem generatedRecoveryAction_answer : generatedRecoveryAction.answer = recoveryStateFirst := rfl

def generatedRecoveryAction_receipt : RecoveryActionReceiptAt recoveryParentEvent recoveryStateFirst :=
  generatedRecoveryAction.receipt

theorem generatedRecoveryAction_next : generatedRecoveryAction.target.targetAnswerAndNext.nextCurrent =
    ⟨RecoveryV, recoveryAuthoritativeRoot, generatedRecoveryAction.target.targetVisit⟩ :=
  generatedRecoveryAction.target.targetAnswerAndNext_next_eq

end

end LAlanine40K2025.Thermal.Recovery.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
