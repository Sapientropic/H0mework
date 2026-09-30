import H0mework.Chemistry.LAlanineInertia.RuntimeInertiaAuthority

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Inertia.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion
open LAlanine40K2025.Root LAlanine40K2025.Installation
noncomputable section

def inertiaOccurrencePresentation : ConstructivePresentation
    (root.toAuthoritativeRoot.toRoot.actual.OccurrenceAt inertiaParentVisit.current)
    (inertiaLivingRoot.toAuthoritativeRoot.toRoot.actual.OccurrenceAt
      inertiaLivingRoot.toAuthoritativeRoot.toRoot.source.initial) where
  forward := fun _ => inertiaEmitted .ingress
  backward := fun _ => inertiaParentEvent.occurrence
  backward_forward := by
    rintro ⟨support, event⟩
    change LAlanineRootEventAt .forceDrivenMaterialNextCertified support at event
    cases event
    rfl
  forward_backward := by
    rintro ⟨support, event⟩
    change PLift (support = inertiaSupport) at event
    cases event.down
    rfl

theorem inertiaTranslatedEntry_exact :
    (inertiaTranslation.oldOpenLedger inertiaSupport).forward inertiaParentEntry = inertiaInitialEntry := by
  rw [inertiaParentEntry_exact]
  rfl

structure InertiaActionReceiptAt
    (event : ExactTemporalCausalRootEventAt root.toAuthoritativeRoot.toLedgerRoot inertiaParentVisit)
    (answer : Interface.InertialStepReadout) : Type 3 where
  sourceExact : event = inertiaParentEvent
  actualAnswer : answer = Source.stepReadout
  sourceFirstStep : Producer.firstStepClosure
  receivedParentLedger : answer.currentLedger = inertiaParentMaterial.targetEnergyLedger
  receivedParentPositions : answer.currentPositionPicobohr = inertiaParentMaterial.recordedTargetPositions
  receivedParentNuclei : answer.currentNuclei = inertiaParentMaterial.targetNuclei

def inertiaActionTargetAt
    (event : ExactTemporalCausalRootEventAt root.toAuthoritativeRoot.toLedgerRoot inertiaParentVisit) :
    SourceNativeSequentialActualActionTargetAt root inertiaParentVisit event inertiaParentEntry inertiaParentAuthority := by
  rw [event.eq_generated]
  exact
    { TargetN := N
      translation := inertiaTranslation
      TargetV := InertiaV
      targetRoot := inertiaLivingRoot
      targetTheory := TheoryState.rootSemantic N
      lawSurface_heq := HEq.rfl
      targetTheory_rootSemantic := { compile := id, commuting := fun _ => rfl }
      occurrencePresentation := inertiaOccurrencePresentation
      occurrence_commutes := rfl
      initialSupport_heq := HEq.rfl
      initialOpenLedger := inertiaTranslation.oldOpenLedger inertiaSupport
      initialOpenLedger_heq := HEq.rfl
      initialLedger_responsibility_commutes := fun _ => rfl
      initialLedger_claim_commutes := fun _ => rfl
      initialLedger_budget_conservative := fun _ => Nat.le_refl _
      initialLedgerNoFresh := inertiaIngress_no_fresh _
      translatedSourceEntryRow := by rw [inertiaTranslatedEntry_exact]; exact inertiaInitialEntryRow
      firstSuccessor := inertiaFirstSuccessor
      canonical_targetNextVisit_eq := rfl
      Answer := Interface.InertialStepReadout
      answer := inertiaReadout inertiaFirstSuccessor.targetCurrent
      Receipt := InertiaActionReceiptAt inertiaParentEvent
      receipt :=
        { sourceExact := rfl
          actualAnswer := rfl
          sourceFirstStep := Producer.sourceGeneratedFirstStep
          receivedParentLedger := Producer.currentLedger_eq_parent.trans inertiaParentMaterial_energy.symm
          receivedParentPositions := Producer.currentPositionPicobohr_eq_parent.trans
            (congrArg (·.recordedTargetPositions) inertiaParentMaterial_exact).symm
          receivedParentNuclei := Producer.currentNuclei_eq_parent.trans
            (congrArg (·.targetNuclei) inertiaParentMaterial_exact).symm } }

def inertiaActionProgram : SourceNativeSequentialActualActionProgramAt root inertiaParentVisit
    inertiaParentEntry inertiaParentAuthority where
  targetAt := inertiaActionTargetAt

def generatedInertiaAction : SourceGeneratedSequentialActualActionAt inertiaActionProgram inertiaParentEvent :=
  inertiaActionProgram.generate inertiaParentEvent

theorem generatedInertiaAction_answer : generatedInertiaAction.answer = Source.stepReadout := rfl

def generatedInertiaAction_receipt : InertiaActionReceiptAt inertiaParentEvent Source.stepReadout :=
  generatedInertiaAction.receipt

theorem generatedInertiaAction_next : generatedInertiaAction.target.targetAnswerAndNext.nextCurrent =
    ⟨InertiaV, inertiaAuthoritativeRoot, generatedInertiaAction.target.targetVisit⟩ :=
  generatedInertiaAction.target.targetAnswerAndNext_next_eq

end
end LAlanine40K2025.Inertia.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
