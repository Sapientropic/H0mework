import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Root.SourceGeneratedContributionCapacityJointSettlementRoot

/-!
# Sequential actual action into joint survivor settlement

The exact survivor occurrence at local current `2` generates the minimal
target-network extension and its two-current terminal root.  The generic
sequential-action seam is anchored at row `0`, while the target and receipt
are indexed by the source-generated joint material that already contains
complete `Fin 2` authority and independent consumers.  No caller submits a
target, terminal receipt, empty support, patch, or future.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedSequentialContributionCapacityJointSettlement

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityReopeningWorld
open M14SourceGeneratedContributionCapacityReopeningRoot
open M14SourceGeneratedContributionCapacitySettlementSupport
open M14SourceGeneratedContributionCapacitySettlementSurvivorCompiler
open M14SourceGeneratedContributionCapacitySettlementSurvivorRoot
open M14SourceGeneratedContributionCapacitySettlementState
open M14SourceGeneratedContributionCapacitySettlementSurvivorAccountability
open M14SourceGeneratedContributionCapacityJointSettlementWorld
open M14SourceGeneratedContributionCapacityJointSettlementMaterial
open M14SourceGeneratedContributionCapacityJointSettlementCompiler
open M14SourceGeneratedContributionCapacityJointSettlementRoot

abbrev CanonicalJointSettlementMaterialAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  sourceGeneratedContributionCapacityJointSettlementMaterialAt oldVisit
    sourceIndex

def contributionCapacityJointSettlementActionEntryAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    OpenResponsibilityAt (ReopeningNAt oldVisit)
      ((ContributionCapacityJointSettlementSurvivorRootAt oldVisit sourceIndex)
        |>.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
          ((ContributionCapacityJointSettlementSurvivorRootAt oldVisit
            sourceIndex).emitted
              (contributionCapacityJointSettlementSurvivorVisitAt oldVisit
                sourceIndex).current)) :=
  contributionCapacitySettlementSurvivorEntryAt oldVisit 0

def contributionCapacityJointSettlementActionAuthorityAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (material : JointMaterialAt oldVisit sourceIndex) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt
      (ContributionCapacityJointSettlementSurvivorRootAt oldVisit sourceIndex)
      (contributionCapacityJointSettlementSurvivorVisitAt oldVisit sourceIndex)
      (contributionCapacityJointSettlementActionEntryAt oldVisit sourceIndex) :=
  material.authorityAt 0

def contributionCapacityJointSettlementActionOccurrencePresentationAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (material : JointMaterialAt oldVisit sourceIndex) :
    ConstructivePresentation
      ((ContributionCapacityJointSettlementSurvivorRootAt oldVisit sourceIndex)
        |>.toAuthoritativeRoot.toRoot.actual.OccurrenceAt
          (contributionCapacityJointSettlementSurvivorVisitAt oldVisit
            sourceIndex).current)
      ((ContributionCapacityJointSettlementRootAt oldVisit sourceIndex
        material).toAuthoritativeRoot.toRoot.actual.OccurrenceAt false) where
  forward := fun _ => contributionCapacityJointSettlementEmitted oldVisit
    sourceIndex material false
  backward := fun _ =>
    (ContributionCapacityJointSettlementSurvivorRootAt oldVisit sourceIndex)
      |>.emitted
        (contributionCapacityJointSettlementSurvivorVisitAt oldVisit
          sourceIndex).current
  backward_forward := by
    intro occurrence
    exact (contributionCapacitySettlementSurvivorOccurrence_eq_emitted
      oldVisit sourceIndex
      (CanonicalContributionCapacitySettlementSourceEventAt oldVisit
        sourceIndex) occurrence).symm
  forward_backward := by
    intro occurrence
    exact (contributionCapacityJointSettlementOccurrence_eq_emitted oldVisit
      sourceIndex material occurrence).symm

structure ExactContributionCapacityJointSettlementIngressReceiptAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (material : JointMaterialAt oldVisit sourceIndex)
    (sourceEvent : ExactTemporalCausalRootEventAt
      (ContributionCapacityJointSettlementSurvivorRootAt oldVisit sourceIndex
        ).toAuthoritativeRoot.toLedgerRoot
      (contributionCapacityJointSettlementSurvivorVisitAt oldVisit sourceIndex))
    (_answer : ContributionCapacitySettlementSurvivorAnswer) : Type 3 where
  sourceEventExact : sourceEvent = material.sourceEvent
  completeAccountability :
    ContributionCapacitySettlementSurvivorAccountabilityAtCurrent oldVisit
      sourceIndex contributionCapacityJointSettlementSurvivorCurrentIndex
  everyRowMaterial : (entryIndex : Fin 2) →
    Nonempty
      (ContributionCapacityJointSettlementTerminalRowEvidenceAt oldVisit
        sourceIndex material entryIndex)
  firstSuccessorCurrentExact :
    (contributionCapacityJointSettlementFirstSuccessor oldVisit sourceIndex
      material).targetCurrent = true
  ingressNoFresh :
    (targetEntry :
      (contributionCapacityJointSettlementLiveLedger oldVisit).Entry) →
      Nonempty
        (Sigma fun oldEntry :
            (contributionCapacitySettlementSurvivorLedger oldVisit).Entry =>
          PLift
            ((contributionCapacityJointSettlementIngressPresentation oldVisit
              ).forward oldEntry = targetEntry))
  emptySupportNoOldPreimage :
    IsEmpty
      (Sigma fun oldSupport : (ReopeningNAt oldVisit).Support =>
        PLift
          ((contributionCapacityJointSettlementTranslation oldVisit
            ).support.forward oldSupport =
              contributionCapacityJointSettlementEmptySupport oldVisit))

def exactContributionCapacityJointSettlementIngressReceiptAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (material : JointMaterialAt oldVisit sourceIndex)
    (sourceEvent : ExactTemporalCausalRootEventAt
      (ContributionCapacityJointSettlementSurvivorRootAt oldVisit sourceIndex
        ).toAuthoritativeRoot.toLedgerRoot
      (contributionCapacityJointSettlementSurvivorVisitAt oldVisit sourceIndex)) :
    ExactContributionCapacityJointSettlementIngressReceiptAt oldVisit
      sourceIndex material sourceEvent
        (ContributionCapacitySettlementSurvivorAnswer.canonical 0) := by
  rw [sourceEvent.eq_generated]
  exact
    { sourceEventExact := material.sourceEventExact.symm
      completeAccountability := material.accountability
      everyRowMaterial := fun entryIndex =>
        ⟨contributionCapacityJointSettlementTerminalRowEvidenceAt oldVisit
          sourceIndex material entryIndex⟩
      firstSuccessorCurrentExact := rfl
      ingressNoFresh :=
        contributionCapacityJointSettlementIngress_noFresh oldVisit
      emptySupportNoOldPreimage :=
        contributionCapacityJointSettlementEmptySupport_hasNoOldPreimage
          oldVisit }

def contributionCapacityJointSettlementActionTargetAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (material : JointMaterialAt oldVisit sourceIndex)
    (sourceEvent : ExactTemporalCausalRootEventAt
      (ContributionCapacityJointSettlementSurvivorRootAt oldVisit sourceIndex
        ).toAuthoritativeRoot.toLedgerRoot
      (contributionCapacityJointSettlementSurvivorVisitAt oldVisit sourceIndex)) :
    SourceNativeSequentialActualActionTargetAt
      (ContributionCapacityJointSettlementSurvivorRootAt oldVisit sourceIndex)
      (contributionCapacityJointSettlementSurvivorVisitAt oldVisit sourceIndex)
      sourceEvent
      (contributionCapacityJointSettlementActionEntryAt oldVisit sourceIndex)
      (contributionCapacityJointSettlementActionAuthorityAt oldVisit
        sourceIndex material) := by
  rw [sourceEvent.eq_generated]
  exact
    { TargetN := JointSettlementNAt oldVisit
      translation := contributionCapacityJointSettlementTranslation oldVisit
      TargetV := ContributionCapacityJointSettlementVAt oldVisit
      targetRoot := contributionCapacityJointSettlementLivingRoot oldVisit
        sourceIndex material
      targetTheory := TheoryState.rootSemantic (JointSettlementNAt oldVisit)
      lawSurface_heq := HEq.rfl
      targetTheory_rootSemantic :=
        { compile := id
          commuting := fun _ => rfl }
      occurrencePresentation :=
        contributionCapacityJointSettlementActionOccurrencePresentationAt
          oldVisit sourceIndex material
      occurrence_commutes := rfl
      initialSupport_heq := HEq.rfl
      initialOpenLedger :=
        (contributionCapacityJointSettlementTranslation oldVisit).oldOpenLedger
          (contributionCapacitySettlementSurvivorSupport oldVisit)
      initialOpenLedger_heq := HEq.rfl
      initialLedger_responsibility_commutes := fun _ => rfl
      initialLedger_claim_commutes := fun _ => rfl
      initialLedger_budget_conservative := fun _ => Nat.le_refl _
      initialLedgerNoFresh :=
        contributionCapacityJointSettlementIngress_noFresh oldVisit
      translatedSourceEntryRow :=
        contributionCapacityJointSettlementInitialEntryRow oldVisit
          sourceIndex material 0
      firstSuccessor :=
        contributionCapacityJointSettlementFirstSuccessor oldVisit sourceIndex
          material
      canonical_targetNextVisit_eq := rfl
      Answer := ContributionCapacitySettlementSurvivorAnswer
      answer := ContributionCapacitySettlementSurvivorAnswer.canonical 0
      Receipt := fun answer =>
        ExactContributionCapacityJointSettlementIngressReceiptAt oldVisit
          sourceIndex material material.sourceEvent answer
      receipt := exactContributionCapacityJointSettlementIngressReceiptAt
        oldVisit sourceIndex material material.sourceEvent }

def contributionCapacityJointSettlementActionProgramAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (material : JointMaterialAt oldVisit sourceIndex) :
    SourceNativeSequentialActualActionProgramAt
      (ContributionCapacityJointSettlementSurvivorRootAt oldVisit sourceIndex)
      (contributionCapacityJointSettlementSurvivorVisitAt oldVisit sourceIndex)
      (contributionCapacityJointSettlementActionEntryAt oldVisit sourceIndex)
      (contributionCapacityJointSettlementActionAuthorityAt oldVisit
        sourceIndex material) where
  targetAt := contributionCapacityJointSettlementActionTargetAt oldVisit
    sourceIndex material

def generatedContributionCapacityJointSettlementActionAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (material : JointMaterialAt oldVisit sourceIndex) :
    SourceGeneratedSequentialActualActionAt
      (contributionCapacityJointSettlementActionProgramAt oldVisit sourceIndex
        material) material.sourceEvent :=
  (contributionCapacityJointSettlementActionProgramAt oldVisit sourceIndex
    material).generate material.sourceEvent

def contributionCapacityJointSettlementActionCompilationAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (material : JointMaterialAt oldVisit sourceIndex)
    (sourceEvent : ExactTemporalCausalRootEventAt
      (ContributionCapacityJointSettlementSurvivorRootAt oldVisit sourceIndex
        ).toAuthoritativeRoot.toLedgerRoot
      (contributionCapacityJointSettlementSurvivorVisitAt oldVisit sourceIndex)) :
    SourceNativeInquiryCompilationAt
      (ContributionCapacityJointSettlementSurvivorRootAt oldVisit sourceIndex)
      (contributionCapacityJointSettlementSurvivorVisitAt oldVisit sourceIndex)
      (contributionCapacityReopeningU7 oldVisit)
      (contributionCapacityReopeningCalculus oldVisit)
      (contributionCapacityReopeningTheory oldVisit) ()
      (contributionCapacitySettlementSurvivorEntryInquiryEventAt oldVisit
        sourceIndex contributionCapacityJointSettlementSurvivorCurrentIndex)
      (contributionCapacityJointSettlementActionEntryAt oldVisit sourceIndex)
      (contributionCapacityJointSettlementActionAuthorityAt oldVisit
        sourceIndex material) :=
  .actualAction
    ((contributionCapacityJointSettlementActionProgramAt oldVisit sourceIndex
      material).generate sourceEvent)

def contributionCapacityJointSettlementActionCompilationProgramAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (material : JointMaterialAt oldVisit sourceIndex) :
    SourceNativeInquiryCompilationProgramAt
      (ContributionCapacityJointSettlementSurvivorRootAt oldVisit sourceIndex)
      (contributionCapacityJointSettlementSurvivorVisitAt oldVisit sourceIndex)
      (contributionCapacityReopeningU7 oldVisit)
      (contributionCapacityReopeningCalculus oldVisit)
      (contributionCapacityReopeningTheory oldVisit) ()
      (contributionCapacitySettlementSurvivorEntryInquiryEventAt oldVisit
        sourceIndex contributionCapacityJointSettlementSurvivorCurrentIndex)
      (contributionCapacityJointSettlementActionEntryAt oldVisit sourceIndex)
      (contributionCapacityJointSettlementActionAuthorityAt oldVisit
        sourceIndex material) where
  compile := contributionCapacityJointSettlementActionCompilationAt oldVisit
    sourceIndex material

end
end M14SourceGeneratedSequentialContributionCapacityJointSettlement
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedSequentialContributionCapacityJointSettlement.contributionCapacityJointSettlementActionTargetAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedSequentialContributionCapacityJointSettlement.generatedContributionCapacityJointSettlementActionAt
