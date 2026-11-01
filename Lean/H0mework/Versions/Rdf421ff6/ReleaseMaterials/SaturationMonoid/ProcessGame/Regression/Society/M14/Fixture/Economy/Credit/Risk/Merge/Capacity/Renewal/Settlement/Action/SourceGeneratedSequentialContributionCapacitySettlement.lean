import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Root.SourceGeneratedContributionCapacitySettlementRoot

/-!
# Source-generated sequential contribution-capacity settlement

At reopening current `3`, the exact residual occurrence generates the fixed
two-current settlement root.  The cross-root ingress is the identity
translation of the complete three-row ledger.  The action receipt records
only this generated ingress and first write; terminal discharge remains an
actual later occurrence rather than a stored completed future.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedSequentialContributionCapacitySettlement

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityReopeningWorld
open M14SourceGeneratedContributionCapacityReopeningCompiler
open M14SourceGeneratedContributionCapacityReopeningRoot
open M14SourceGeneratedContributionCapacityReopeningState
open M14SourceGeneratedContributionCapacitySettlementSupport
open M14SourceGeneratedContributionCapacitySettlementActionSource
open M14SourceGeneratedContributionCapacitySettlementCompiler
open M14SourceGeneratedContributionCapacitySettlementRoot

def contributionCapacitySettlementIdentityTranslation
    (oldVisit : OldVisit) :
    TypedSemanticWorldNetworkTranslationAt
      (ReopeningNAt oldVisit) (SettlementNAt oldVisit) where
  support :=
    { forward := id
      backward := id
      backward_forward := fun _ => rfl }
  anchor :=
    { forward := id
      backward := id
      backward_forward := fun _ => rfl }
  incidence :=
    { forward := id
      backward := id
      backward_forward := fun _ => rfl }
  lineage :=
    { forward := id
      backward := id
      backward_forward := fun _ => rfl }
  responsibility :=
    { forward := id
      backward := id
      backward_forward := fun _ => rfl }
  claim :=
    { forward := id
      backward := id
      backward_forward := fun _ => rfl }
  anchor_commutes := fun _ => rfl
  incidence_commutes := fun _ => rfl
  lineage_commutes := fun _ => rfl
  oldOpenLedger := fun _ =>
    { forward := id
      backward := id
      backward_forward := fun _ => rfl }
  oldOpenClaim_commutes := fun _ _ => rfl
  oldOpenProgressBudget_commutes := fun _ _ => rfl
  oldHoldsSurvives := fun _ _ proof => proof
  oldDispositionSurvives := fun _ _ proof => proof

def contributionCapacitySettlementActionOccurrencePresentationAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (exactSource :
      ContributionCapacitySettlementSourceEventAt oldVisit sourceIndex) :
    ConstructivePresentation
      ((ContributionCapacitySettlementActionRootAt oldVisit sourceIndex)
        |>.toAuthoritativeRoot.toRoot.actual.OccurrenceAt
          (contributionCapacitySettlementActionVisitAt oldVisit
            sourceIndex).current)
      ((contributionCapacitySettlementLivingRoot oldVisit sourceIndex
        exactSource).toAuthoritativeRoot.toRoot.actual.OccurrenceAt false) where
  forward := fun _ => contributionCapacitySettlementEmitted oldVisit
    sourceIndex exactSource false
  backward := fun _ =>
    (ContributionCapacitySettlementActionRootAt oldVisit sourceIndex).emitted
      (contributionCapacitySettlementActionVisitAt oldVisit
        sourceIndex).current
  backward_forward := by
    intro occurrence
    exact (contributionCapacityReopeningOccurrence_eq_emitted oldVisit
      sourceIndex (CanonicalReopeningSourceEventAt oldVisit sourceIndex)
      occurrence).symm
  forward_backward := by
    intro occurrence
    exact (contributionCapacitySettlementOccurrence_eq_emitted oldVisit
      sourceIndex exactSource occurrence).symm

@[simp] theorem contributionCapacitySettlementActionOccurrence_commutes
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (exactSource :
      ContributionCapacitySettlementSourceEventAt oldVisit sourceIndex) :
    (contributionCapacitySettlementActionOccurrencePresentationAt oldVisit
      sourceIndex exactSource).forward exactSource.occurrence =
      (contributionCapacitySettlementLivingRoot oldVisit sourceIndex
        exactSource).emitted false :=
  rfl

structure ExactContributionCapacitySettlementIngressReceiptAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (sourceEvent :
      ContributionCapacitySettlementSourceEventAt oldVisit sourceIndex)
    (_answer : contributionCapacityReopeningAnswerPayloadAt oldVisit
      sourceIndex (CanonicalReopeningSourceEventAt oldVisit sourceIndex)
        3) : Type 3 where
  sourceEventExact : sourceEvent =
    contributionCapacitySettlementActionExactSourceEventAt oldVisit
      sourceIndex
  sourceCurrentExact :
    (show Nat from
      (contributionCapacitySettlementActionVisitAt oldVisit
        sourceIndex).current) = 3
  sourceResidualExact :
    contributionCapacitySettlementActionEntryAt oldVisit sourceIndex =
      contributionCapacityReopeningTargetResidual oldVisit
  firstSuccessorCurrentExact :
    (contributionCapacitySettlementFirstSuccessor oldVisit sourceIndex
      sourceEvent).targetCurrent = true
  initialLedgerExactlyThree :
    (entry : (contributionCapacitySettlementFullLedger oldVisit).Entry) →
      entry = contributionCapacitySettlementFullEntryAt oldVisit 0 ∨
      entry = contributionCapacitySettlementFullEntryAt oldVisit 1 ∨
      entry = contributionCapacitySettlementFullEntryAt oldVisit 2
  initialLedgerAllZero :
    (entry : (contributionCapacitySettlementFullLedger oldVisit).Entry) →
      entry.progressBudget = 0

def exactContributionCapacitySettlementIngressReceiptAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (sourceEvent :
      ContributionCapacitySettlementSourceEventAt oldVisit sourceIndex)
    (answer : contributionCapacityReopeningAnswerPayloadAt oldVisit
      sourceIndex (CanonicalReopeningSourceEventAt oldVisit sourceIndex)
        3) :
    ExactContributionCapacitySettlementIngressReceiptAt oldVisit sourceIndex
      sourceEvent answer := by
  rw [sourceEvent.eq_generated]
  exact
    { sourceEventExact := rfl
      sourceCurrentExact :=
        contributionCapacitySettlementActionVisit_current_exact oldVisit
          sourceIndex
      sourceResidualExact := rfl
      firstSuccessorCurrentExact := rfl
      initialLedgerExactlyThree :=
        contributionCapacitySettlementFullEntry_cases oldVisit
      initialLedgerAllZero :=
        contributionCapacityReopeningTargetEntry_budget_zero oldVisit }

def contributionCapacitySettlementActionTargetAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (exactSource :
      ContributionCapacitySettlementSourceEventAt oldVisit sourceIndex) :
    SourceNativeSequentialActualActionTargetAt
      (ContributionCapacitySettlementActionRootAt oldVisit sourceIndex)
      (contributionCapacitySettlementActionVisitAt oldVisit sourceIndex)
      exactSource
      (contributionCapacitySettlementActionEntryAt oldVisit sourceIndex)
      (contributionCapacitySettlementActionAuthorityAt oldVisit sourceIndex) :=
  { TargetN := SettlementNAt oldVisit
    translation := contributionCapacitySettlementIdentityTranslation oldVisit
    TargetV := SettlementVAt oldVisit
    targetRoot := contributionCapacitySettlementLivingRoot oldVisit sourceIndex
      exactSource
    targetTheory := contributionCapacityReopeningTheory oldVisit
    lawSurface_heq := HEq.rfl
    targetTheory_rootSemantic :=
      { compile := id
        commuting := fun _ => rfl }
    occurrencePresentation :=
      contributionCapacitySettlementActionOccurrencePresentationAt oldVisit
        sourceIndex exactSource
    occurrence_commutes :=
      contributionCapacitySettlementActionOccurrence_commutes oldVisit
        sourceIndex exactSource
    initialSupport_heq := HEq.rfl
    initialOpenLedger :=
      (contributionCapacitySettlementIdentityTranslation oldVisit).oldOpenLedger
        (contributionCapacitySettlementFullSupport oldVisit)
    initialOpenLedger_heq := HEq.rfl
    initialLedger_responsibility_commutes := fun _ => rfl
    initialLedger_claim_commutes := fun _ => rfl
    initialLedger_budget_conservative := fun _ => Nat.le_refl _
    initialLedgerNoFresh := fun targetEntry =>
      ⟨⟨targetEntry, PLift.up rfl⟩⟩
    translatedSourceEntryRow :=
      contributionCapacitySettlementInitialResidualRow oldVisit sourceIndex
        exactSource
    firstSuccessor := contributionCapacitySettlementFirstSuccessor oldVisit
      sourceIndex exactSource
    canonical_targetNextVisit_eq := rfl
    Answer := contributionCapacityReopeningAnswerPayloadAt oldVisit
      sourceIndex (CanonicalReopeningSourceEventAt oldVisit sourceIndex) 3
    answer := contributionCapacityReopeningAnswerPayload oldVisit sourceIndex
      (CanonicalReopeningSourceEventAt oldVisit sourceIndex) 3
    Receipt := fun answer =>
      ExactContributionCapacitySettlementIngressReceiptAt oldVisit sourceIndex
        exactSource answer
    receipt := exactContributionCapacitySettlementIngressReceiptAt oldVisit
      sourceIndex exactSource
      (contributionCapacityReopeningAnswerPayload oldVisit sourceIndex
        (CanonicalReopeningSourceEventAt oldVisit sourceIndex) 3) }

def contributionCapacitySettlementActionProgramAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    SourceNativeSequentialActualActionProgramAt
      (ContributionCapacitySettlementActionRootAt oldVisit sourceIndex)
      (contributionCapacitySettlementActionVisitAt oldVisit sourceIndex)
      (contributionCapacitySettlementActionEntryAt oldVisit sourceIndex)
      (contributionCapacitySettlementActionAuthorityAt oldVisit sourceIndex) where
  targetAt := contributionCapacitySettlementActionTargetAt oldVisit sourceIndex

def generatedContributionCapacitySettlementActionAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    SourceGeneratedSequentialActualActionAt
      (contributionCapacitySettlementActionProgramAt oldVisit sourceIndex)
      (contributionCapacitySettlementActionExactSourceEventAt oldVisit
        sourceIndex) :=
  (contributionCapacitySettlementActionProgramAt oldVisit sourceIndex).generate
    (contributionCapacitySettlementActionExactSourceEventAt oldVisit
      sourceIndex)

def contributionCapacitySettlementActionCompilationAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (exactSource :
      ContributionCapacitySettlementSourceEventAt oldVisit sourceIndex) :
    SourceNativeInquiryCompilationAt
      (ContributionCapacitySettlementActionRootAt oldVisit sourceIndex)
      (contributionCapacitySettlementActionVisitAt oldVisit sourceIndex)
      (contributionCapacityReopeningU7 oldVisit)
      (contributionCapacityReopeningCalculus oldVisit)
      (contributionCapacityReopeningTheory oldVisit) ()
      (contributionCapacityReopenedInquiryEventAt oldVisit sourceIndex 2)
      (contributionCapacitySettlementActionEntryAt oldVisit sourceIndex)
      (contributionCapacitySettlementActionAuthorityAt oldVisit sourceIndex) :=
  .actualAction
    ((contributionCapacitySettlementActionProgramAt oldVisit sourceIndex)
      |>.generate exactSource)

def contributionCapacitySettlementActionCompilationProgramAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    SourceNativeInquiryCompilationProgramAt
      (ContributionCapacitySettlementActionRootAt oldVisit sourceIndex)
      (contributionCapacitySettlementActionVisitAt oldVisit sourceIndex)
      (contributionCapacityReopeningU7 oldVisit)
      (contributionCapacityReopeningCalculus oldVisit)
      (contributionCapacityReopeningTheory oldVisit) ()
      (contributionCapacityReopenedInquiryEventAt oldVisit sourceIndex 2)
      (contributionCapacitySettlementActionEntryAt oldVisit sourceIndex)
      (contributionCapacitySettlementActionAuthorityAt oldVisit sourceIndex) where
  compile := contributionCapacitySettlementActionCompilationAt oldVisit
    sourceIndex

end
end M14SourceGeneratedSequentialContributionCapacitySettlement
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedSequentialContributionCapacitySettlement.generatedContributionCapacitySettlementActionAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedSequentialContributionCapacitySettlement.contributionCapacitySettlementActionTargetAt
