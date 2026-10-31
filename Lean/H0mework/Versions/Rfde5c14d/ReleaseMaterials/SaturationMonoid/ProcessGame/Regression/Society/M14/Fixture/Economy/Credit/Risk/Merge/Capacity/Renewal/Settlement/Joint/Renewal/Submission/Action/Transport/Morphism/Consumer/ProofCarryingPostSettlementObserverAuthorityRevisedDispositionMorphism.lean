import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Morphism.Producer.SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphism

/-!
# Proof-carrying consumer of the revised-disposition authority morphism

The consumer retains the exact input authority witness in a proof-relevant
installed fibre, its source K square, the rightReplay span certificate, the
augmented core's revised root/new-only row, whole-ledger successor, attached
coface, runtime and macro next.  It also universally eliminates every target
U8 factorization that requires a fabricated same-occurrence local legislation
source.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingPostSettlementObserverAuthorityRevisedDispositionMorphism

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open ConstructiveRoot.TypedSemanticWorldNetworkU8
open Renewal UniversalRootGrammar
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedPostSettlementObserverSubmissionU8
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation.SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
open M14ProofCarryingPostSettlementObserverSubmissionExternalPaymentLegislation
open M14SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphism
open M14SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphism.SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphismAt

structure ProofCarryingPostSettlementObserverAuthorityRevisedDispositionMorphismAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {span :
      SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
        oldVisit sourceIndex boundary}
    {authority :
      SourceNativeObserverConsumerRootedAuthorityAt (sourceSubmission span)}
    (morphism :
      SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphismAt
        span authority) : Prop where
  private mk ::
  spanCertificate :
    ProofCarryingPostSettlementObserverSubmissionExternalPaymentLegislationAt
      (legislationSpan morphism)
  sourceAuthorityExact :
    SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphismAt.sourceAuthority
        morphism = authority
  morphismGraphRetainsInput :
    (transportedInstalledAuthority morphism).1 = authority
  sourceEffectRootKExact : SourceEffectCommutesWithRootKAt morphism
  transportedDispositionExact :
    transportedDisposition morphism =
      (activatedSubmissionAt oldVisit sourceIndex boundary
        ).payload.disposition
  targetCoreExact :
    targetCore morphism = generatedU8CoreAt oldVisit sourceIndex boundary
  targetCoreNewLivingRootExact :
    (targetCore morphism).revision.generate.newLivingRoot =
      revisedLivingRootAt oldVisit sourceIndex boundary
  targetSourceEntryExact :
    (activatedSubmissionAt oldVisit sourceIndex boundary).payload.sourceEntry =
      (targetCore morphism).revision.generate.newOnlyEntry
  targetSelectedRowExact : HEq
    (activatedSubmissionAt oldVisit sourceIndex boundary).payload.selectedRow
    (targetCore morphism).revision.generate.newOnlyEntryRow.sourceRow
  targetSuccessorExact : HEq
    (activatedSubmissionAt oldVisit sourceIndex boundary).payload.successor
    (generatedFirstSuccessorAt oldVisit sourceIndex boundary)
  targetAttachedCoface :
    Nonempty
      (SourceGeneratedAttachedCofaceRealizationAt
        (targetCore morphism).revision.generate)
  targetRuntimeConsumesCore :
    SourceNativeInquiryRuntime.CofaceRealizationResumptionAt
      (targetCore morphism) (runtimeAt oldVisit sourceIndex boundary) 0
  targetIndependentConsumer :
    Nonempty
      (TargetLegislationConsumerAt (legislationSpan morphism))
  targetRootFactorization :
    (activatedSubmissionAt oldVisit sourceIndex boundary
      ).RootAnswerAndNextFactorizes
  targetMacroNextExact :
    ((runtimeAt oldVisit sourceIndex boundary).stateAt 1).engine.node.erase =
      (firstTickAt oldVisit sourceIndex boundary).next.node.erase
  localLegislationBasedReverseFactorizationEmpty :
    ∀ Generates :
        CanonicalSubmissionLocalLegislationAt oldVisit sourceIndex boundary →
        targetCore morphism =
          generatedU8CoreAt oldVisit sourceIndex boundary →
        SourceNativeInquiryRuntime.CofaceRealizationResumptionAt
          (targetCore morphism) (runtimeAt oldVisit sourceIndex boundary) 0 →
        Prop,
      IsEmpty
        (ObserverLocalLegislationTargetU8FactorizationAt morphism Generates)

/-- Independent direct consumer of one generated morphism. -/
theorem proofCarryingPostSettlementObserverAuthorityRevisedDispositionMorphism
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {span :
      SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
        oldVisit sourceIndex boundary}
    {authority :
      SourceNativeObserverConsumerRootedAuthorityAt (sourceSubmission span)}
    (morphism :
      SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphismAt
        span authority) :
    ProofCarryingPostSettlementObserverAuthorityRevisedDispositionMorphismAt
      morphism where
  spanCertificate :=
    proofCarryingPostSettlementObserverSubmissionExternalPaymentLegislation
      (legislationSpan morphism)
  sourceAuthorityExact := sourceAuthority_isInput morphism
  morphismGraphRetainsInput :=
    transportedInstalledAuthority_source_isInput morphism
  sourceEffectRootKExact := sourceEffect_commutes_with_rootK morphism
  transportedDispositionExact :=
    transportedDisposition_isInstalled morphism
  targetCoreExact := targetCore_isAugmentedCore morphism
  targetCoreNewLivingRootExact :=
    targetCore_newLivingRoot_isAugmentedRoot morphism
  targetSourceEntryExact :=
    installedDisposition_sourceEntry_isCoreNewOnlyEntry morphism
  targetSelectedRowExact :=
    installedDisposition_selectedRow_isCoreNewOnlyRow morphism
  targetSuccessorExact :=
    installedDisposition_successor_isGeneratedFirstSuccessor morphism
  targetAttachedCoface := ⟨targetAttachedCofaceRealization morphism⟩
  targetRuntimeConsumesCore := targetRuntimeConsumesCore morphism
  targetIndependentConsumer :=
    (proofCarryingPostSettlementObserverSubmissionExternalPaymentLegislation
      (legislationSpan morphism)).targetIndependentConsumer
  targetRootFactorization :=
    (targetCoreAndRootAnswerAndNextFactorizes morphism).2
  targetMacroNextExact := (targetCoreAndMacroNextExact morphism).2
  localLegislationBasedReverseFactorizationEmpty :=
    fun Generates =>
      observerLocalLegislationTargetU8Factorization_isEmpty morphism Generates

/-- Canonical span, exact authority witness, morphism and direct consumer. -/
abbrev AnyProofCarryingPostSettlementObserverAuthorityRevisedDispositionMorphismAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  Sigma fun span :
      SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
        oldVisit sourceIndex boundary =>
    Sigma fun authority :
        SourceNativeObserverConsumerRootedAuthorityAt (sourceSubmission span) =>
      { morphism :
          SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphismAt
            span authority //
        ProofCarryingPostSettlementObserverAuthorityRevisedDispositionMorphismAt
          morphism }

def canonicalProofCarryingPostSettlementObserverAuthorityRevisedDispositionMorphismAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    AnyProofCarryingPostSettlementObserverAuthorityRevisedDispositionMorphismAt
      oldVisit sourceIndex boundary :=
  let span :=
    sourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
      oldVisit sourceIndex boundary
  let authority := Classical.choice (sourceRootedAuthority span)
  let morphism :=
    sourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphismAt
      span authority
  ⟨span, authority, ⟨morphism,
    proofCarryingPostSettlementObserverAuthorityRevisedDispositionMorphism
      morphism⟩⟩

end
end M14ProofCarryingPostSettlementObserverAuthorityRevisedDispositionMorphism
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPostSettlementObserverAuthorityRevisedDispositionMorphism.proofCarryingPostSettlementObserverAuthorityRevisedDispositionMorphism
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPostSettlementObserverAuthorityRevisedDispositionMorphism.canonicalProofCarryingPostSettlementObserverAuthorityRevisedDispositionMorphismAt
