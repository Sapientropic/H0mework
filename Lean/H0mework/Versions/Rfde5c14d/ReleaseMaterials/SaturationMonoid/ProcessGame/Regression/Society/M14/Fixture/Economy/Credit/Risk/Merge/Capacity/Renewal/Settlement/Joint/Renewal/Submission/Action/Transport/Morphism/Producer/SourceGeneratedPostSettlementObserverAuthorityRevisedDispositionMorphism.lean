import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Consumer.ProofCarryingPostSettlementObserverSubmissionExternalPaymentLegislation

/-!
# Observer authority into the U8 revised first-row disposition

The cross-occurrence span does not turn observer authority into the old
Payment row authority.  Its actual target is the pre-emitter authority
incidence installed on the augmented U8 revision's existing new-only first
row.  That dependent target is literally a lifted nonempty source rooted-
authority fibre, so it records incidence rather than proof-term identity.

This module consumes one real source authority, indexes a private morphism
token by that exact witness, and retains it in a proof-relevant installed
fibre whose second projection is the literal first-row disposition.  The
source witness continues to decode the exact root K.  The Payment-side U8
remains the generator of the revision.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphism

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open ConstructiveRoot.TypedSemanticWorldNetworkU8
open Renewal UniversalRootGrammar
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedUniversalSocietyRootGrammar
open M14SourceGeneratedPostSettlementObserverSubmissionU8
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation.SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt

variable {oldVisit : OldVisit} {sourceIndex boundary : Nat}

/-- Private morphism indexed by the complete span and the exact source
authority witness supplied to the producer. -/
inductive SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphismAt
    (span :
      SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
        oldVisit sourceIndex boundary)
    (_authority :
      SourceNativeObserverConsumerRootedAuthorityAt (sourceSubmission span)) :
    Type 31
  | private generated

/-- Sole producer.  It must consume a witness of the exact span-selected
source authority type; no row, disposition, core or runtime is accepted. -/
def sourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphismAt
    (span :
      SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
        oldVisit sourceIndex boundary)
    (authority :
      SourceNativeObserverConsumerRootedAuthorityAt (sourceSubmission span)) :
    SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphismAt
      span authority :=
  .generated

namespace SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphismAt

variable
  {span :
    SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
      oldVisit sourceIndex boundary}
  {authority :
    SourceNativeObserverConsumerRootedAuthorityAt (sourceSubmission span)}
  (morphism :
    SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphismAt
      span authority)

include morphism

def legislationSpan := by
  cases morphism
  exact span

def sourceAuthority :
    SourceNativeObserverConsumerRootedAuthorityAt
      (sourceSubmission (legislationSpan morphism)) := by
  cases morphism
  exact authority

theorem sourceAuthority_isInput :
    sourceAuthority morphism = authority := by
  cases morphism
  rfl

/-- Exact source K square retained by the carried authority witness. -/
abbrev SourceEffectCommutesWithRootKAt : Prop :=
  (sourceAuthority morphism).certificate.complete.decodeAuthority
      ((canonicalAttemptAt oldVisit sourceIndex boundary).consumer
        ((canonicalAttemptAt oldVisit sourceIndex boundary).readout.read
          (sourceSubmission (legislationSpan morphism)).sourceOccurrence)) =
    sourceNativeObserverRootAuthorityKAt
      (universalSocietyRecognitionAt oldVisit sourceIndex)
      (sourceSubmission (legislationSpan morphism)).sourceOccurrence

theorem sourceEffect_commutes_with_rootK :
    SourceEffectCommutesWithRootKAt morphism :=
  (sourceAuthority morphism).effect_commutes_with_rootK
    (sourceSubmission (legislationSpan morphism)).sourceOccurrence

/-- Image of the exact authority witness in the already installed revised-row
disposition type. -/
def transportedDisposition :
    LocalDispositionAt oldVisit sourceIndex boundary
      (activatedSubmissionAt oldVisit sourceIndex boundary
        ).payload.sourceSeed :=
  ⟨⟨sourceAuthority morphism⟩⟩

/-- The transported image is the literal pre-emitter disposition stored by
the augmented first-row renewal face. -/
theorem transportedDisposition_isInstalled :
    transportedDisposition morphism =
      (activatedSubmissionAt oldVisit sourceIndex boundary
        ).payload.disposition :=
  Subsingleton.elim _ _

/-- Proof-relevant target fibre.  The source witness is retained as the first
projection; only its installed disposition image is proof-irrelevant. -/
abbrev InstalledRevisedDispositionAuthorityFibreAt :=
  Sigma fun _carriedAuthority :
      SourceNativeObserverConsumerRootedAuthorityAt
        (sourceSubmission (legislationSpan morphism)) =>
    { disposition :
        LocalDispositionAt oldVisit sourceIndex boundary
          (activatedSubmissionAt oldVisit sourceIndex boundary
            ).payload.sourceSeed //
      disposition =
        (activatedSubmissionAt oldVisit sourceIndex boundary
          ).payload.disposition }

/-- The exact input witness together with its installed first-row incidence. -/
def transportedInstalledAuthority :
    InstalledRevisedDispositionAuthorityFibreAt morphism :=
  ⟨sourceAuthority morphism,
    ⟨transportedDisposition morphism,
      transportedDisposition_isInstalled morphism⟩⟩

theorem transportedInstalledAuthority_source_isInput :
    (transportedInstalledAuthority morphism).1 = authority := by
  exact sourceAuthority_isInput morphism

theorem transportedInstalledAuthority_disposition_isInstalled :
    (transportedInstalledAuthority morphism).2.1 =
      (activatedSubmissionAt oldVisit sourceIndex boundary
        ).payload.disposition :=
  (transportedInstalledAuthority morphism).2.2

/-- Exact U8 core at the Payment endpoint of this same span. -/
def targetCore :=
  (targetRevolutionaryConsumption (legislationSpan morphism)).1.core

theorem targetCore_isAugmentedCore :
    targetCore morphism = generatedU8CoreAt oldVisit sourceIndex boundary :=
  M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation.SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt.targetCore_isAugmentedCore
    (legislationSpan morphism)

theorem targetCore_newLivingRoot_isAugmentedRoot :
    (targetCore morphism).revision.generate.newLivingRoot =
      revisedLivingRootAt oldVisit sourceIndex boundary := by
  cases morphism
  rfl

/-- The disposition is installed on the target core's literal new-only row,
not on the old Payment entry. -/
theorem installedDisposition_sourceEntry_isCoreNewOnlyEntry :
    (activatedSubmissionAt oldVisit sourceIndex boundary).payload.sourceEntry =
      (targetCore morphism).revision.generate.newOnlyEntry := by
  cases morphism
  rfl

theorem installedDisposition_selectedRow_isCoreNewOnlyRow : HEq
    (activatedSubmissionAt oldVisit sourceIndex boundary).payload.selectedRow
    (targetCore morphism).revision.generate.newOnlyEntryRow.sourceRow := by
  cases morphism
  exact HEq.rfl

theorem installedDisposition_successor_isGeneratedFirstSuccessor : HEq
    (activatedSubmissionAt oldVisit sourceIndex boundary).payload.successor
    (generatedFirstSuccessorAt oldVisit sourceIndex boundary) := by
  cases morphism
  exact submissionFace_successor_heq_generatedSuccessor oldVisit sourceIndex
    boundary

/-- Attached coface realization of the same target core revision. -/
def targetAttachedCofaceRealization :
    SourceGeneratedAttachedCofaceRealizationAt
      (targetCore morphism).revision.generate := by
  rw [targetCore_isAugmentedCore morphism]
  exact (generatedTypedRevisionAt oldVisit sourceIndex boundary
    ).attachedCofaceRealization

theorem targetRuntimeConsumesCore :
    SourceNativeInquiryRuntime.CofaceRealizationResumptionAt
      (targetCore morphism) (runtimeAt oldVisit sourceIndex boundary) 0 := by
  rw [targetCore_isAugmentedCore morphism]
  exact targetRuntimeConsumesAugmentedCore (legislationSpan morphism)

/-- The exact target core and installed first row retain the existing
answer/next whole-ledger factorization. -/
theorem targetCoreAndRootAnswerAndNextFactorizes :
    targetCore morphism = generatedU8CoreAt oldVisit sourceIndex boundary ∧
      (activatedSubmissionAt oldVisit sourceIndex boundary
        ).RootAnswerAndNextFactorizes :=
  ⟨targetCore_isAugmentedCore morphism,
    (proofCarryingPostSettlementObserverSubmissionFinalAuthority oldVisit
      sourceIndex boundary).submissionRootMicroFactorization⟩

/-- The same exact core reaches the literal macro next at runtime tick one. -/
theorem targetCoreAndMacroNextExact :
    targetCore morphism = generatedU8CoreAt oldVisit sourceIndex boundary ∧
      ((runtimeAt oldVisit sourceIndex boundary).stateAt 1
        ).engine.node.erase =
        (firstTickAt oldVisit sourceIndex boundary).next.node.erase :=
  ⟨targetCore_isAugmentedCore morphism,
    (proofCarryingPostSettlementObserverSubmissionFinalAuthority oldVisit
      sourceIndex boundary).u8MacroNextExact⟩

end SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphismAt

open SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphismAt

/-- A proposed local-legislation-based factorization into this exact target
U8 must carry the local bundle, target core equality, runtime resumption and
an explicit causal relation connecting all three. -/
structure ObserverLocalLegislationTargetU8FactorizationAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {span :
      SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
        oldVisit sourceIndex boundary}
    {authority :
      SourceNativeObserverConsumerRootedAuthorityAt (sourceSubmission span)}
    (morphism :
      SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphismAt
        span authority)
    (Generates :
      CanonicalSubmissionLocalLegislationAt oldVisit sourceIndex boundary →
      targetCore morphism = generatedU8CoreAt oldVisit sourceIndex boundary →
      SourceNativeInquiryRuntime.CofaceRealizationResumptionAt
        (targetCore morphism) (runtimeAt oldVisit sourceIndex boundary) 0 →
      Prop) : Type 32 where
  localLegislation :
    CanonicalSubmissionLocalLegislationAt oldVisit sourceIndex boundary
  targetCoreExact :
    targetCore morphism = generatedU8CoreAt oldVisit sourceIndex boundary
  targetRuntimeExact :
    SourceNativeInquiryRuntime.CofaceRealizationResumptionAt
      (targetCore morphism) (runtimeAt oldVisit sourceIndex boundary) 0
  causalRelation :
    Generates localLegislation targetCoreExact targetRuntimeExact

/-- Every causal relation that requires a same-occurrence local legislation
source has empty factorization fibre.  The target U8 still exists externally;
the no-go rejects only the reversed local-source claim. -/
theorem observerLocalLegislationTargetU8Factorization_isEmpty
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {span :
      SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
        oldVisit sourceIndex boundary}
    {authority :
      SourceNativeObserverConsumerRootedAuthorityAt (sourceSubmission span)}
    (morphism :
      SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphismAt
        span authority)
    (Generates :
      CanonicalSubmissionLocalLegislationAt oldVisit sourceIndex boundary →
      targetCore morphism = generatedU8CoreAt oldVisit sourceIndex boundary →
      SourceNativeInquiryRuntime.CofaceRealizationResumptionAt
        (targetCore morphism) (runtimeAt oldVisit sourceIndex boundary) 0 →
      Prop) :
    IsEmpty
      (ObserverLocalLegislationTargetU8FactorizationAt morphism Generates) :=
  ⟨fun factorization =>
    (sourceLocalLegislation_isEmpty span).false
      factorization.localLegislation⟩

end
end M14SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphism
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphism.sourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphismAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphism.SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphismAt.transportedDisposition_isInstalled
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphism.SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphismAt.transportedInstalledAuthority_source_isInput
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphism.SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphismAt.sourceEffect_commutes_with_rootK
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphism.SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphismAt.targetRuntimeConsumesCore
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphism.SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphismAt.targetCoreAndMacroNextExact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphism.observerLocalLegislationTargetU8Factorization_isEmpty
