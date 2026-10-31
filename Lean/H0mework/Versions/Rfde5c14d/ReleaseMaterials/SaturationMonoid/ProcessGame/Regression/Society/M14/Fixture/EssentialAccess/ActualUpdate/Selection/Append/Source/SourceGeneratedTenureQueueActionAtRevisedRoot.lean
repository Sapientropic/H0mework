import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.U8.Revised.Continuation.SourceGeneratedCriticalEventSelectionRevisedContinuation
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Source.Queue.SourceGeneratedEssentialAccessCriticalActionQueue
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccessPaymentPurposeFixture

/-!
# First queue action at the revised root

The first exact M10 queue occurrence generates tenure.  This file ties that
private carrier to the revised root's exact depth-two event, new-only living
entry authority and historically inherited UBI restriction.  The historical
UBI payload is not reissued as a revised Payment or ledger write; it supplies
the already generated tenure-purpose seam only.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedTenureQueueActionAtRevisedRoot

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Renewal
open M10OccurrenceCapacityProcessFixture
open M14EssentialAccessRelationFixture
open M14EssentialAccessPaymentPurposeLaw
open M14EssentialAccessPaymentPurposeFixture
open M14UBIProofCarryingRootRestriction
open M14SourceEssentialServiceRestoration
open M14SourceGeneratedHealthCessationTargetRoot
open M14SourceGeneratedCriticalEventSelectionRevisedLedger
open M14SourceGeneratedCriticalEventSelectionRevisedRoot
open M14SourceGeneratedCriticalEventSelectionRevisedContinuation
open M14SourceGeneratedEssentialAccessCriticalActionQueue

def revisedDepthTwoEvent := revisedSelectionExactEventAt 2

def revisedDepthTwoInheritedUBIPayload :=
  revisedProjectionLaw.project revisedInheritedUBIProjection
    (revisedEmitted (revisedSelectionRootVisitAt 2).current) PUnit.unit

def oldHealthTargetDepthOneInstalledUBI : SourceInstalledRenewalAt
    M9SourceHealthCessationSuffix.ubiRecognition
      (M14SourceGeneratedHealthCessationTargetHistory.healthCessationTargetTemporalVisitAt 1) :=
  SourceInstalledRenewalAt.generate PUnit.unit rfl

theorem revisedDepthTwoInheritedUBIPayload_exact :
    HEq revisedDepthTwoInheritedUBIPayload
      oldHealthTargetDepthOneInstalledUBI.payload :=
  HEq.rfl

@[simp] theorem revisedDepthTwoInheritedUBIConsumer_exact :
    revisedDepthTwoInheritedUBIPayload.consumer =
      sourceGeneratedUBIRootRestriction :=
  rfl

@[simp] theorem revisedDepthTwoInheritedUBIDisposition_exact :
    revisedDepthTwoInheritedUBIPayload.disposition =
      sourceGeneratedUBIDisposition :=
  rfl

theorem revisedDepthTwoInheritedUBI_factorizes :
    oldHealthTargetDepthOneInstalledUBI.RootAnswerAndNextFactorizes :=
  oldHealthTargetDepthOneInstalledUBI.rootAnswerAndNext_factorizes

@[simp] theorem firstQueueSourceSeed_eq_inheritedUBI :
    firstExactUnit.sourceSeed serviceQueueCompiler =
      revisedDepthTwoInheritedUBIPayload.sourceSeed :=
  rfl

@[simp] theorem tenureQueueActionSeed_exact :
    sourceGeneratedTenureCriticalActionQueue.action.criticalBearer.bearerLineage.seed =
      exactEssentialAccessSeed EssentialAccessEvent.tenure :=
  queueAction_actionSeed_exact sourceGeneratedTenureCriticalActionQueue

/-- Private tether consumed by the first sequential append program. -/
structure SourceGeneratedTenureQueueActionAtRevisedRoot : Type 12 where
  private mk ::
  exactSource : ExactTemporalCausalRootEventAt
    revisedAuthoritativeRoot.toLedgerRoot
      (revisedSelectionTemporalVisitAt 2)
  exactSourceCanonical : exactSource = revisedDepthTwoEvent
  sourceEntry : OpenResponsibilityAt NewN minimalCoface.cofaceSupport
  sourceEntryExact : sourceEntry = revisedSelectionEntryAt 2
  sourceAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt
    revisedLivingRoot (revisedSelectionTemporalVisitAt 2) sourceEntry
  sourceAuthorityExact : HEq sourceAuthority
    (revisedSelectionAuthorityAt 2)
  queueAction :
    SourceGeneratedEssentialAccessCriticalActionQueueAt firstExactUnit
  queueActionExact : queueAction = sourceGeneratedTenureCriticalActionQueue
  queueSeedCommutes :
    firstExactUnit.sourceSeed serviceQueueCompiler =
      revisedDepthTwoInheritedUBIPayload.sourceSeed
  historicalUBIPayload : type_of% revisedDepthTwoInheritedUBIPayload
  historicalUBIPayloadExact : historicalUBIPayload =
    revisedDepthTwoInheritedUBIPayload
  historicalUBIFactorization :
    oldHealthTargetDepthOneInstalledUBI.RootAnswerAndNextFactorizes
  tenurePurposeExact :
    sourceGeneratedUBIDisposition.sourceFailure.paymentPurpose =
      exactTenurePaymentPurpose
  actionSeedExact :
    queueAction.action.criticalBearer.bearerLineage.seed =
      exactEssentialAccessSeed .tenure

def sourceGeneratedTenureQueueActionAtRevisedRoot :
    SourceGeneratedTenureQueueActionAtRevisedRoot where
  exactSource := revisedDepthTwoEvent
  exactSourceCanonical := rfl
  sourceEntry := revisedSelectionEntryAt 2
  sourceEntryExact := rfl
  sourceAuthority := revisedSelectionAuthorityAt 2
  sourceAuthorityExact := HEq.rfl
  queueAction := sourceGeneratedTenureCriticalActionQueue
  queueActionExact := rfl
  queueSeedCommutes := firstQueueSourceSeed_eq_inheritedUBI
  historicalUBIPayload := revisedDepthTwoInheritedUBIPayload
  historicalUBIPayloadExact := rfl
  historicalUBIFactorization := revisedDepthTwoInheritedUBI_factorizes
  tenurePurposeExact := rootSourceCarriesExactTenurePaymentPurpose
  actionSeedExact := tenureQueueActionSeed_exact

theorem tenureQueueActionAtRevisedRoot_directConsumer :
    let source := sourceGeneratedTenureQueueActionAtRevisedRoot
    source.exactSource = revisedSelectionExactEventAt 2 ∧
      source.sourceEntry = revisedSelectionEntryAt 2 ∧
      source.queueAction.event = EssentialAccessEvent.tenure ∧
      source.queueAction.action.criticalBearer.bearerLineage.seed =
        exactEssentialAccessSeed EssentialAccessEvent.tenure ∧
      sourceGeneratedUBIDisposition.sourceFailure.paymentPurpose =
        exactTenurePaymentPurpose ∧
      oldHealthTargetDepthOneInstalledUBI.RootAnswerAndNextFactorizes :=
  ⟨rfl, rfl, rfl, tenureQueueActionSeed_exact,
    rootSourceCarriesExactTenurePaymentPurpose,
    revisedDepthTwoInheritedUBI_factorizes⟩

end
end M14SourceGeneratedTenureQueueActionAtRevisedRoot
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedTenureQueueActionAtRevisedRoot.sourceGeneratedTenureQueueActionAtRevisedRoot
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedTenureQueueActionAtRevisedRoot.tenureQueueActionAtRevisedRoot_directConsumer
