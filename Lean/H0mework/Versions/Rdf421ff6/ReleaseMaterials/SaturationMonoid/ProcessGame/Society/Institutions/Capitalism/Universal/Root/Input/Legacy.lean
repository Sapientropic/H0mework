import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Input.Failure
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Transport.ProjectionCofaceRevision

/-! The legacy input branch retains the canonical paid Payment revision.
Its richer world, first write and future law are not regenerated from a
programme payload.  Only the old-root query epoch is transported. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.InputSource

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.TypedSemanticWorldNetworkU8
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation.SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt

variable {Party Good Port Technology Instrument : Type}
  (datum : Datum Party Good Port Technology Instrument)
  (oldVisit : OldVisit) (sourceIndex boundary : Nat)

def originalRevision : FieldGroundedTypedSemanticWorldNetworkRevisionAt
    (FreshPayment.frontier oldVisit sourceIndex boundary).rooted :=
  M14SourceGeneratedPostSettlementObserverSubmissionU8.typedRevisionSourceAt
    oldVisit sourceIndex (boundary + 1)

theorem originalRevision_is_paid_target :
    HEq (originalRevision oldVisit sourceIndex boundary)
      ((targetRevolutionaryConsumption (FreshPayment.span oldVisit sourceIndex boundary)).1.core).revision :=
  HEq.rfl

theorem originalRevision_richer :
    (originalRevision oldVisit sourceIndex boundary).generate.SourceGeneratedFaithfulRicherCofaceRestructuringAt :=
  M14SourceGeneratedPostSettlementObserverSubmissionU8.generatedTypedRevision_richerGroundingAt
    oldVisit sourceIndex (boundary + 1)

def legacyGenerated : GeneratedTypedSemanticWorldNetworkRevisionAt
    (frontier datum oldVisit sourceIndex boundary).rooted :=
  Transport.ProjectionCofaceRevision.generated
    (component datum)
    (FreshPayment.frontier oldVisit sourceIndex boundary).rooted
    (frontier datum oldVisit sourceIndex boundary).rooted
    rfl (HEq.rfl)
    (M14SourceGeneratedPostSettlementObserverSubmissionU8.generatedTypedRevisionAt
      oldVisit sourceIndex (boundary + 1))

set_option maxHeartbeats 1000000 in
def legacySplit :
    (legacyGenerated datum oldVisit sourceIndex boundary).SourceGeneratedFirstWriteGenuineSplitAt := by
  let split := M14SourceGeneratedPostSettlementObserverSubmissionU8.augmentedGeneratedFirstWriteGenuineSplitAt
    oldVisit sourceIndex (boundary + 1)
  exact GeneratedTypedSemanticWorldNetworkRevisionAt.SourceGeneratedFirstWriteGenuineSplitAt.ofCompilerSelectedSplit
    (legacyGenerated datum oldVisit sourceIndex boundary)
    split.successor split.left split.right split.children_distinct split.origin_eq
    split.parent_origin_eq split.split (by rfl)
    split.initialLedgerNoDormant split.targetOriginsCovered

def legacyRevision : FieldGroundedTypedSemanticWorldNetworkRevisionAt
    (frontier datum oldVisit sourceIndex boundary).rooted :=
  FieldGroundedTypedSemanticWorldNetworkRevisionAt.ofSourceGeneratedRestructuring
    (legacyGenerated datum oldVisit sourceIndex boundary)
    ⟨HEq.rfl, ⟨legacySplit datum oldVisit sourceIndex boundary⟩⟩

theorem legacy_retains_original_revised_world :
    HEq (legacyRevision datum oldVisit sourceIndex boundary).generate.newLivingRoot
      (originalRevision oldVisit sourceIndex boundary).generate.newLivingRoot := HEq.rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.InputSource
