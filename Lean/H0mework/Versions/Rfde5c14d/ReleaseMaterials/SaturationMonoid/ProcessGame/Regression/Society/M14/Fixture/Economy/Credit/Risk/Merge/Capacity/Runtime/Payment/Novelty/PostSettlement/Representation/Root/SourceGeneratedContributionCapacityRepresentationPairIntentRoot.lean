import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Novelty.PostSettlement.Representation.Renewal.Source.SourceGeneratedContributionCapacityRepresentationPairIntentProofCarryingRenewal

/-!
# Source-installed pair-intent root

The fixed two-law theory, four semantic projections, and one proof-carrying
renewal coordinate are part of the authority source before an emitter is
supplied.  `ledger` is active at both Bool
currents.  `intent`, `failure`, and `inquiry` are inactive at conservative
ingress `false` and become active only at the first-write target `true`.

The intent payload explicitly carries the source-generated semantic change
from the existing revised-Q boundary row's inherited claim to the ordered-pair
obstruction claim.  The two claims are deliberately unequal; the semantic
change is the visible responsibility bridge, and the later U8 coface is what
creates a new claim-bearing row.  No ledger evolution is falsely advertised
as preserving a changed claim.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityRepresentationPairIntentRoot

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open ConstructiveRoot.ObstructionGeneratedMinimalCoface
open Renewal Legislation
open M9ProofCarryingRenewalInquiryRoot
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityRepresentationClaimWorld
open M14SourceGeneratedContributionCapacityRepresentationPairIntentTheory
open M14SourceGeneratedContributionCapacityRepresentationPairIntentCompiler
open M14SourceGeneratedContributionCapacityRepresentationPairIntentProofCarryingRenewal
open M14SourceGeneratedPostSettlementObserverSubmissionU8

def representationIntentDefaultEntryAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (support : (RepresentationIntentNAt oldVisit sourceIndex boundary).Support) :
    OpenResponsibilityAt
      (RepresentationIntentNAt oldVisit sourceIndex boundary) support :=
  let entry := M9ProofCarryingRenewalU8RevisedWorld.revisedDefaultEntryAt
    (oldRootVisitAt oldVisit sourceIndex boundary) support
  ⟨entry.1, entry.2⟩

@[simp] theorem representationIntentDefaultEntry_target_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    representationIntentDefaultEntryAt oldVisit sourceIndex boundary
        (representationIntentSupportAt oldVisit sourceIndex boundary) =
      representationResidualBearerAt oldVisit sourceIndex boundary :=
  rfl

def representationIntentLawExtensionDispositionAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (support : (RepresentationIntentNAt oldVisit sourceIndex boundary).Support) :
    (RepresentationIntentNAt oldVisit sourceIndex boundary).DispositionAt
      support .lawSurfaceExtension := by
  rcases support with ⟨worldSupport, phase⟩
  cases worldSupport with
  | inl oldSupport => exact ()
  | inr direction =>
      cases direction
      exact GeneratedMinimalCofaceAt.CofaceTargetDispositionAt.ofTarget ()

def representationIntentU7At
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    U7ProducerCalculus
      (RepresentationIntentNAt oldVisit sourceIndex boundary) where
  DemandAt := fun _ => Unit
  generateDemand := fun _ => ()

def representationIntentU7SourceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    U7ActualSuccessorSource
      (RepresentationIntentNAt oldVisit sourceIndex boundary)
      (representationIntentU7At oldVisit sourceIndex boundary) where
  EventAt := SourceGeneratedU7DemandAt
    (representationIntentU7At oldVisit sourceIndex boundary)
  emit := fun obstruction => .canonical obstruction
  demandGeneratedAt := fun event => event
  demandEntryAt := fun {support} {_obstruction} {_demand} _ =>
    representationIntentDefaultEntryAt oldVisit sourceIndex boundary support

def representationIntentTheoryAuditCalculusAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    U7ObstructionEvolutionCalculus
      (RepresentationIntentNAt oldVisit sourceIndex boundary)
      (representationIntentU7At oldVisit sourceIndex boundary) where
  source := representationIntentU7SourceAt oldVisit sourceIndex boundary
  compile := by
    intro support obstruction demand event
    exact
      { disposition := .requiresTheoryAudit
          (representationIntentLawExtensionDispositionAt oldVisit sourceIndex
            boundary support)
        demandEntryDisposition := PUnit.unit }

def representationIntentU7EventAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (representationIntentTheoryAuditCalculusAt oldVisit sourceIndex boundary
    ).source.emit
      (generatedRepresentationObstructionAt oldVisit sourceIndex boundary)

def representationIntentU7GateAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeU7TheoryAuditAt
      (representationIntentTheoryAuditCalculusAt oldVisit sourceIndex boundary)
      (representationIntentU7EventAt oldVisit sourceIndex boundary) :=
  PUnit.unit

def representationIntentInquiryAuditAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeInquiryFrontAuditAt
      (representationIntentU7At oldVisit sourceIndex boundary)
      (representationIntentTheoryAuditCalculusAt oldVisit sourceIndex boundary)
      (representationPairIntentTheoryAt oldVisit sourceIndex boundary)
      (representationIntentSupportAt oldVisit sourceIndex boundary) :=
  .obstructed
    (generatedRepresentationObstructionAt oldVisit sourceIndex boundary)
    (.requiresU8
      (representationIntentU7GateAt oldVisit sourceIndex boundary)
      (representationPairIntentFailureAt oldVisit sourceIndex boundary))

@[simp] theorem representationIntentInquiryAudit_requiresU8
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    representationIntentInquiryAuditAt oldVisit sourceIndex boundary =
      .obstructed
        (generatedRepresentationObstructionAt oldVisit sourceIndex boundary)
        (.requiresU8
          (representationIntentU7GateAt oldVisit sourceIndex boundary)
          (representationPairIntentFailureAt oldVisit sourceIndex boundary)) :=
  rfl

inductive RepresentationIntentProjection
  | ledger
  | intent
  | failure
  | inquiry

/-- Low-universe exact intent payload.  It makes the claim mismatch visible
and accounts for it by the source-generated semantic-change coordinate. -/
structure SourceGeneratedRepresentationIntentPayloadAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) : Type where
  pair : RepresentationPairIntent
  pair_exact : pair =
    actualRepresentationPairIntentAt oldVisit sourceIndex boundary
  semanticChange :
    (RepresentationIntentNAt oldVisit sourceIndex boundary).SemanticChangeAt
      (representationIntentSupportAt oldVisit sourceIndex boundary)
      (representationResidualBearerAt oldVisit sourceIndex boundary).claim
      (generatedRepresentationClaimAt oldVisit sourceIndex boundary)

def sourceGeneratedRepresentationIntentPayloadAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceGeneratedRepresentationIntentPayloadAt oldVisit sourceIndex
      boundary :=
  ⟨actualRepresentationPairIntentAt oldVisit sourceIndex boundary, rfl,
    sourceGeneratedRepresentationSemanticChangeAt oldVisit sourceIndex
      boundary⟩

def representationIntentProjectionLawAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeProjectionLaw
      (representationIntentRestructuringSource oldVisit sourceIndex boundary
        ).toLedgerSource where
  Projection := RepresentationIntentProjection
  ActiveAt := fun projection {current} _ =>
    match projection with
    | .ledger => PUnit
    | .intent | .failure | .inquiry => PLift (current = true)
  InactiveAt := fun projection {current} _ =>
    match projection with
    | .ledger => PEmpty
    | .intent | .failure | .inquiry => PLift (current ≠ true)
  classify := by
    intro projection current occurrence
    cases projection with
    | ledger => exact .inl PUnit.unit
    | intent | failure | inquiry =>
        by_cases current_eq : current = true
        · exact .inl ⟨current_eq⟩
        · exact .inr ⟨current_eq⟩
  PayloadAt := fun projection {current} occurrence active =>
    match projection with
    | .ledger =>
        SourceNativeLedgerEvolutionAt
          (representationIntentSource oldVisit sourceIndex boundary) occurrence
    | .intent =>
        SourceGeneratedRepresentationIntentPayloadAt oldVisit sourceIndex
          boundary
    | .failure =>
        SourceNativeRootExpressibilityFailureTokenAt
          (representationPairIntentFailureAt oldVisit sourceIndex boundary)
          (representationIntentTheoryAuditCalculusAt oldVisit sourceIndex
            boundary)
          (representationIntentU7EventAt oldVisit sourceIndex boundary)
    | .inquiry =>
        SourceNativeInquiryCompilationTokenAt
          (representationIntentDefaultEntryAt oldVisit sourceIndex boundary
            (representationIntentSupportAt oldVisit sourceIndex boundary))
          () (ULift.up.{1, 0} occurrence)
          (representationIntentInquiryAuditAt oldVisit sourceIndex boundary)
          PUnit
  project := by
    intro projection current occurrence active
    cases projection with
    | ledger =>
        exact (representationIntentLedgerCompiler oldVisit sourceIndex boundary
          ).compile occurrence
    | intent =>
        exact sourceGeneratedRepresentationIntentPayloadAt oldVisit sourceIndex
          boundary
    | failure => exact .canonical
    | inquiry => exact .canonical PUnit.unit

def representationIntentIntentActiveAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (representationIntentProjectionLawAt oldVisit sourceIndex boundary
      ).ActiveAt .intent
        (representationIntentEmitted oldVisit sourceIndex boundary true) :=
  ⟨rfl⟩

def representationIntentFailureActiveAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (representationIntentProjectionLawAt oldVisit sourceIndex boundary
      ).ActiveAt .failure
        (representationIntentEmitted oldVisit sourceIndex boundary true) :=
  ⟨rfl⟩

def representationIntentInquiryActiveAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (representationIntentProjectionLawAt oldVisit sourceIndex boundary
      ).ActiveAt .inquiry
        (representationIntentEmitted oldVisit sourceIndex boundary true) :=
  ⟨rfl⟩

@[simp] theorem representationIntentClassifier_intent_true
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (representationIntentProjectionLawAt oldVisit sourceIndex boundary
      ).classify .intent
        (representationIntentEmitted oldVisit sourceIndex boundary true) =
      .inl
        (representationIntentIntentActiveAt oldVisit sourceIndex boundary) := by
  dsimp [representationIntentProjectionLawAt,
    representationIntentIntentActiveAt]
  split
  · apply congrArg Sum.inl
    exact Subsingleton.elim _ _
  · contradiction

@[simp] theorem representationIntentClassifier_failure_true
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (representationIntentProjectionLawAt oldVisit sourceIndex boundary
      ).classify .failure
        (representationIntentEmitted oldVisit sourceIndex boundary true) =
      .inl
        (representationIntentFailureActiveAt oldVisit sourceIndex boundary) := by
  dsimp [representationIntentProjectionLawAt,
    representationIntentFailureActiveAt]
  split
  · apply congrArg Sum.inl
    exact Subsingleton.elim _ _
  · contradiction

@[simp] theorem representationIntentClassifier_inquiry_true
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (representationIntentProjectionLawAt oldVisit sourceIndex boundary
      ).classify .inquiry
        (representationIntentEmitted oldVisit sourceIndex boundary true) =
      .inl
        (representationIntentInquiryActiveAt oldVisit sourceIndex boundary) := by
  dsimp [representationIntentProjectionLawAt,
    representationIntentInquiryActiveAt]
  split
  · apply congrArg Sum.inl
    exact Subsingleton.elim _ _
  · contradiction

def representationIntentBaseAuthoritySourceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeAuthoritySource
      (RepresentationIntentNAt oldVisit sourceIndex boundary)
      (RepresentationIntentVAt oldVisit sourceIndex boundary) where
  restructuringSource :=
    representationIntentRestructuringSource oldVisit sourceIndex boundary
  eventInventoryAdmission :=
    .reflOfNoFaithfulTerminal
      (representationIntentRestructuringSource oldVisit sourceIndex boundary)
      (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface :=
    representationPairIntentTheoryAt oldVisit sourceIndex boundary
  projectionLaw :=
    representationIntentProjectionLawAt oldVisit sourceIndex boundary

def representationIntentAuthoritySourceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeAuthoritySource
      (RepresentationIntentNAt oldVisit sourceIndex boundary)
      (RepresentationIntentVAt oldVisit sourceIndex boundary) :=
  withRenewalProjection
    (representationIntentBaseAuthoritySourceAt oldVisit sourceIndex boundary)
    (representationIntentProofCarryingRenewalLawAt oldVisit sourceIndex
      boundary)

def representationIntentAuthoritativeRootAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeAuthoritativeRootClosure
      (RepresentationIntentNAt oldVisit sourceIndex boundary)
      (RepresentationIntentVAt oldVisit sourceIndex boundary) where
  source := representationIntentAuthoritySourceAt oldVisit sourceIndex boundary
  emitted := representationIntentEmitted oldVisit sourceIndex boundary
  compiler_commutes :=
    representationIntentCompiler_commutes oldVisit sourceIndex boundary

def representationIntentLivingRootAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeLivingRootClosure
      (RepresentationIntentNAt oldVisit sourceIndex boundary)
      (RepresentationIntentVAt oldVisit sourceIndex boundary) :=
  (representationIntentAuthoritativeRootAt oldVisit sourceIndex boundary
    ).toLivingWithoutFaithfulTerminal
      (fun _ => ⟨fun terminal => nomatch terminal⟩)

@[simp] theorem representationIntentRoot_lawSurface_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (representationIntentLivingRootAt oldVisit sourceIndex boundary
      ).source.base.lawSurface =
      representationPairIntentTheoryAt oldVisit sourceIndex boundary :=
  rfl

def representationIntentInitialVisitAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeTemporalVisitAt
      (representationIntentAuthoritativeRootAt oldVisit sourceIndex boundary
        ).toLedgerRoot :=
  .finite
    (representationIntentAuthoritativeRootAt oldVisit sourceIndex boundary
      ).toRoot.initialVisit

def representationIntentActiveVisitAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeTemporalVisitAt
      (representationIntentAuthoritativeRootAt oldVisit sourceIndex boundary
        ).toLedgerRoot :=
  (representationIntentInitialVisitAt oldVisit sourceIndex boundary).next rfl

@[simp] theorem representationIntentInitialVisit_current_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (representationIntentInitialVisitAt oldVisit sourceIndex boundary).current =
      false :=
  rfl

@[simp] theorem representationIntentActiveVisit_current_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (representationIntentActiveVisitAt oldVisit sourceIndex boundary).current =
      true :=
  rfl

def representationIntentProofCarryingRenewalInstallationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  renewalComponent
    (representationIntentBaseAuthoritySourceAt oldVisit sourceIndex boundary)
    (representationIntentProofCarryingRenewalLawAt oldVisit sourceIndex
      boundary)

def representationIntentProofCarryingRenewalRecognitionAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeProofCarryingRenewalRecognitionAt
      (representationIntentLivingRootAt oldVisit sourceIndex boundary)
      ResidualProcess RenewalObserver LocalConsumerAt LocalLifecycleAt
      LocalDispositionAt where
  law := representationIntentProofCarryingRenewalLawAt oldVisit sourceIndex
    boundary
  installation :=
    representationIntentProofCarryingRenewalInstallationAt oldVisit
      sourceIndex boundary

def representationIntentInstalledProofCarryingRenewalAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceInstalledRenewalAt
      (representationIntentProofCarryingRenewalRecognitionAt oldVisit
        sourceIndex boundary)
      (representationIntentActiveVisitAt oldVisit sourceIndex boundary) :=
  SourceInstalledRenewalAt.generate
    (representationIntentProofCarryingRenewalActiveAt oldVisit sourceIndex
      boundary)
    (representationIntentProofCarryingRenewalClassifier_true oldVisit
      sourceIndex boundary)

@[simp] theorem representationIntentInstalledRenewal_sourceEntry_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (representationIntentInstalledProofCarryingRenewalAt oldVisit sourceIndex
      boundary).payload.sourceEntry =
      representationResidualBearerAt oldVisit sourceIndex boundary :=
  rfl

theorem representationIntentInstalledRenewal_originPayload_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    let installed :=
      representationIntentInstalledProofCarryingRenewalAt oldVisit sourceIndex
        boundary
    let origin :=
      representationIntentOriginInstalledProofCarryingRenewalAt oldVisit
        sourceIndex boundary
    installed.payload.sourceSeed = origin.payload.sourceSeed ∧
      installed.payload.consumer = origin.payload.consumer ∧
      installed.payload.disposition = origin.payload.disposition :=
  ⟨rfl, rfl, rfl⟩

theorem representationIntentInstalledRenewal_factorizes
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (representationIntentInstalledProofCarryingRenewalAt oldVisit sourceIndex
      boundary).RootAnswerAndNextFactorizes :=
  (representationIntentInstalledProofCarryingRenewalAt oldVisit sourceIndex
    boundary).rootAnswerAndNext_factorizes

def representationIntentInitialGeneratedAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (representationIntentAuthoritativeRootAt oldVisit sourceIndex boundary
    ).toLedgerRoot.generatedAtTemporalVisit
      (representationIntentInitialVisitAt oldVisit sourceIndex boundary)

def representationIntentInitialBearerRowAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (representationIntentInitialGeneratedAt oldVisit sourceIndex boundary
      ).GeneratedEntryRowAt
        (representationResidualBearerAt oldVisit sourceIndex boundary) :=
  ((representationIntentInitialGeneratedAt oldVisit sourceIndex boundary
    ).canonicalGeneratedEntryRow?
      (representationResidualBearerAt oldVisit sourceIndex boundary)).get
        (by rfl)

def representationIntentInitialBearerAuthorityAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt
      (representationIntentLivingRootAt oldVisit sourceIndex boundary)
      (representationIntentInitialVisitAt oldVisit sourceIndex boundary)
      (representationResidualBearerAt oldVisit sourceIndex boundary) :=
  SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitialRow
    (representationIntentLivingRootAt oldVisit sourceIndex boundary)
    (representationResidualBearerAt oldVisit sourceIndex boundary)
    (representationIntentInitialBearerRowAt oldVisit sourceIndex boundary)

def representationIntentActiveBearerAuthorityAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt
      (representationIntentLivingRootAt oldVisit sourceIndex boundary)
      (representationIntentActiveVisitAt oldVisit sourceIndex boundary)
      (representationResidualBearerAt oldVisit sourceIndex boundary) :=
  (representationIntentInitialBearerAuthorityAt oldVisit sourceIndex boundary
    ).next rfl

theorem representationIntentRoot_directConsumer
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (representationIntentLivingRootAt oldVisit sourceIndex boundary
      ).source.base.lawSurface =
        representationPairIntentTheoryAt oldVisit sourceIndex boundary ∧
      IsEmpty
        ((representationIntentProjectionLawAt oldVisit sourceIndex boundary
          ).ActiveAt .failure
            (representationIntentEmitted oldVisit sourceIndex boundary false)) ∧
      Nonempty
        ((representationIntentProjectionLawAt oldVisit sourceIndex boundary
          ).ActiveAt .failure
            (representationIntentEmitted oldVisit sourceIndex boundary true)) ∧
      Nonempty
        ((RepresentationIntentNAt oldVisit sourceIndex boundary).SemanticChangeAt
          (representationIntentSupportAt oldVisit sourceIndex boundary)
          (representationResidualBearerAt oldVisit sourceIndex boundary).claim
          (generatedRepresentationClaimAt oldVisit sourceIndex boundary)) ∧
      (representationResidualBearerAt oldVisit sourceIndex boundary).claim ≠
        (RepresentationIntentNAt oldVisit sourceIndex boundary).obstructionClaim
          (generatedRepresentationObstructionAt oldVisit sourceIndex boundary) ∧
      type_of% (representationIntentInquiryAudit_requiresU8 oldVisit sourceIndex
        boundary) ∧
      Nonempty
        (SourceNativeLivingTemporalCausalEntryAuthorityAt
          (representationIntentLivingRootAt oldVisit sourceIndex boundary)
          (representationIntentActiveVisitAt oldVisit sourceIndex boundary)
          (representationResidualBearerAt oldVisit sourceIndex boundary)) :=
  ⟨rfl, ⟨fun active => nomatch active⟩, ⟨⟨rfl⟩⟩,
    ⟨sourceGeneratedRepresentationSemanticChangeAt oldVisit sourceIndex
      boundary⟩,
    representationResidualBearer_claim_ne_obstructionClaim oldVisit sourceIndex
      boundary,
    representationIntentInquiryAudit_requiresU8 oldVisit sourceIndex boundary,
    ⟨representationIntentActiveBearerAuthorityAt oldVisit sourceIndex
      boundary⟩⟩

end
end M14SourceGeneratedContributionCapacityRepresentationPairIntentRoot
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentRoot.representationIntentTheoryAuditCalculusAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentRoot.representationIntentProjectionLawAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentRoot.representationIntentLivingRootAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentRoot.representationIntentInstalledProofCarryingRenewalAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentRoot.representationIntentInstalledRenewal_originPayload_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentRoot.representationIntentActiveBearerAuthorityAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentRoot.representationIntentRoot_directConsumer
