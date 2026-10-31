import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Legislation.StructuralExploitationLegislationRegression

/-!
# M14 proof-carrying recognition witness escape

The third pre-emitter coordinate of the literal M9/M14 root publishes the
root-independent structural-exploitation witness at the exact hidden standing
of the PCL authority kernel.  The coarse observer remains non-faithful.  The
published bit, whose truth is equivalent to source-witness inhabitation,
strictly separates the two exact kernel endpoints and supports a posterior
faithful reconstruction of the complete fixed `ActualPath` carrier.

The publication source contains neither an occurrence payload nor authority
`K`; occurrence and authority reconstruction are downstream theorems.  No
second occurrence family, root, ledger, witness registry, observer oracle, or
completed future is introduced.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingRecognitionWitnessEscapeRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open Lifecycle Universal Observer Renewal Legislation Revision
open UBI.Policy
open Go.CrossOccurrenceClassicalResidual
open M3FiniteExchangeFixture
open M3ExchangeSettlementPriceRegression
open M6GoNaturalAuthorityReconstructionRegression
open M8RelationshipMaintenanceFixture
open M8RelationshipMaintenanceRenewalRegression
open M9ProofCarryingRenewalInquiryRoot
open M9ProofCarryingRenewalInquiryRuntime
open M9ProofCarryingLegislationRegression
open M14StructuralExploitationWitness
open M14RecognitionWitnessPublication
open M14UBIProofCarryingLegislationRegression
open M14StructuralExploitationLegislationRegression
open M14EssentialAccessSectorRegression
open M14TenureCaptureRouteRepairNoGoRegression
open M14ProofCarryingExitRepairRegression

/-! ## Installed escape seal -/

/-- Zero-choice seal indexed by the actual installed publication coordinate.
The producer can receive no witness verdict, hidden standing, observer,
decoder, factorization, repair, branch, or next. -/
structure SourceGeneratedProofCarryingRecognitionWitnessEscapeAt
    (installed : SourceInstalledRenewalAt recognitionWitnessRecognition
      jointVisit) : Type 14 where
  private mk ::

def SourceGeneratedProofCarryingRecognitionWitnessEscapeAt.generate
    (installed : SourceInstalledRenewalAt recognitionWitnessRecognition
      jointVisit) :
    SourceGeneratedProofCarryingRecognitionWitnessEscapeAt installed :=
  ⟨⟩

def sourceGeneratedProofCarryingRecognitionWitnessEscape :
    SourceGeneratedProofCarryingRecognitionWitnessEscapeAt
      installedRecognitionWitness :=
  SourceGeneratedProofCarryingRecognitionWitnessEscapeAt.generate
    installedRecognitionWitness

namespace SourceGeneratedProofCarryingRecognitionWitnessEscapeAt

variable {installed : SourceInstalledRenewalAt recognitionWitnessRecognition
  jointVisit}
variable (escape : SourceGeneratedProofCarryingRecognitionWitnessEscapeAt
  installed)

include escape

/-- Source witness read from the installed coordinate. -/
def sourceWitness : SourceGeneratedStructuralExploitationWitnessAt
    relationshipRenewalSeed := by
  cases escape
  exact installed.payload.consumer

/-- Actual pre-emitter disposition and its honest total publication law. -/
def publicationDisposition :
    RecognitionWitnessDispositionAt relationshipRenewalSeed := by
  cases escape
  exact installed.payload.disposition

def publicationLaw : SourceWitnessPublicationAt RecognitionWitnessAt :=
  escape.publicationDisposition.publicationLaw

@[simp] theorem publicationLaw_eq_sourceLaw :
    escape.publicationLaw = recognitionWitnessPublicationLaw := by
  cases escape
  rfl

/-- The PCL kernel carried by the first coordinate remains the authoritative
coarse fibre. -/
def coarseKernel : AuthorityKernelPair (goAuthorityObserver 1) :=
  by
    cases escape
    exact proofCarryingLegislation.observerKernel

@[simp] theorem coarseKernel_left_eq_hiddenStanding :
    escape.coarseKernel.left = proofCarryingLegislation.hiddenStanding :=
  proofCarryingLegislation.observerKernel_left_eq_hiddenStanding

@[simp] theorem coarseKernel_left_eq_koPath :
    escape.coarseKernel.left = koPath := by
  rw [escape.coarseKernel_left_eq_hiddenStanding]
  rfl

@[simp] theorem coarseKernel_right_eq_freshPath :
    escape.coarseKernel.right = freshPath := by
  change verticalSwap koPath = freshPath
  exact verticalSwap_ko

/-- Exact installed publication refines the exact PCL kernel. -/
theorem kernelRefinement :
    SourceWitnessKernelRefinementAt escape.publicationLaw
      escape.coarseKernel := by
  apply sourceWitnessKernelRefinement
  · rw [escape.coarseKernel_left_eq_koPath]
    exact ⟨escape.publicationDisposition.exactPublication⟩
  · rw [escape.coarseKernel_right_eq_freshPath]
    exact kernelRight_has_no_sourceWitness

/-- Refined observer reads only the installed publication bit in addition to
the unchanged normalized image. -/
def refinedObserver :=
  sourceWitnessRefinedObserver (goAuthorityObserver 1) escape.publicationLaw

@[simp] theorem publicationTag_ko :
    escape.publicationLaw.publicationTag koPath = true := by
  rw [escape.publicationLaw_eq_sourceLaw]
  exact witnessPublicationTag_ko

@[simp] theorem publicationTag_fresh :
    escape.publicationLaw.publicationTag freshPath = false := by
  rw [escape.publicationLaw_eq_sourceLaw]
  exact witnessPublicationTag_fresh

theorem coarse_observer_remains_nonfaithful :
    (goAuthorityObserver 1).forget escape.coarseKernel.left =
        (goAuthorityObserver 1).forget escape.coarseKernel.right ∧
      (goAuthorityObserver 1).authorityK escape.coarseKernel.left ≠
        (goAuthorityObserver 1).authorityK escape.coarseKernel.right ∧
      ¬ Nonempty (AuthorityFactorization (goAuthorityObserver 1)) :=
  ⟨escape.coarseKernel.visible_eq, escape.coarseKernel.authority_ne,
    escape.coarseKernel.noAuthorityFactorization⟩

/-- Positive kernel escape: publication leaves the old coarse image intact
but separates the exact endpoints in the refined visible carrier. -/
theorem witness_refines_exact_kernel :
    (goAuthorityObserver 1).forget escape.coarseKernel.left =
        (goAuthorityObserver 1).forget escape.coarseKernel.right ∧
      escape.refinedObserver.forget escape.coarseKernel.left ≠
        escape.refinedObserver.forget escape.coarseKernel.right :=
  ⟨escape.kernelRefinement.coarseVisible_eq,
    escape.kernelRefinement.refinedVisible_ne⟩

/-- Publication itself is not reconstructible from the old normalized image. -/
theorem publication_not_coarse_factorizable :
    ¬ ∃ readPublication : NormalizedImage 1 → Bool,
      ∀ path : ActualPath,
        readPublication (normalizedForget 1 path) =
          escape.publicationLaw.publicationTag path := by
  rintro ⟨readPublication, factorizes⟩
  exact escape.kernelRefinement.publicationTag_ne <| by
    calc
      escape.publicationLaw.publicationTag escape.coarseKernel.left =
          readPublication
            (normalizedForget 1 escape.coarseKernel.left) :=
        (factorizes escape.coarseKernel.left).symm
      _ = readPublication
            (normalizedForget 1 escape.coarseKernel.right) :=
        congrArg readPublication escape.coarseKernel.visible_eq
      _ = escape.publicationLaw.publicationTag escape.coarseKernel.right :=
        factorizes escape.coarseKernel.right

/-! ## Full fixed-ActualPath reconstruction -/

abbrev RefinedVisible := SourceWitnessRefinedVisible (NormalizedImage 1)

/-- Posterior decoder.  It reads only the public bit; the normalized image is
the existing singleton image. -/
def reconstructPath (visible : RefinedVisible) : ActualPath :=
  match visible.witnessPublished with
  | true => koPath
  | false => freshPath

def readRefinedAuthority (visible : RefinedVisible) : Go.TacticalPhase :=
  pathAuthorityK (reconstructPath visible)

theorem reconstructPath_recoversVisible (visible : RefinedVisible) :
    escape.refinedObserver.forget (reconstructPath visible) = visible := by
  rcases visible with ⟨coarse, published⟩
  cases coarse
  cases published
  · exact congrArg₂ SourceWitnessRefinedVisible.mk rfl
      escape.publicationTag_fresh
  · exact congrArg₂ SourceWitnessRefinedVisible.mk rfl
      escape.publicationTag_ko

@[simp] theorem reconstructPath_refined_ko :
    reconstructPath (escape.refinedObserver.forget koPath) = koPath := by
  change (match escape.publicationLaw.publicationTag koPath with
    | true => koPath
    | false => freshPath) = koPath
  rw [escape.publicationTag_ko]

@[simp] theorem reconstructPath_refined_fresh :
    reconstructPath (escape.refinedObserver.forget freshPath) = freshPath := by
  change (match escape.publicationLaw.publicationTag freshPath with
    | true => koPath
    | false => freshPath) = freshPath
  rw [escape.publicationTag_fresh]

theorem reconstructPath_recoversOccurrence (path : ActualPath) :
    reconstructPath (escape.refinedObserver.forget path) = path := by
  fin_cases path
  · exact escape.reconstructPath_refined_ko
  · exact escape.reconstructPath_refined_fresh

theorem readRefinedAuthority_preserves (path : ActualPath) :
    readRefinedAuthority (escape.refinedObserver.forget path) =
      (goAuthorityObserver 1).authorityK path := by
  rw [show readRefinedAuthority (escape.refinedObserver.forget path) =
      pathAuthorityK (reconstructPath
        (escape.refinedObserver.forget path)) from rfl,
    escape.reconstructPath_recoversOccurrence path]
  rfl

/-- Full reconstruction of the actual two-path carrier, not merely the Bool
restriction used in the generic regression. -/
def faithfulRecognitionReconstruction :
    FaithfulAuthorityReconstruction escape.refinedObserver where
  lift := reconstructPath
  lift_forget := escape.reconstructPath_recoversVisible
  readAuthority := readRefinedAuthority
  preservesActualAuthority := escape.readRefinedAuthority_preserves
  recoversOccurrence := escape.reconstructPath_recoversOccurrence

def refinedAuthorityFactorization :
    AuthorityFactorization escape.refinedObserver :=
  escape.faithfulRecognitionReconstruction.toAuthorityFactorization

/-! ## Same-root publication authority -/

theorem source_witness_is_shared_with_legislation :
    escape.sourceWitness =
      structuralExploitationLegislation.sourceWitness :=
  rfl

/-- The same root seed carries both the structural witness's relationship
consumer and the PCL vertical kernel; publication is not a later arbitrary
pairing of unrelated assets. -/
theorem source_witness_is_pcl_relationship_consumer :
    escape.sourceWitness.relationshipConsumer =
      proofCarryingLegislation.localResponsibilityConsumer.existingLocalConsumer :=
  rfl

theorem source_failure_is_shared_with_ubi_disposition :
    escape.sourceWitness.sourceFailure =
      installedUBI.payload.disposition.sourceFailure :=
  rfl

theorem publication_root_row_ledger_commutes :
    Nonempty (SourceGeneratedProofCarryingRecognitionWitnessEscapeAt
        installed) ∧
      installed.payload.sourceEntry = installedRenewal.payload.sourceEntry ∧
      HEq installed.payload.selectedRow installedRenewal.payload.selectedRow ∧
      HEq installed.payload.successor installedRenewal.payload.successor ∧
      HEq
        ((sourceGeneratedRuntimeInquiryCoordinateAt jointRuntime 0).1.state.base.root
          |>.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
            (sourceGeneratedRuntimeInquiryCoordinateAt jointRuntime 0).1.state.base.visit)
        (jointRoot.toAuthoritativeRoot.toLedgerRoot
          |>.exactTemporalCausalEventAt jointVisit) ∧
      (jointRoot.toAuthoritativeRoot.toLedgerRoot
        |>.generatedAtTemporalVisit jointVisit).wholeLedgerWriteBack =
        proofCarryingLegislation.wholeLedgerWriteBack ∧
      installed.RootAnswerAndNextFactorizes := by
  exact ⟨⟨escape⟩, rfl, HEq.rfl, HEq.rfl,
    inquiryOccurrence_is_literalInstalledOccurrence, rfl,
    installed.rootAnswerAndNext_factorizes⟩

/-- Publication does not select an institutional branch.  Existing ordinary
repair and automatic self-U8 remain strictly different nexts. -/
theorem publication_does_not_choose_revision_branch :
    Nonempty (SourceGeneratedProofCarryingRecognitionWitnessEscapeAt
        installed) ∧
      proofCarryingLegislation.revisionKind =
        SourceGeneratedInstitutionalRevisionKind.revolution ∧
      (⟨M9ProofCarryingRenewalInquiryRoot.N,
        sourceGeneratedUBIProofCarryingLegislation.ordinaryRepair.generatedNext⟩ :
          AnyAuthoritativeRootCurrent) ≠
        proofCarryingLegislation.generatedNext :=
  ⟨⟨escape⟩, automatic_revisionKind_is_revolution,
    sourceGeneratedUBIProofCarryingLegislation
      |>.ordinary_and_revolutionary_nexts_distinct⟩

end SourceGeneratedProofCarryingRecognitionWitnessEscapeAt

/-! ## Direct certificate and negative controls -/

structure ProofCarryingRecognitionWitnessEscapeCertificate : Prop where
  standing : Nonempty
    (SourceGeneratedProofCarryingRecognitionWitnessEscapeAt
      installedRecognitionWitness)
  installedConsumerExact :
    installedRecognitionWitness.payload.consumer =
      sourceGeneratedStructuralExploitationWitness
  installedDispositionExact :
    installedRecognitionWitness.payload.disposition =
      recognitionWitnessDisposition
  publicationTagHonest : ∀ path : ActualPath,
    (sourceGeneratedProofCarryingRecognitionWitnessEscape
      |>.publicationLaw).publicationTag path = true ↔
      Nonempty (RecognitionWitnessAt path)
  sourceSharedWithLegislation :
    sourceGeneratedProofCarryingRecognitionWitnessEscape.sourceWitness =
      structuralExploitationLegislation.sourceWitness
  sourceRelationshipIsPCLConsumer :
    (sourceGeneratedProofCarryingRecognitionWitnessEscape
      |>.sourceWitness).relationshipConsumer =
      proofCarryingLegislation.localResponsibilityConsumer.existingLocalConsumer
  kernelLeftWitness : Nonempty (RecognitionWitnessAt
    sourceGeneratedProofCarryingRecognitionWitnessEscape.coarseKernel.left)
  kernelRightWitnessEmpty : IsEmpty (RecognitionWitnessAt
    sourceGeneratedProofCarryingRecognitionWitnessEscape.coarseKernel.right)
  coarseStillNonfaithful :
    ¬ Nonempty (AuthorityFactorization (goAuthorityObserver 1))
  coarseKernelStillExact :
    (goAuthorityObserver 1).forget
          sourceGeneratedProofCarryingRecognitionWitnessEscape.coarseKernel.left =
        (goAuthorityObserver 1).forget
          sourceGeneratedProofCarryingRecognitionWitnessEscape.coarseKernel.right ∧
      (goAuthorityObserver 1).authorityK
          sourceGeneratedProofCarryingRecognitionWitnessEscape.coarseKernel.left ≠
        (goAuthorityObserver 1).authorityK
          sourceGeneratedProofCarryingRecognitionWitnessEscape.coarseKernel.right
  refinedVisibleSeparates :
    sourceGeneratedProofCarryingRecognitionWitnessEscape.refinedObserver.forget
        sourceGeneratedProofCarryingRecognitionWitnessEscape.coarseKernel.left ≠
      sourceGeneratedProofCarryingRecognitionWitnessEscape.refinedObserver.forget
        sourceGeneratedProofCarryingRecognitionWitnessEscape.coarseKernel.right
  fullActualPathReconstruction : Nonempty
    (FaithfulAuthorityReconstruction
      sourceGeneratedProofCarryingRecognitionWitnessEscape.refinedObserver)
  refinedAuthorityFactors : Nonempty
    (AuthorityFactorization
      sourceGeneratedProofCarryingRecognitionWitnessEscape.refinedObserver)
  publicationNotCoarseFactorizable :
    ¬ ∃ readPublication : NormalizedImage 1 → Bool,
      ∀ path : ActualPath,
        readPublication (normalizedForget 1 path) =
          (sourceGeneratedProofCarryingRecognitionWitnessEscape
            |>.publicationLaw).publicationTag path
  rootRowLedger :
    installedRecognitionWitness.payload.sourceEntry =
        installedRenewal.payload.sourceEntry ∧
      HEq installedRecognitionWitness.payload.selectedRow
        installedRenewal.payload.selectedRow ∧
      HEq installedRecognitionWitness.payload.successor
        installedRenewal.payload.successor ∧
      installedRecognitionWitness.RootAnswerAndNextFactorizes
  exactRootOccurrence : HEq
    ((sourceGeneratedRuntimeInquiryCoordinateAt jointRuntime 0).1.state.base.root
      |>.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
        (sourceGeneratedRuntimeInquiryCoordinateAt jointRuntime 0).1.state.base.visit)
    (jointRoot.toAuthoritativeRoot.toLedgerRoot
      |>.exactTemporalCausalEventAt jointVisit)
  wholeLedgerShared :
    (jointRoot.toAuthoritativeRoot.toLedgerRoot
      |>.generatedAtTemporalVisit jointVisit).wholeLedgerWriteBack =
      proofCarryingLegislation.wholeLedgerWriteBack
  coordinatesDistinct :
    jointRecognitionWitnessProjection ≠ jointUBIProjection ∧
      jointRecognitionWitnessProjection ≠ jointProofCarryingProjection
  sourceFailureSharedWithUBI :
    sourceGeneratedProofCarryingRecognitionWitnessEscape.sourceWitness.sourceFailure =
      installedUBI.payload.disposition.sourceFailure
  automaticBranchUnchanged :
    proofCarryingLegislation.revisionKind =
      SourceGeneratedInstitutionalRevisionKind.revolution
  ordinaryAndRevolutionaryNextsDistinct :
    (⟨M9ProofCarryingRenewalInquiryRoot.N,
      sourceGeneratedUBIProofCarryingLegislation.ordinaryRepair.generatedNext⟩ :
        AnyAuthoritativeRootCurrent) ≠
      proofCarryingLegislation.generatedNext
  noRelationshipTraceNoWitness :
    (¬ ∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
      Lifecycle.Universal.FixedAdapter.targetFace.SeedAt
        Lifecycle.actualEventGame.source state relationshipRenewalFace.event) →
      IsEmpty (SourceGeneratedStructuralExploitationWitnessAt
        relationshipRenewalSeed)
  noRelationshipTraceNoPublication :
    (¬ ∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
      Lifecycle.Universal.FixedAdapter.targetFace.SeedAt
        Lifecycle.actualEventGame.source state relationshipRenewalFace.event) →
      IsEmpty (RecognitionWitnessDispositionAt relationshipRenewalSeed)
  noForwardControlNoWitness :
    IsEmpty (M8RelationshipMaintenanceFixture.SelectedMaintenanceControlAt
      relationshipRenewalFace.event .a (counterparty .a)) →
      IsEmpty (SourceGeneratedStructuralExploitationWitnessAt
        relationshipRenewalSeed)
  noForwardControlNoPublication :
    IsEmpty (M8RelationshipMaintenanceFixture.SelectedMaintenanceControlAt
      relationshipRenewalFace.event .a (counterparty .a)) →
      IsEmpty (RecognitionWitnessDispositionAt relationshipRenewalSeed)
  noForwardDebtNoWitness :
    IsEmpty (M8RelationshipMaintenanceFixture.SelectedMaintenanceDebtFlowAt
      relationshipRenewalFace.event .a (counterparty .a)) →
      IsEmpty (SourceGeneratedStructuralExploitationWitnessAt
        relationshipRenewalSeed)
  noForwardDebtNoPublication :
    IsEmpty (M8RelationshipMaintenanceFixture.SelectedMaintenanceDebtFlowAt
      relationshipRenewalFace.event .a (counterparty .a)) →
      IsEmpty (RecognitionWitnessDispositionAt relationshipRenewalSeed)
  noPaymentPurposeTraceNoPublication :
    (¬ ∃ purposeSeed :
      M14EssentialAccessRelationFixture.essentialAccessRelationCompiler.ExactRelationSeed,
      (∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
        state = Lifecycle.Universal.FixedAdapter.core.targetFace.state
          Lifecycle.actualEventGame.source ∧
        M14EssentialAccessRelationFixture.essentialAccessRelationCompiler.relationSeedAt
          Lifecycle.actualEventGame.source state purposeSeed.1 ∧
        Lifecycle.Universal.FixedAdapter.core.targetFace.SeedAt
          Lifecycle.actualEventGame.source state
          (M14EssentialAccessRelationFixture.essentialAccessRelationCompiler
            |>.beneficiaryActorSeed purposeSeed.1)) ∧
      purposeSeed.actor
          M14EssentialAccessRelationFixture.essentialAccessRelationCompiler =
        Money.exactCounterpartyActor exactResidualActivation ∧
      M14EssentialAccessRelationFixture.essentialAccessRelationCompiler.relationOf
          purposeSeed = M14EssentialAccessRelationFixture.tenureRelation) →
      IsEmpty (RecognitionWitnessDispositionAt relationshipRenewalSeed)
  uncapturedForgeryEmpty :
    IsEmpty UncapturedStructuralExploitationWitnessForgery
  fullyFulfilledForgeryEmpty :
    IsEmpty FullyFulfilledStructuralExploitationWitnessForgery
  coarseBeneficiaryCannotRecoverAuthority :
    ¬ ∃ reconstruct : M3FiniteExchangeFixture.V.ProtectedInterest →
        EssentialAccessRelationAuthority,
      Function.LeftInverse reconstruct protectedInterestReadout
  capacityCannotSelectRepair :
    ¬ ∃ reconstruct : Nat → ExactExitRepair,
      ∀ origin : RepairFailureOriginAt 0,
        reconstruct (failureCapacityReadoutAt 0 origin) =
          canonicalRepairAt origin

theorem proofCarryingRecognitionWitnessEscapeDirectConsumer :
    ProofCarryingRecognitionWitnessEscapeCertificate := by
  let escape := sourceGeneratedProofCarryingRecognitionWitnessEscape
  let refinement := escape.kernelRefinement
  exact
    { standing := ⟨escape⟩
      installedConsumerExact := installedRecognitionWitness_consumer_eq
      installedDispositionExact := installedRecognitionWitness_disposition_eq
      publicationTagHonest := escape.publicationLaw.publicationTag_eq_true_iff
      sourceSharedWithLegislation :=
        escape.source_witness_is_shared_with_legislation
      sourceRelationshipIsPCLConsumer :=
        escape.source_witness_is_pcl_relationship_consumer
      kernelLeftWitness := refinement.leftWitness
      kernelRightWitnessEmpty := refinement.rightWitnessEmpty
      coarseStillNonfaithful :=
        escape.coarse_observer_remains_nonfaithful.2.2
      coarseKernelStillExact :=
        ⟨escape.coarse_observer_remains_nonfaithful.1,
          escape.coarse_observer_remains_nonfaithful.2.1⟩
      refinedVisibleSeparates := escape.witness_refines_exact_kernel.2
      fullActualPathReconstruction :=
        ⟨escape.faithfulRecognitionReconstruction⟩
      refinedAuthorityFactors := ⟨escape.refinedAuthorityFactorization⟩
      publicationNotCoarseFactorizable :=
        escape.publication_not_coarse_factorizable
      rootRowLedger :=
        ⟨(escape.publication_root_row_ledger_commutes).2.1,
          (escape.publication_root_row_ledger_commutes).2.2.1,
          (escape.publication_root_row_ledger_commutes).2.2.2.1,
          (escape.publication_root_row_ledger_commutes).2.2.2.2.2.2⟩
      exactRootOccurrence :=
        (escape.publication_root_row_ledger_commutes).2.2.2.2.1
      wholeLedgerShared :=
        (escape.publication_root_row_ledger_commutes).2.2.2.2.2.1
      coordinatesDistinct :=
        ⟨recognitionWitness_projection_ne_ubi_projection,
          recognitionWitness_projection_ne_proofCarrying_projection⟩
      sourceFailureSharedWithUBI :=
        escape.source_failure_is_shared_with_ubi_disposition
      automaticBranchUnchanged :=
        escape.publication_does_not_choose_revision_branch.2.1
      ordinaryAndRevolutionaryNextsDistinct :=
        escape.publication_does_not_choose_revision_branch.2.2
      noRelationshipTraceNoWitness :=
        noRelationshipTrace_noStructuralExploitationWitness
      noRelationshipTraceNoPublication := fun noTrace =>
        noStructuralWitness_noPublication
          (noRelationshipTrace_noStructuralExploitationWitness noTrace)
      noForwardControlNoWitness :=
        noForwardControl_noStructuralExploitationWitness
      noForwardControlNoPublication := fun noControl =>
        noStructuralWitness_noPublication
          (noForwardControl_noStructuralExploitationWitness noControl)
      noForwardDebtNoWitness :=
        noForwardDebt_noStructuralExploitationWitness
      noForwardDebtNoPublication := fun noDebt =>
        noStructuralWitness_noPublication
          (noForwardDebt_noStructuralExploitationWitness noDebt)
      noPaymentPurposeTraceNoPublication := fun noTrace =>
        noStructuralWitness_noPublication
          (noPaymentPurposeTrace_noStructuralExploitationWitness noTrace)
      uncapturedForgeryEmpty :=
        uncapturedStructuralExploitationWitnessForgery_isEmpty
      fullyFulfilledForgeryEmpty :=
        fullyFulfilledStructuralExploitationWitnessForgery_isEmpty
      coarseBeneficiaryCannotRecoverAuthority :=
        no_protectedInterest_authority_reconstruction
      capacityCannotSelectRepair :=
        sourceGeneratedUBIProofCarryingLegislation
          |>.capacity_observer_cannot_legislate_repair }

end
end M14ProofCarryingRecognitionWitnessEscapeRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingRecognitionWitnessEscapeRegression.SourceGeneratedProofCarryingRecognitionWitnessEscapeAt.generate
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingRecognitionWitnessEscapeRegression.proofCarryingRecognitionWitnessEscapeDirectConsumer
