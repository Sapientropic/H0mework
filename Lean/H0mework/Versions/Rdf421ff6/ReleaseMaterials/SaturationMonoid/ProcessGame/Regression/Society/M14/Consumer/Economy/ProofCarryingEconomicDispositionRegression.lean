import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Economy.GeneratedEconomicDisposition

/-!
# M14 proof-carrying economic disposition consumer

This consumer proves factorization of every currently generated fixed update
mouth: actual ordinary repair at each finite depth, the first repaired viable
successor, and the existing depth-zero self-U8 landing.  The root-native
terminal classifier is empty at every fixed visit.  Every disposition carries
proof that its image came from the indexed occurrence, so arbitrary lists and
caller-pruned images have no disposition authority.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingEconomicDispositionRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open RootedAccountedUnfolding
open Renewal Revision UBI Policy Legislation Election
open ConstructiveRoot.RootInquiryCompletion
open M9ProofCarryingRenewalInquiryRoot
open M9ProofCarryingRenewalInquiryRuntime
open M9ProofCarryingRenewalU8Revision
open M9ProofCarryingLegislationRegression
open M8ActualElectionMandateRenewalRegression
open M14UBIPeriodicRootHistory
open M14UBIPeriodicActualServiceCapacity
open M14SourceMandateRenewal
open M14PeriodicMandatePowerRenewal
open M14ProofCarryingExitRepairRegression
open M14ProofCarryingExitRepairRenewalRegression
open M14UBIPolicyBreakingOccurrence
open M14UBIPolicySelfU8Regression
open M14UBIProofCarryingLegislationRegression
open M14ProofCarryingRecognitionWitnessEscapeRegression
open M14EconomicSingleFold
open M14GeneratedEconomicDisposition

theorem every_actual_ordinary_update_factors (depth : Nat) :
    Nonempty (EconomicDispositionAt
      (tenureRepairExposureAt depth) (tenureEconomicImageAt depth)
      (ordinaryEconomicLandingAt depth)) :=
  ⟨ordinaryDispositionAt depth⟩

theorem fixed_repaired_successor_is_viable :
    Nonempty (SourceGeneratedPostRepairViableEconomicDispositionAt
      postRepairViableExposure postRepairViableImage
      (ordinaryEconomicLandingAt 0)) :=
  ⟨fixedPostRepairViableEconomicDisposition⟩

theorem fixed_breaking_occurrence_requires_u8 :
    Nonempty (EconomicDispositionAt
      (tenureRepairExposureAt 0) (tenureEconomicImageAt 0)
      revolutionaryEconomicLanding) :=
  ⟨requiresU8Disposition⟩

/-- Every branch proves that its image is the fold of its exact occurrence.
This is the substantive guard against a totality theorem on arbitrary lists. -/
theorem disposition_image_is_source_generated
    {occurrence : RootedAccountedUnfolding ExactEconomicAtom}
    {image : EconomicFoldImage} {landing : EconomicLanding}
    (disposition : EconomicDispositionAt occurrence image landing) :
    image = economicImage occurrence := by
  rcases disposition with viable | rest
  · exact viable.image_eq
  · rcases rest with ordinary | rest
    · exact ordinary.image_eq
    · rcases rest with requiresU8 | terminal
      · exact requiresU8.image_eq
      · exact terminal.image_eq

theorem non_source_image_has_no_disposition
    {occurrence : RootedAccountedUnfolding ExactEconomicAtom}
    {image : EconomicFoldImage} {landing : EconomicLanding}
    (notSource : image ≠ economicImage occurrence) :
    IsEmpty (EconomicDispositionAt occurrence image landing) :=
  ⟨fun disposition =>
    notSource (disposition_image_is_source_generated disposition)⟩

/-- The ordinary and U8 branches share the exact old image but consume
different projections and land in strictly different heterogeneous currents. -/
theorem ordinary_u8_same_old_authority_different_landing :
    let ordinary := actualOrdinaryRenewalAt 0
    (tenureRepairExposureAt 0).root.erasedRootEvent =
        ⟨temporalVisitAt 0,
          (periodicSourceBackedPaymentAt 0).rootOccurrence⟩ ∧
      ordinary.rootOccurrence =
        jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
          (temporalVisitAt 0) ∧
      (⟨jointVisit.current, audit.rootOccurrence⟩ :
        Sigma M14UBIPolicyBreakingOccurrence.Root.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt) =
        ⟨(temporalVisitAt 0).current,
          (periodicSourceBackedPaymentAt 0).rootOccurrence.occurrence⟩ ∧
      ordinary.wholeLedgerWriteBack =
        (jointRoot.toAuthoritativeRoot.toLedgerRoot
          |>.generatedAtTemporalVisit
            (temporalVisitAt 0)).wholeLedgerWriteBack ∧
      (jointRoot.toAuthoritativeRoot.toLedgerRoot
        |>.generatedAtTemporalVisit jointVisit).wholeLedgerWriteBack =
        proofCarryingLegislation.wholeLedgerWriteBack ∧
      jointUBIProjection ≠ jointInquiryProjection ∧
      ordinaryEconomicLandingAt 0 ≠ revolutionaryEconomicLanding ∧
      ordinary.generatedNext.root.source.lawSurface =
        jointRoot.source.base.lawSurface ∧
      jointCore.cofaceFactorization.2.firstWrite =
        M13SelfU8Regression.selfU8.firstWrite := by
  exact ⟨tenureRepairExposure_rootEvent 0,
    (actualOrdinaryRenewalAt 0).rootOccurrence_eq,
    audit_rootOccurrence_is_payment_rootOccurrence,
    rfl, rfl, ubi_projection_ne_inquiry_projection,
    ordinary_and_u8_share_image_but_not_landing.2.2,
    (actualOrdinaryRenewalAt 0).lawSurface_preserved,
    policyCore_firstWrite_is_selfU8_firstWrite⟩

/-- A local election archive remains visible while whole-root terminal
authority is empty.  The two notions cannot be retyped into one another. -/
theorem local_mandate_archive_is_not_whole_economic_terminal (depth : Nat) :
    (∃ archive,
      sourceMandateExitFace.exactDisposition.1.target.slots[
          (mandateSlot lineageCompiler
            sourceMandateExitHistory.current).val]? =
        some (ObligationSlot.terminal archive)) ∧
      IsEmpty (SourceGeneratedGroundedEconomicTerminalAt
        (tenureRepairExposureAt depth) (tenureEconomicImageAt depth) none) :=
  ⟨SourceGeneratedProofCarryingPeriodicMandatePowerRenewalAt.actual_exit_retains_prior_trace_and_ends_power.2.2.2,
    inferInstance⟩

/-- Existing fixed actual authority excludes the route-only repair and every
whole-root terminal, while preserving both source-generated nonterminal
landings. -/
structure ProofCarryingEconomicDispositionCertificate : Prop where
  everyDepthOrdinary : ∀ depth : Nat,
    Nonempty (EconomicDispositionAt
      (tenureRepairExposureAt depth) (tenureEconomicImageAt depth)
      (ordinaryEconomicLandingAt depth))
  fixedViable : Nonempty (SourceGeneratedPostRepairViableEconomicDispositionAt
    postRepairViableExposure postRepairViableImage
    (ordinaryEconomicLandingAt 0))
  fixedRequiresU8 : Nonempty (EconomicDispositionAt
    (tenureRepairExposureAt 0) (tenureEconomicImageAt 0)
    revolutionaryEconomicLanding)
  sameImageDifferentLanding :
    Nonempty (SourceGeneratedOrdinaryEconomicDispositionAt
      (tenureRepairExposureAt 0) (tenureEconomicImageAt 0)
      (ordinaryEconomicLandingAt 0)) ∧
      Nonempty (SourceGeneratedRequiresU8EconomicDispositionAt
        (tenureRepairExposureAt 0) (tenureEconomicImageAt 0)
        revolutionaryEconomicLanding) ∧
      ordinaryEconomicLandingAt 0 ≠ revolutionaryEconomicLanding
  sameOldAuthorityDifferentBranch :
    let ordinary := actualOrdinaryRenewalAt 0
    (tenureRepairExposureAt 0).root.erasedRootEvent =
        ⟨temporalVisitAt 0,
          (periodicSourceBackedPaymentAt 0).rootOccurrence⟩ ∧
      ordinary.rootOccurrence =
        jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
          (temporalVisitAt 0) ∧
      ordinary.wholeLedgerWriteBack =
        (jointRoot.toAuthoritativeRoot.toLedgerRoot
          |>.generatedAtTemporalVisit
            (temporalVisitAt 0)).wholeLedgerWriteBack ∧
      jointUBIProjection ≠ jointInquiryProjection ∧
      ordinary.generatedNext.root.source.lawSurface =
        jointRoot.source.base.lawSurface ∧
      jointCore.cofaceFactorization.2.firstWrite =
        M13SelfU8Regression.selfU8.firstWrite
  fixedViableClosure :
    postRepairViableExposure.root.erasedRootEvent =
        ⟨temporalVisitAt 1,
          (periodicSourceBackedPaymentAt 1).rootOccurrence⟩ ∧
      Nonempty (PeriodicActualServiceExitAt 1) ∧
      Nonempty (SourceGeneratedProofCarryingPeriodicMandatePowerRenewalAt 1) ∧
      Nonempty (SourceGeneratedProofCarryingRecognitionWitnessEscapeAt
        installedRecognitionWitness) ∧
      SourceNativeInquiryRuntime.CofaceRealizationResumptionAt
        jointCore jointRuntime 0
  u8LandingGeneratedByRuntimeOption :
    revolutionaryEconomicLanding =
        (sourceGeneratedUBIProofCarryingLegislation.policyLegislation
          |>.revolutionaryConsumption |>.map
            (fun _ =>
              sourceGeneratedUBIProofCarryingLegislation.policyLegislation.generatedNext)) ∧
      revolutionaryEconomicLanding =
        some sourceGeneratedUBIProofCarryingLegislation.policyLegislation.generatedNext
  everyDepthGroundedTerminalEmpty : ∀ depth : Nat,
    IsEmpty (SourceGeneratedGroundedEconomicTerminalAt
      (tenureRepairExposureAt depth) (tenureEconomicImageAt depth) none)
  everyDepthTerminalClassifierNone : ∀ depth : Nat,
    generateGroundedEconomicTerminalAt? depth = none
  everyDepthActualSuccessor : ∀ depth : Nat,
    (jointRoot.toAuthoritativeRoot.toRoot.evolutionAt
      (rootVisitAt depth).current).nextCurrent? =
        some (rootVisitAt depth).current
  everyNoneLandingEmpty : ∀
    (occurrence : RootedAccountedUnfolding ExactEconomicAtom)
    (image : EconomicFoldImage),
    IsEmpty (EconomicDispositionAt occurrence image none)
  localArchiveNeverWholeTerminal : ∀ depth : Nat,
    (∃ archive,
      sourceMandateExitFace.exactDisposition.1.target.slots[
          (mandateSlot lineageCompiler
            sourceMandateExitHistory.current).val]? =
        some (ObligationSlot.terminal archive)) ∧
      IsEmpty (SourceGeneratedGroundedEconomicTerminalAt
        (tenureRepairExposureAt depth) (tenureEconomicImageAt depth) none)
  everyDepthWrongActualRepairEmpty : ∀ depth : Nat,
    IsEmpty (SourceInstalledProofCarryingExitRepairRenewalAt
      depth .restoreRoute)
  arbitraryImageRejected : ∀
    (occurrence : RootedAccountedUnfolding ExactEconomicAtom)
    (image : EconomicFoldImage) (landing : EconomicLanding),
    image ≠ economicImage occurrence →
      IsEmpty (EconomicDispositionAt occurrence image landing)

theorem proofCarryingEconomicDispositionDirectConsumer :
    ProofCarryingEconomicDispositionCertificate where
  everyDepthOrdinary := every_actual_ordinary_update_factors
  fixedViable := fixed_repaired_successor_is_viable
  fixedRequiresU8 := fixed_breaking_occurrence_requires_u8
  sameImageDifferentLanding :=
    ordinary_and_u8_share_image_but_not_landing
  sameOldAuthorityDifferentBranch :=
    ⟨tenureRepairExposure_rootEvent 0,
      (actualOrdinaryRenewalAt 0).rootOccurrence_eq,
      rfl, ubi_projection_ne_inquiry_projection,
      (actualOrdinaryRenewalAt 0).lawSurface_preserved,
      policyCore_firstWrite_is_selfU8_firstWrite⟩
  fixedViableClosure :=
    ⟨postRepairViableExposure_rootEvent,
      ⟨periodicActualServiceExitAt 1⟩,
      ⟨periodicMandatePowerRenewalAt 1⟩,
      ⟨sourceGeneratedProofCarryingRecognitionWitnessEscape⟩,
      runtime_consumes_jointCore_after_policy_factorization⟩
  u8LandingGeneratedByRuntimeOption :=
    ⟨rfl, revolutionaryEconomicLanding_eq_some⟩
  everyDepthGroundedTerminalEmpty := fun _depth => inferInstance
  everyDepthTerminalClassifierNone :=
    fixed_grounded_terminal_classifier_eq_none
  everyDepthActualSuccessor := fixedRoot_has_actual_successor
  everyNoneLandingEmpty := fixedRoot_noneLandingDisposition_isEmpty
  localArchiveNeverWholeTerminal :=
    local_mandate_archive_is_not_whole_economic_terminal
  everyDepthWrongActualRepairEmpty :=
    SourceInstalledProofCarryingExitRepairRenewalAt.restoreRoute_is_not_actual_in_tenure_coordinate
  arbitraryImageRejected := fun _occurrence _image _landing =>
    non_source_image_has_no_disposition

end
end M14ProofCarryingEconomicDispositionRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingEconomicDispositionRegression.disposition_image_is_source_generated
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingEconomicDispositionRegression.ordinary_u8_same_old_authority_different_landing
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingEconomicDispositionRegression.proofCarryingEconomicDispositionDirectConsumer
