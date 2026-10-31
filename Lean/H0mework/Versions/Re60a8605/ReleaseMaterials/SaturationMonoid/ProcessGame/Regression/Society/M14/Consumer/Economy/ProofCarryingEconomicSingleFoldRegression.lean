import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.EconomicSingleFold
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Legislation.UBIProofCarryingLegislationRegression

/-!
# M14 proof-carrying economic single-fold consumer

This consumer certifies that exact economic atoms, the one-constructor
unfolding, synchronized quantitative/qualitative evaluation, and the current
living root form one commuting object.  The fold is a calculation trace: it
preserves root authority and cannot choose between ordinary repair and U8.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingEconomicSingleFoldRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open RootedAccountedUnfolding
open Renewal Legislation Revision UBI Policy
open ConstructiveRoot.RootInquiryCompletion
open M9ProofCarryingRenewalInquiryRoot
open M14TenureCaptureRouteRepairNoGoRegression
open M14SourceAccountedEconomicAtom
open M14EconomicSingleFold
open M14UBIProofCarryingLegislationRegression
open M14UBIPeriodicRootHistory

theorem economic_atom_root_authority_commutes
    (atom : ExactEconomicAtom) :
    atom.rootOccurrence = atom.exactTemporalRootEvent.occurrence ∧
      atom.sourceEntry = RootInquiryU8CompletionRegression.entry ∧
      HEq atom.sourceSelectedRow atom.installedUBI.payload.selectedRow ∧
      HEq atom.installedMandate.payload.successor
        atom.installedUBI.payload.successor ∧
      atom.wholeLedgerWriteBack =
        (jointRoot.toAuthoritativeRoot.toLedgerRoot
          |>.generatedAtTemporalVisit atom.visit).wholeLedgerWriteBack ∧
      atom.installedMandate.RootAnswerAndNextFactorizes ∧
      atom.generatedNext = jointRoot.generatedNextCurrentAt atom.visit :=
  ⟨atom.rootOccurrence_eq_exactTemporal,
    atom.sourceEntry_eq_rootEntry,
    atom.sourceSelectedRow_heq_ubi,
    atom.successor_heq_ubi,
    atom.wholeLedgerWriteBack_eq,
    atom.rootAnswerAndNext_factorizes,
    atom.generatedNext_eq⟩

theorem every_failure_repair_pair_shares_root_authority (depth : Nat) :
    SourceAccountedEconomicAtomAt.CanonicalRepairSharesRootAuthorityAt
        (tenureCaptureOriginAt depth) ∧
      SourceAccountedEconomicAtomAt.CanonicalRepairSharesRootAuthorityAt
        (routeBottleneckOriginAt depth) :=
  ⟨SourceAccountedEconomicAtomAt.canonicalRepair_same_root_authority
      (tenureCaptureOriginAt depth),
    SourceAccountedEconomicAtomAt.canonicalRepair_same_root_authority
      (routeBottleneckOriginAt depth)⟩

theorem economic_fold_does_not_choose_revision_branch :
    sourceGeneratedUBIProofCarryingLegislation.policyLegislation.branchKind =
        SourceGeneratedInstitutionalRevisionKind.revolution ∧
      (⟨M9ProofCarryingRenewalInquiryRoot.N,
        sourceGeneratedUBIProofCarryingLegislation.ordinaryRepair.generatedNext⟩ :
          AnyAuthoritativeRootCurrent) ≠
        sourceGeneratedUBIProofCarryingLegislation.policyLegislation.generatedNext :=
  ⟨ubiProofCarryingLegislationDirectConsumer.automaticSelfU8.1,
    ubiProofCarryingLegislationDirectConsumer
      |>.distinctOrdinaryAndRevolutionaryNexts⟩

/-- Interface regression: neither the sealed source event nor the private
algebra is a downstream readout from an arbitrary atom. -/
theorem sealed_generator_has_no_public_atom_bypass
    (_atom : ExactEconomicAtom) : True := by
  fail_if_success
    have _event : EconomicEvent := _atom.eventEvidence
  fail_if_success
    have _image : EconomicFoldImage := economicAlgebra _atom []
  fail_if_success
    have _event : EconomicEvent :=
      ExactEconomicAtom.rec
        (motive := fun _ => EconomicEvent)
        (fun eventEvidence _sourceAnchor => eventEvidence)
        _atom
  fail_if_success
    have _event : EconomicEvent :=
      ExactEconomicAtom.casesOn
        (motive := fun _ => EconomicEvent)
        _atom
        (fun eventEvidence _sourceAnchor => eventEvidence)
  fail_if_success
    have _capacity : List Nat := quantitativeImage []
  fail_if_success
    have _qualitative :
        List (Bool × ExactExitFailureKind × ExactExitRepair) :=
      qualitativeImage []
  trivial

structure ProofCarryingEconomicSingleFoldCertificate : Prop where
  everyAtomRooted : ∀ atom : ExactEconomicAtom,
    atom.rootOccurrence = atom.exactTemporalRootEvent.occurrence ∧
      atom.sourceEntry = RootInquiryU8CompletionRegression.entry ∧
      HEq atom.sourceSelectedRow atom.installedUBI.payload.selectedRow ∧
      HEq atom.installedMandate.payload.successor
        atom.installedUBI.payload.successor ∧
      atom.wholeLedgerWriteBack =
        (jointRoot.toAuthoritativeRoot.toLedgerRoot
          |>.generatedAtTemporalVisit atom.visit).wholeLedgerWriteBack ∧
      atom.installedMandate.RootAnswerAndNextFactorizes ∧
      atom.generatedNext = jointRoot.generatedNextCurrentAt atom.visit
  everyFailureRepairPairSharesAuthority : ∀ depth : Nat,
    SourceAccountedEconomicAtomAt.CanonicalRepairSharesRootAuthorityAt
        (tenureCaptureOriginAt depth) ∧
      SourceAccountedEconomicAtomAt.CanonicalRepairSharesRootAuthorityAt
        (routeBottleneckOriginAt depth)
  constructorCompatibleEvaluatorUnique :
    ∀ (candidate : RootedAccountedUnfolding ExactEconomicAtom →
          EconomicFoldImage),
      EconomicConstructorCompatible candidate →
      ∀ occurrence : RootedAccountedUnfolding ExactEconomicAtom,
        candidate occurrence = economicImage occurrence
  canonicalEvaluatorCompatible :
    EconomicConstructorCompatible economicImage
  frontierPreserved : ∀ occurrence :
      RootedAccountedUnfolding ExactEconomicAtom,
    (economicRepairExposure occurrence).frontier =
      occurrence.frontier.flatMap
        (fun atom => (canonicalRepairPatch atom).frontier)
  consecutiveExposureCanonical : ∀ occurrence :
      RootedAccountedUnfolding ExactEconomicAtom,
    economicTwoStepExposure occurrence =
      occurrence.advance (fun atom =>
        (canonicalRepairPatch atom).advance nextVisitRepairPatch)
  everyDepthRepairFrontier : ∀ depth : Nat,
    (economicRepairExposure
        (tenureEconomicFailureOccurrenceAt depth)).frontier =
        [tenureExactEconomicRepairAtomAt depth] ∧
      (economicRepairExposure
        (routeEconomicFailureOccurrenceAt depth)).frontier =
        [routeExactEconomicRepairAtomAt depth]
  everyDepthNextVisitFrontier : ∀ depth : Nat,
    (economicTwoStepExposure
        (tenureEconomicFailureOccurrenceAt depth)).frontier =
        [tenureExactEconomicRepairAtomAt (depth + 1)] ∧
      (economicTwoStepExposure
        (routeEconomicFailureOccurrenceAt depth)).frontier =
        [routeExactEconomicRepairAtomAt (depth + 1)]
  everyDepthTenureRootEvent : ∀ depth : Nat,
    (economicRepairExposure
      (tenureEconomicFailureOccurrenceAt depth)).root.erasedRootEvent =
      ⟨temporalVisitAt depth,
        (periodicSourceBackedPaymentAt depth).rootOccurrence⟩
  crossSourceOccurrencesDistinct : tenureRepairExposure ≠ routeRepairExposure
  crossRootOccurrencesDistinct :
    (tenureFailureAtomAt 0).erasedRootOccurrence ≠
      (routeFailureAtomAt 1).erasedRootOccurrence
  sameQuantitativeImage :
    economicQuantitativeImage tenureRepairExposure = [0, 1] ∧
      economicQuantitativeImage routeRepairExposure = [0, 1] ∧
      economicQuantitativeImage tenureRepairExposure =
        economicQuantitativeImage routeRepairExposure
  differentQualitativeImage :
    economicQualitativeImage tenureRepairExposure ≠
      economicQualitativeImage routeRepairExposure
  noQuantitativeReconstruction :
    ¬ ∃ reconstruct : List Nat →
        List (Bool × ExactExitFailureKind × ExactExitRepair),
      reconstruct (economicQuantitativeImage tenureRepairExposure) =
          economicQualitativeImage tenureRepairExposure ∧
        reconstruct (economicQuantitativeImage routeRepairExposure) =
          economicQualitativeImage routeRepairExposure
  ordinaryAndSelfU8RemainDistinct :
    sourceGeneratedUBIProofCarryingLegislation.policyLegislation.branchKind =
        SourceGeneratedInstitutionalRevisionKind.revolution ∧
      (⟨M9ProofCarryingRenewalInquiryRoot.N,
        sourceGeneratedUBIProofCarryingLegislation.ordinaryRepair.generatedNext⟩ :
          AnyAuthoritativeRootCurrent) ≠
        sourceGeneratedUBIProofCarryingLegislation.policyLegislation.generatedNext

theorem proofCarryingEconomicSingleFoldDirectConsumer :
    ProofCarryingEconomicSingleFoldCertificate where
  everyAtomRooted := economic_atom_root_authority_commutes
  everyFailureRepairPairSharesAuthority :=
    every_failure_repair_pair_shares_root_authority
  constructorCompatibleEvaluatorUnique :=
    constructorCompatibleEvaluator_eq_economicImage
  canonicalEvaluatorCompatible := economicImage_constructorCompatible
  frontierPreserved := economic_frontier_advance
  consecutiveExposureCanonical := economic_advance_assoc
  everyDepthRepairFrontier := fun depth =>
    ⟨tenure_repair_frontier depth, route_repair_frontier depth⟩
  everyDepthNextVisitFrontier := fun depth =>
    ⟨tenure_two_step_frontier depth, route_two_step_frontier depth⟩
  everyDepthTenureRootEvent := tenureRepairExposure_rootEvent
  crossSourceOccurrencesDistinct := tenure_route_source_occurrences_distinct
  crossRootOccurrencesDistinct :=
    tenure_route_exact_root_occurrences_distinct
  sameQuantitativeImage :=
    ⟨tenure_quantitative_image, route_quantitative_image,
      tenure_route_quantitative_images_equal⟩
  differentQualitativeImage := tenure_route_qualitative_images_distinct
  noQuantitativeReconstruction :=
    no_quantitative_image_reconstructs_qualitative_image
  ordinaryAndSelfU8RemainDistinct :=
    economic_fold_does_not_choose_revision_branch

end
end M14ProofCarryingEconomicSingleFoldRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingEconomicSingleFoldRegression.proofCarryingEconomicSingleFoldDirectConsumer
