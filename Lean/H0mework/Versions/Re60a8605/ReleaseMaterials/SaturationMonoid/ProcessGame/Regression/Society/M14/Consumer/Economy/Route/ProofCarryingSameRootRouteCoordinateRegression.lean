import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M9.JointRoot.ProofCarryingRenewalInquiryRoot
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Economy.Route.ProofCarryingSourceRouteOutageRestorationRegression

/-!
# M14 direct consumer for the same-root route-restoration coordinate

The root-independent outage/action mouth is now installed before the existing
M9 emitter as an eighth authority coordinate.  This consumer checks that the
installed payload is the exact source route outage and compiler-generated
`restoreRoute` action, shares the original root entry/row/successor with UBI,
and remains distinct from every preceding projection.

No route occurrence, service result, capacity result, trace, measure, U8
branch, second root, or completed future is constructed here.  Those belong
to downstream occurrence consumers of this installed authority.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingSameRootRouteCoordinateRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Renewal UBI Policy
open M9ProofCarryingRenewalInquiryRoot
open M10OccurrenceCapacityProcessFixture
open M14UBIProofCarryingRootRestriction
open M14SourceRouteOutageRestoration
open M14ProofCarryingSourceRouteOutageRestorationRegression

/-! ## Positive same-root installation -/

theorem installedRouteCoordinateExact :
    Nonempty (SourceInstalledRenewalAt
        routeOutageRestorationRecognition jointVisit) ∧
      installedRouteOutageRestoration.payload.sourceSeed = focalSeed ∧
      installedRouteOutageRestoration.payload.consumer =
        sourceRouteOutageRestriction ∧
      installedRouteOutageRestoration.payload.disposition =
        sourceGeneratedRouteRestoration ∧
      SourceAppliedRouteRestorationAt.failureKindAt
          installedRouteOutageRestoration.payload.disposition =
        .routeBottleneck ∧
      SourceAppliedRouteRestorationAt.repairAt
          installedRouteOutageRestoration.payload.disposition =
        .restoreRoute := by
  exact ⟨⟨installedRouteOutageRestoration⟩, rfl, rfl, rfl, rfl, rfl⟩

theorem routeAndUBIShareRootAuthority :
    installedRouteOutageRestoration.payload.sourceEntry =
        installedUBI.payload.sourceEntry ∧
      HEq installedRouteOutageRestoration.payload.selectedRow
        installedUBI.payload.selectedRow ∧
      HEq installedRouteOutageRestoration.payload.successor
        installedUBI.payload.successor ∧
      HEq installedRouteOutageRestoration.operationalAuthority
        installedUBI.operationalAuthority ∧
      installedRouteOutageRestoration.RootAnswerAndNextFactorizes ∧
      jointAuthoritySource.restructuringSource =
        (RootInquiryU8CompletionRegression.root.toAuthoritativeRoot.source
          ).restructuringSource := by
  exact ⟨routeOutage_shares_ubi_sourceEntry,
    routeOutage_shares_ubi_selectedRow,
    routeOutage_shares_ubi_successor,
    HEq.rfl,
    routeOutageRestoration_root_factorization,
    joint_restructuringSource_is_original⟩

/-! ## Independent authority and strict controls -/

theorem routeCoordinateIsIndependentAuthority :
    jointRouteOutageRestorationProjection ≠
        jointEssentialServiceRestorationProjection ∧
      jointRouteOutageRestorationProjection ≠ jointMandateProjection ∧
      jointRouteOutageRestorationProjection ≠
        jointRecognitionWitnessProjection ∧
      jointRouteOutageRestorationProjection ≠ jointUBIProjection ∧
      jointRouteOutageRestorationProjection ≠
        jointProofCarryingProjection ∧
      jointRouteOutageRestorationProjection ≠ jointInquiryProjection ∧
      jointRouteOutageRestorationProjection ≠ jointFailureProjection ∧
      SourceAppliedRouteRestorationAt.repairAt
          installedRouteOutageRestoration.payload.disposition ≠
        SourceAppliedTenureCaptureRepairAt.repairAt
          SourceAppliedTenureCaptureRepairAt.generate := by
  exact ⟨routeOutage_projection_ne_essentialService_projection,
    routeOutage_projection_ne_mandate_projection,
    routeOutage_projection_ne_recognitionWitness_projection,
    routeOutage_projection_ne_ubi_projection,
    routeOutage_projection_ne_proofCarrying_projection,
    routeOutage_projection_ne_inquiry_projection,
    routeOutage_projection_ne_failure_projection,
    by decide⟩

theorem routeCoordinateStrictControls :
    IsEmpty
        (SourceAppliedRouteRestorationAt focalSeed RouteOutageRoutesAt
          SourceGeneratedUBIRouteReceiptAt .routeBottleneck .removeCapture) ∧
      IsEmpty
        (SourceAppliedRouteRestorationAt focalSeed RouteOutageRoutesAt
          SourceGeneratedUBIRouteReceiptAt .tenureCapture .restoreRoute) ∧
      IsEmpty
        (SourceRouteOutageRestrictionAt focalSeed
          SourceGeneratedUBIRouteReceiptAt) ∧
      IsEmpty
        (SourceAppliedRouteRestorationAt focalSeed
          SourceGeneratedUBIRouteReceiptAt
          SourceGeneratedUBIRouteReceiptAt
          .routeBottleneck .restoreRoute) ∧
      IsEmpty
        (SourceAppliedRouteRestorationAt focalSeed RouteOutageRoutesAt
          RouteOutageRoutesAt .routeBottleneck .restoreRoute) :=
  sourceRouteOutageRestorationStrictControls

structure ProofCarryingSameRootRouteCoordinateCertificate : Prop where
  exactInstalled :
    Nonempty (SourceInstalledRenewalAt
        routeOutageRestorationRecognition jointVisit) ∧
      installedRouteOutageRestoration.payload.sourceSeed = focalSeed ∧
      installedRouteOutageRestoration.payload.consumer =
        sourceRouteOutageRestriction ∧
      installedRouteOutageRestoration.payload.disposition =
        sourceGeneratedRouteRestoration ∧
      SourceAppliedRouteRestorationAt.failureKindAt
          installedRouteOutageRestoration.payload.disposition =
        .routeBottleneck ∧
      SourceAppliedRouteRestorationAt.repairAt
          installedRouteOutageRestoration.payload.disposition =
        .restoreRoute
  sameRootAuthority :
    installedRouteOutageRestoration.payload.sourceEntry =
        installedUBI.payload.sourceEntry ∧
      HEq installedRouteOutageRestoration.payload.selectedRow
        installedUBI.payload.selectedRow ∧
      HEq installedRouteOutageRestoration.payload.successor
        installedUBI.payload.successor ∧
      HEq installedRouteOutageRestoration.operationalAuthority
        installedUBI.operationalAuthority ∧
      installedRouteOutageRestoration.RootAnswerAndNextFactorizes ∧
      jointAuthoritySource.restructuringSource =
        (RootInquiryU8CompletionRegression.root.toAuthoritativeRoot.source
          ).restructuringSource
  independentAuthority :
    jointRouteOutageRestorationProjection ≠
        jointEssentialServiceRestorationProjection ∧
      jointRouteOutageRestorationProjection ≠ jointMandateProjection ∧
      jointRouteOutageRestorationProjection ≠
        jointRecognitionWitnessProjection ∧
      jointRouteOutageRestorationProjection ≠ jointUBIProjection ∧
      jointRouteOutageRestorationProjection ≠
        jointProofCarryingProjection ∧
      jointRouteOutageRestorationProjection ≠ jointInquiryProjection ∧
      jointRouteOutageRestorationProjection ≠ jointFailureProjection ∧
      SourceAppliedRouteRestorationAt.repairAt
          installedRouteOutageRestoration.payload.disposition ≠
        SourceAppliedTenureCaptureRepairAt.repairAt
          SourceAppliedTenureCaptureRepairAt.generate
  strictControls :
    IsEmpty
        (SourceAppliedRouteRestorationAt focalSeed RouteOutageRoutesAt
          SourceGeneratedUBIRouteReceiptAt .routeBottleneck .removeCapture) ∧
      IsEmpty
        (SourceAppliedRouteRestorationAt focalSeed RouteOutageRoutesAt
          SourceGeneratedUBIRouteReceiptAt .tenureCapture .restoreRoute) ∧
      IsEmpty
        (SourceRouteOutageRestrictionAt focalSeed
          SourceGeneratedUBIRouteReceiptAt) ∧
      IsEmpty
        (SourceAppliedRouteRestorationAt focalSeed
          SourceGeneratedUBIRouteReceiptAt
          SourceGeneratedUBIRouteReceiptAt
          .routeBottleneck .restoreRoute) ∧
      IsEmpty
        (SourceAppliedRouteRestorationAt focalSeed RouteOutageRoutesAt
          RouteOutageRoutesAt .routeBottleneck .restoreRoute)

theorem proofCarryingSameRootRouteCoordinateDirectConsumer :
    ProofCarryingSameRootRouteCoordinateCertificate where
  exactInstalled := installedRouteCoordinateExact
  sameRootAuthority := routeAndUBIShareRootAuthority
  independentAuthority := routeCoordinateIsIndependentAuthority
  strictControls := routeCoordinateStrictControls

end
end M14ProofCarryingSameRootRouteCoordinateRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingSameRootRouteCoordinateRegression.installedRouteCoordinateExact
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingSameRootRouteCoordinateRegression.routeAndUBIShareRootAuthority
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingSameRootRouteCoordinateRegression.routeCoordinateIsIndependentAuthority
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingSameRootRouteCoordinateRegression.routeCoordinateStrictControls
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingSameRootRouteCoordinateRegression.proofCarryingSameRootRouteCoordinateDirectConsumer
