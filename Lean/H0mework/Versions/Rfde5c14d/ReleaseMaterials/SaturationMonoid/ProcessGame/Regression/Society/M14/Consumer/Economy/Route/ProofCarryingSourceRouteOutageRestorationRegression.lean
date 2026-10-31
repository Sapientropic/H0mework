import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Route.SourceRouteOutageRestoration

/-!
# M14 direct consumer for the root-independent route-restoration source

The source-side route outage and its compiler-generated `restoreRoute`
action are now complete before any living root installs them.  This consumer
checks the exact source/target route-family separation, repair authority, and
wrong-index exclusions without claiming that a concrete root coordinate or
temporal occurrence already exists.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingSourceRouteOutageRestorationRegression

noncomputable section

open UBI Policy
open M10OccurrenceCapacityProcessFixture
open M11GeneratedSocialSpaceCrossingFixture
open M14UBIExitCapacityFixture
open M14UBIProofCarryingRootRestriction
open M14SourceRouteOutageRestoration

theorem sourceRouteOutageRestorationAt :
    Nonempty (ExactSourceRouteOutageRestrictionAt focalSeed) ∧
      Nonempty (ExactSourceAppliedRouteRestorationAt focalSeed) ∧
      SourceAppliedRouteRestorationAt.failureKindAt
          sourceGeneratedRouteRestoration = .routeBottleneck ∧
      SourceAppliedRouteRestorationAt.repairAt
          sourceGeneratedRouteRestoration = .restoreRoute ∧
      (∀ crossing : ConcreteCrossing,
        IsEmpty (RouteOutageRoutesAt ExitFutureCode.leave crossing)) ∧
      (∀ crossing : ConcreteCrossing,
        Nonempty (SourceGeneratedUBIRouteReceiptAt
          ExitFutureCode.leave crossing)) ∧
      SourceAppliedRouteRestorationAt.repairAt
          sourceGeneratedRouteRestoration ≠
        SourceAppliedTenureCaptureRepairAt.repairAt
          SourceAppliedTenureCaptureRepairAt.generate := by
  exact
    ⟨⟨sourceRouteOutageRestriction⟩,
      ⟨sourceGeneratedRouteRestoration⟩,
      rfl,
      rfl,
      fun _crossing => inferInstance,
      fun crossing =>
        ⟨SourceGeneratedUBIRouteReceiptAt.generate crossing⟩,
      by decide⟩

theorem sourceRouteOutageRestorationStrictControls :
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
  ⟨removeCaptureRouteRestoration_isEmpty,
    tenureKindRouteRestoration_isEmpty,
    generatedFullRouteSource_isNotOutage,
    generatedFullRouteSource_cannotGenerateRouteRestoration,
    outageTarget_cannotGenerateRouteRestoration⟩

theorem noRouteCauseStillForbidsAction
    (noCause : IsEmpty
      (ExactSourceRouteOutageRestrictionAt focalSeed)) :
    IsEmpty (ExactSourceAppliedRouteRestorationAt focalSeed) :=
  noRouteOutageCause_noRestoration noCause

structure ProofCarryingSourceRouteOutageRestorationCertificate : Prop where
  generated :
    Nonempty (ExactSourceRouteOutageRestrictionAt focalSeed) ∧
      Nonempty (ExactSourceAppliedRouteRestorationAt focalSeed) ∧
      SourceAppliedRouteRestorationAt.failureKindAt
          sourceGeneratedRouteRestoration = .routeBottleneck ∧
      SourceAppliedRouteRestorationAt.repairAt
          sourceGeneratedRouteRestoration = .restoreRoute ∧
      (∀ crossing : ConcreteCrossing,
        IsEmpty (RouteOutageRoutesAt ExitFutureCode.leave crossing)) ∧
      (∀ crossing : ConcreteCrossing,
        Nonempty (SourceGeneratedUBIRouteReceiptAt
          ExitFutureCode.leave crossing)) ∧
      SourceAppliedRouteRestorationAt.repairAt
          sourceGeneratedRouteRestoration ≠
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
  noCauseNoAction :
    IsEmpty (ExactSourceRouteOutageRestrictionAt focalSeed) →
      IsEmpty (ExactSourceAppliedRouteRestorationAt focalSeed)

theorem proofCarryingSourceRouteOutageRestorationDirectConsumer :
    ProofCarryingSourceRouteOutageRestorationCertificate where
  generated := sourceRouteOutageRestorationAt
  strictControls := sourceRouteOutageRestorationStrictControls
  noCauseNoAction := noRouteCauseStillForbidsAction

end
end M14ProofCarryingSourceRouteOutageRestorationRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingSourceRouteOutageRestorationRegression.sourceRouteOutageRestorationAt
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingSourceRouteOutageRestorationRegression.sourceRouteOutageRestorationStrictControls
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingSourceRouteOutageRestorationRegression.proofCarryingSourceRouteOutageRestorationDirectConsumer
