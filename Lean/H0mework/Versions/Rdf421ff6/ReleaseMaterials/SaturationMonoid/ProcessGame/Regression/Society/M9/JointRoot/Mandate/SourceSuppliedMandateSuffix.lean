import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M9.JointRoot.ProofCarryingRenewalInquiryRoot

/-!
# One supplied mandate coordinate with the existing M9 economic suffix

The M9 prefix through recognition publication is fixed.  This assembler
installs exactly one history-indexed mandate coordinate and then reuses the
existing service, route, common-clearing and backstop laws.  Standing and
actual exit are therefore two generated root representations of one slot,
not two mandate coordinates in one inventory.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M9SourceSuppliedMandateSuffix

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Renewal Election
open M8ActualElectionMandateRenewalRegression
open M9ProofCarryingRenewalInquiryRoot
open M14SourceMandateRenewal
open M14SourceEssentialServiceRestoration
open M14SourceRouteOutageRestoration
open M14SourceCommonClearingRenewal
open M14SourceClearingBackstopRenewal

abbrev N := M9ProofCarryingRenewalInquiryRoot.N
abbrev V := M9ProofCarryingRenewalInquiryRoot.V

def mandateAuthoritySourceFor (history : ActualHistory) :
    SourceNativeAuthoritySource N V :=
  withSourceMandateRenewalFor history recognitionAuthoritySource
    mandateRootShell

def essentialServiceRestorationLawFor (history : ActualHistory) :
    SourceEssentialServiceRestorationLawAt
      (mandateAuthoritySourceFor history).restructuringSource.toLedgerSource :=
  sourceEssentialServiceRestorationLaw mandateRootShell

def essentialServiceRestorationAuthoritySourceFor
    (history : ActualHistory) : SourceNativeAuthoritySource N V :=
  withRenewalProjection (mandateAuthoritySourceFor history)
    (essentialServiceRestorationLawFor history)

def routeOutageRestorationLawFor (history : ActualHistory) :
    SourceRouteOutageRestorationLawAt
      (essentialServiceRestorationAuthoritySourceFor history
        ).restructuringSource.toLedgerSource :=
  sourceRouteOutageRestorationLaw mandateRootShell

def routeOutageRestorationAuthoritySourceFor
    (history : ActualHistory) : SourceNativeAuthoritySource N V :=
  withRenewalProjection (essentialServiceRestorationAuthoritySourceFor history)
    (routeOutageRestorationLawFor history)

def commonClearingLawFor (history : ActualHistory) :
    SourceCommonClearingRenewalLawAt
      (routeOutageRestorationAuthoritySourceFor history
        ).restructuringSource.toLedgerSource :=
  sourceCommonClearingRenewalLaw mandateRootShell

def commonClearingAuthoritySourceFor
    (history : ActualHistory) : SourceNativeAuthoritySource N V :=
  withRenewalProjection (routeOutageRestorationAuthoritySourceFor history)
    (commonClearingLawFor history)

def clearingBackstopLawFor (history : ActualHistory) :
    SourceClearingBackstopRenewalLawAt
      (commonClearingAuthoritySourceFor history
        ).restructuringSource.toLedgerSource :=
  sourceClearingBackstopRenewalLaw mandateRootShell

/-- Complete M9 authority inventory with exactly one supplied mandate slot. -/
def jointAuthoritySourceFor (history : ActualHistory) :
    SourceNativeAuthoritySource N V :=
  withRenewalProjection (commonClearingAuthoritySourceFor history)
    (clearingBackstopLawFor history)

/-- Living root emitted only after the one-slot inventory is complete. -/
def jointRootFor (history : ActualHistory) :
    SourceNativeLivingRootClosure N V where
  source :=
    { base := jointAuthoritySourceFor history
      terminalHandoff :=
        (jointAuthoritySourceFor history).emptyFaithfulTerminalHandoff
          (fun _ => ⟨fun terminal => nomatch terminal⟩) }
  emitted := RootInquiryU8CompletionRegression.root.emitted
  compiler_commutes := fun _ => rfl

def jointVisitFor (history : ActualHistory) :
    SourceNativeTemporalVisitAt
      (jointRootFor history).toAuthoritativeRoot.toLedgerRoot :=
  .finite (jointRootFor history).toAuthoritativeRoot.toRoot.initialVisit

/-! ## Fixed coordinate inventory -/

def inquiryProjectionFor (history : ActualHistory) :
    (jointRootFor history).toAuthoritativeRoot.source.projectionLaw.Projection :=
  .inherited
    (.inherited
      (.inherited
        (.inherited (.inherited (.inherited (.inherited (.inherited .inquiry)))))))

def proofCarryingProjectionFor (history : ActualHistory) :
    (jointRootFor history).toAuthoritativeRoot.source.projectionLaw.Projection :=
  .inherited
    (.inherited
      (.inherited (.inherited (.inherited (.inherited (.inherited .renewal))))))

def ubiProjectionFor (history : ActualHistory) :
    (jointRootFor history).toAuthoritativeRoot.source.projectionLaw.Projection :=
  .inherited
    (.inherited (.inherited (.inherited (.inherited (.inherited .renewal)))))

def recognitionWitnessProjectionFor (history : ActualHistory) :
    (jointRootFor history).toAuthoritativeRoot.source.projectionLaw.Projection :=
  .inherited (.inherited (.inherited (.inherited (.inherited .renewal))))

/-- The sole mandate coordinate in the supplied-history inventory. -/
def mandateProjectionFor (history : ActualHistory) :
    (jointRootFor history).toAuthoritativeRoot.source.projectionLaw.Projection :=
  .inherited (.inherited (.inherited (.inherited .renewal)))

def essentialServiceProjectionFor (history : ActualHistory) :
    (jointRootFor history).toAuthoritativeRoot.source.projectionLaw.Projection :=
  .inherited (.inherited (.inherited .renewal))

def routeProjectionFor (history : ActualHistory) :
    (jointRootFor history).toAuthoritativeRoot.source.projectionLaw.Projection :=
  .inherited (.inherited .renewal)

def commonClearingProjectionFor (history : ActualHistory) :
    (jointRootFor history).toAuthoritativeRoot.source.projectionLaw.Projection :=
  .inherited .renewal

def clearingBackstopProjectionFor (history : ActualHistory) :
    (jointRootFor history).toAuthoritativeRoot.source.projectionLaw.Projection :=
  .renewal

theorem mandateProjection_distinct_from_other_named_coordinates
    (history : ActualHistory) :
    mandateProjectionFor history ≠ recognitionWitnessProjectionFor history ∧
      mandateProjectionFor history ≠ ubiProjectionFor history ∧
      mandateProjectionFor history ≠ proofCarryingProjectionFor history ∧
      mandateProjectionFor history ≠ inquiryProjectionFor history ∧
      mandateProjectionFor history ≠ essentialServiceProjectionFor history ∧
      mandateProjectionFor history ≠ routeProjectionFor history ∧
      mandateProjectionFor history ≠ commonClearingProjectionFor history ∧
      mandateProjectionFor history ≠ clearingBackstopProjectionFor history := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals intro equality
  all_goals cases equality

/-! ## Installation through the unchanged suffix -/

def preBackstopInventoryFor (history : ActualHistory) :
    SourceNativeProjectionLaw.InstallationAt
      (routeOutageRestorationAuthoritySourceFor history).projectionLaw
      (jointRootFor history).toAuthoritativeRoot.source.projectionLaw :=
  (inheritedByRenewal (routeOutageRestorationAuthoritySourceFor history)
      (commonClearingLawFor history)).trans
    (inheritedByRenewal (commonClearingAuthoritySourceFor history)
      (clearingBackstopLawFor history))

def mandateInstallationFor (history : ActualHistory) :
    SourceNativeProjectionLaw.InstallationAt
      (sourceMandateRenewalLawFor history mandateRootShell).toProjectionLaw
      (jointRootFor history).toAuthoritativeRoot.source.projectionLaw :=
  (((sourceMandateRenewalComponentFor history recognitionAuthoritySource
        mandateRootShell).trans
      (inheritedByRenewal (mandateAuthoritySourceFor history)
        (essentialServiceRestorationLawFor history))).trans
    (inheritedByRenewal (essentialServiceRestorationAuthoritySourceFor history)
      (routeOutageRestorationLawFor history))).trans
    (preBackstopInventoryFor history)

def ubiInstallationFor (history : ActualHistory) :
    SourceNativeProjectionLaw.InstallationAt ubiLaw.toProjectionLaw
      (jointRootFor history).toAuthoritativeRoot.source.projectionLaw :=
  ((((renewalComponent proofCarryingAuthoritySource ubiLaw).trans
      (inheritedByRenewal ubiAuthoritySource recognitionWitnessLaw)).trans
    (inheritedByRenewal recognitionAuthoritySource
      (sourceMandateRenewalLawFor history mandateRootShell))).trans
    (inheritedByRenewal (mandateAuthoritySourceFor history)
      (essentialServiceRestorationLawFor history))).trans
    ((inheritedByRenewal
        (essentialServiceRestorationAuthoritySourceFor history)
          (routeOutageRestorationLawFor history)).trans
      (preBackstopInventoryFor history))

def mandateRecognitionFor (history : ActualHistory) :
    SourceNativeRenewalRecognitionAt (jointRootFor history)
      (SourceMandateGameFor history) (SourceMandateSeedFor history)
      (SourceMandateSeedAtFor history) (SourceMandateConsumerAtFor history)
      (SourceMandateDispositionAtFor history) where
  law := sourceMandateRenewalLawFor history mandateRootShell
  installation := mandateInstallationFor history

def ubiRecognitionFor (history : ActualHistory) :
    SourceNativeRenewalRecognitionAt (jointRootFor history)
      M14UBIProofCarryingRootRestriction.LocalGame
      M14UBIProofCarryingRootRestriction.LocalSeed
      M14UBIProofCarryingRootRestriction.LocalSeedAt
      M14UBIProofCarryingRootRestriction.UBIConsumerAt
      M14UBIProofCarryingRootRestriction.UBIDispositionAt where
  law := ubiLaw
  installation := ubiInstallationFor history

/-! ## Standing specialization and representation invariants -/

@[simp] theorem standing_jointAuthoritySource_exact :
    jointAuthoritySourceFor sourceMandateHistory = jointAuthoritySource :=
  rfl

@[simp] theorem standing_jointRoot_exact :
    jointRootFor sourceMandateHistory = jointRoot :=
  rfl

@[simp] theorem restructuringSource_preserved (history : ActualHistory) :
    (jointRootFor history).toAuthoritativeRoot.source.restructuringSource =
      jointRoot.toAuthoritativeRoot.source.restructuringSource :=
  rfl

@[simp] theorem ledgerCompiler_preserved (history : ActualHistory) :
    (jointRootFor history).toAuthoritativeRoot.toLedgerRoot.source.ledgerCompiler =
      jointRoot.toAuthoritativeRoot.toLedgerRoot.source.ledgerCompiler :=
  rfl

@[simp] theorem emitted_preserved (history : ActualHistory) :
    (jointRootFor history).emitted = jointRoot.emitted :=
  rfl

end
end M9SourceSuppliedMandateSuffix
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M9SourceSuppliedMandateSuffix.jointRootFor
#print axioms SaturationMonoid.ProcessGame.Society.M9SourceSuppliedMandateSuffix.mandateInstallationFor
#print axioms SaturationMonoid.ProcessGame.Society.M9SourceSuppliedMandateSuffix.ubiInstallationFor
#print axioms SaturationMonoid.ProcessGame.Society.M9SourceSuppliedMandateSuffix.standing_jointRoot_exact
