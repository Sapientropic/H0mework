import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M9.JointRoot.Mandate.SourceSuppliedMandateSuffix
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Law.SourceHealthCessationRenewal
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Mandate.Succession.SourceMandateSuccession

/-!
# Successor-mandate root with one supplied health-cessation service slot

The existing prefix through the source-generated successor mandate is fixed.
This assembler replaces the fifth essential-service coordinate with the exact
health-cessation law, then reuses the existing route, common-clearing and
backstop suffix.  It does not append a ninth law: successor mandate, health
cessation and UBI remain three distinct coordinates in the same inventory.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M9SourceHealthCessationSuffix

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Renewal Election
open M8ActualElectionMandateRenewalRegression
open M9ProofCarryingRenewalInquiryRoot
open M9SourceSuppliedMandateSuffix
open M14SourceMandateRenewal
open M14SourceMandateSuccession
open M14SourceHealthCessationRenewal
open M14SourceRouteOutageRestoration
open M14SourceCommonClearingRenewal
open M14SourceClearingBackstopRenewal

abbrev N := M9ProofCarryingRenewalInquiryRoot.N
abbrev V := M9ProofCarryingRenewalInquiryRoot.V

def successorMandateAuthoritySource : SourceNativeAuthoritySource N V :=
  mandateAuthoritySourceFor sourceMandateSuccessorHistory

def healthCessationLaw : SourceHealthCessationRenewalLawAt
    successorMandateAuthoritySource.restructuringSource.toLedgerSource :=
  sourceHealthCessationRenewalLaw mandateRootShell

def healthCessationAuthoritySource : SourceNativeAuthoritySource N V :=
  withRenewalProjection successorMandateAuthoritySource healthCessationLaw

def routeLaw : SourceRouteOutageRestorationLawAt
    healthCessationAuthoritySource.restructuringSource.toLedgerSource :=
  sourceRouteOutageRestorationLaw mandateRootShell

def routeAuthoritySource : SourceNativeAuthoritySource N V :=
  withRenewalProjection healthCessationAuthoritySource routeLaw

def commonClearingLaw : SourceCommonClearingRenewalLawAt
    routeAuthoritySource.restructuringSource.toLedgerSource :=
  sourceCommonClearingRenewalLaw mandateRootShell

def commonClearingAuthoritySource : SourceNativeAuthoritySource N V :=
  withRenewalProjection routeAuthoritySource commonClearingLaw

def clearingBackstopLaw : SourceClearingBackstopRenewalLawAt
    commonClearingAuthoritySource.restructuringSource.toLedgerSource :=
  sourceClearingBackstopRenewalLaw mandateRootShell

def jointAuthoritySource : SourceNativeAuthoritySource N V :=
  withRenewalProjection commonClearingAuthoritySource clearingBackstopLaw

def jointRoot : SourceNativeLivingRootClosure N V where
  source :=
    { base := jointAuthoritySource
      terminalHandoff := jointAuthoritySource.emptyFaithfulTerminalHandoff
        (fun _ => ⟨fun terminal => nomatch terminal⟩) }
  emitted := RootInquiryU8CompletionRegression.root.emitted
  compiler_commutes := fun _ => rfl

def jointInitialVisit : SourceNativeTemporalVisitAt
    jointRoot.toAuthoritativeRoot.toLedgerRoot :=
  .finite jointRoot.toAuthoritativeRoot.toRoot.initialVisit

/-! ## Coordinate inventory -/

def inquiryProjection :
    jointRoot.toAuthoritativeRoot.source.projectionLaw.Projection :=
  .inherited
    (.inherited
      (.inherited
        (.inherited (.inherited (.inherited (.inherited (.inherited .inquiry)))))))

/-- The failure leaf inherited beside `inquiryProjection` from the base
RootInquiry U8 root.  This is a name for an existing coordinate, not a new
projection-law installation. -/
def failureProjection :
    jointRoot.toAuthoritativeRoot.source.projectionLaw.Projection :=
  .inherited
    (.inherited
      (.inherited
        (.inherited (.inherited (.inherited (.inherited (.inherited .failure)))))))

def proofCarryingProjection :
    jointRoot.toAuthoritativeRoot.source.projectionLaw.Projection :=
  .inherited
    (.inherited
      (.inherited (.inherited (.inherited (.inherited (.inherited .renewal))))))

def ubiProjection :
    jointRoot.toAuthoritativeRoot.source.projectionLaw.Projection :=
  .inherited
    (.inherited (.inherited (.inherited (.inherited (.inherited .renewal)))))

def recognitionProjection :
    jointRoot.toAuthoritativeRoot.source.projectionLaw.Projection :=
  .inherited (.inherited (.inherited (.inherited (.inherited .renewal))))

def mandateProjection :
    jointRoot.toAuthoritativeRoot.source.projectionLaw.Projection :=
  .inherited (.inherited (.inherited (.inherited .renewal)))

def healthCessationProjection :
    jointRoot.toAuthoritativeRoot.source.projectionLaw.Projection :=
  .inherited (.inherited (.inherited .renewal))

def routeProjection :
    jointRoot.toAuthoritativeRoot.source.projectionLaw.Projection :=
  .inherited (.inherited .renewal)

def commonClearingProjection :
    jointRoot.toAuthoritativeRoot.source.projectionLaw.Projection :=
  .inherited .renewal

def clearingBackstopProjection :
    jointRoot.toAuthoritativeRoot.source.projectionLaw.Projection :=
  .renewal

theorem healthCessationProjection_distinct :
    healthCessationProjection ≠ mandateProjection ∧
      healthCessationProjection ≠ ubiProjection ∧
      healthCessationProjection ≠ recognitionProjection ∧
      healthCessationProjection ≠ proofCarryingProjection ∧
      healthCessationProjection ≠ inquiryProjection ∧
      healthCessationProjection ≠ routeProjection ∧
      healthCessationProjection ≠ commonClearingProjection ∧
      healthCessationProjection ≠ clearingBackstopProjection := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals intro equality
  all_goals cases equality

/-- The inherited failure face is distinct from every other named coordinate
in this exact inventory, including its sibling inquiry leaf. -/
theorem failureProjection_distinct :
    failureProjection ≠ inquiryProjection ∧
      failureProjection ≠ proofCarryingProjection ∧
      failureProjection ≠ ubiProjection ∧
      failureProjection ≠ recognitionProjection ∧
      failureProjection ≠ mandateProjection ∧
      failureProjection ≠ healthCessationProjection ∧
      failureProjection ≠ routeProjection ∧
      failureProjection ≠ commonClearingProjection ∧
      failureProjection ≠ clearingBackstopProjection := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals intro equality
  all_goals cases equality

/-! ## Installation paths -/

def preBackstopInventory : SourceNativeProjectionLaw.InstallationAt
    routeAuthoritySource.projectionLaw
    jointRoot.toAuthoritativeRoot.source.projectionLaw :=
  (inheritedByRenewal routeAuthoritySource commonClearingLaw).trans
    (inheritedByRenewal commonClearingAuthoritySource clearingBackstopLaw)

def healthCessationInstallation :
    SourceNativeProjectionLaw.InstallationAt
      healthCessationLaw.toProjectionLaw
      jointRoot.toAuthoritativeRoot.source.projectionLaw :=
  (((renewalComponent successorMandateAuthoritySource healthCessationLaw).trans
      (inheritedByRenewal healthCessationAuthoritySource routeLaw)).trans
    (inheritedByRenewal routeAuthoritySource commonClearingLaw)).trans
    (inheritedByRenewal commonClearingAuthoritySource clearingBackstopLaw)

def mandateInstallation : SourceNativeProjectionLaw.InstallationAt
    (sourceMandateRenewalLawFor sourceMandateSuccessorHistory
      mandateRootShell).toProjectionLaw
    jointRoot.toAuthoritativeRoot.source.projectionLaw :=
  (((sourceMandateRenewalComponentFor sourceMandateSuccessorHistory
      recognitionAuthoritySource mandateRootShell).trans
        (inheritedByRenewal successorMandateAuthoritySource
          healthCessationLaw)).trans
      (inheritedByRenewal healthCessationAuthoritySource routeLaw)).trans
    (preBackstopInventory)

def ubiInstallation : SourceNativeProjectionLaw.InstallationAt
    ubiLaw.toProjectionLaw
    jointRoot.toAuthoritativeRoot.source.projectionLaw :=
  (((((renewalComponent proofCarryingAuthoritySource ubiLaw).trans
      (inheritedByRenewal ubiAuthoritySource recognitionWitnessLaw)).trans
    (inheritedByRenewal recognitionAuthoritySource
      (sourceMandateRenewalLawFor sourceMandateSuccessorHistory
        mandateRootShell))).trans
    (inheritedByRenewal successorMandateAuthoritySource
      healthCessationLaw)).trans
    (inheritedByRenewal healthCessationAuthoritySource routeLaw)).trans
    (preBackstopInventory)

def healthCessationRecognition : SourceNativeRenewalRecognitionAt jointRoot
    M14SourceHealthCessationRenewal.LocalGame
    M14SourceHealthCessationRenewal.LocalSeed
    M14SourceHealthCessationRenewal.LocalSeedAt
    M14SourceHealthCessationRenewal.SourceHealthCessationConsumerAt
    M14SourceHealthCessationRenewal.SourceHealthCessationDispositionAt where
  law := healthCessationLaw
  installation := healthCessationInstallation

def mandateRecognition : SourceNativeRenewalRecognitionAt jointRoot
    (SourceMandateGameFor sourceMandateSuccessorHistory)
    (SourceMandateSeedFor sourceMandateSuccessorHistory)
    (SourceMandateSeedAtFor sourceMandateSuccessorHistory)
    (SourceMandateConsumerAtFor sourceMandateSuccessorHistory)
    (SourceMandateDispositionAtFor sourceMandateSuccessorHistory) where
  law := sourceMandateRenewalLawFor sourceMandateSuccessorHistory
    mandateRootShell
  installation := mandateInstallation

def ubiRecognition : SourceNativeRenewalRecognitionAt jointRoot
    M14UBIProofCarryingRootRestriction.LocalGame
    M14UBIProofCarryingRootRestriction.LocalSeed
    M14UBIProofCarryingRootRestriction.LocalSeedAt
    M14UBIProofCarryingRootRestriction.UBIConsumerAt
    M14UBIProofCarryingRootRestriction.UBIDispositionAt where
  law := ubiLaw
  installation := ubiInstallation

abbrev HealthCessationComponentProjection :=
  healthCessationLaw.toProjectionLaw.Projection

def SecondInstalledHealthCessationCoordinate : Prop :=
  ∃ left right : HealthCessationComponentProjection,
    healthCessationInstallation.embed left ≠
      healthCessationInstallation.embed right

theorem secondInstalledHealthCessationCoordinate_isEmpty :
    IsEmpty SecondInstalledHealthCessationCoordinate := by
  constructor
  rintro ⟨left, right, distinct⟩
  cases left
  cases right
  exact distinct rfl

end
end M9SourceHealthCessationSuffix
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M9SourceHealthCessationSuffix.jointRoot
#print axioms SaturationMonoid.ProcessGame.Society.M9SourceHealthCessationSuffix.healthCessationInstallation
#print axioms SaturationMonoid.ProcessGame.Society.M9SourceHealthCessationSuffix.healthCessationProjection_distinct
#print axioms SaturationMonoid.ProcessGame.Society.M9SourceHealthCessationSuffix.failureProjection_distinct
#print axioms SaturationMonoid.ProcessGame.Society.M9SourceHealthCessationSuffix.secondInstalledHealthCessationCoordinate_isEmpty
