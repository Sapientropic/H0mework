import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M8.RootInstallation.ElectionRootInstallationRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M8.RootInstallation.MoneyRootInstallationRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M8.RootInstallation.RelationshipRootInstallationRegression

/-!
# M8 joint same-root installation

Election, purchasing power, relationship maintenance and AI standing are four
coordinates of one complete projection inventory over the same pre-existing
root source.  The source/ledger compiler and emitter are unchanged; only the
pre-emitter authority inventory is successively uplifted.  Every coordinate
then consumes the same exact temporal visit and the same living next.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M8JointRootInstallationRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Renewal Election Lifecycle Universal Relationship
open ConstructiveRoot.OperationalSearchSourceNativeRootRegression
open M8SourceInstalledRenewalProjectionRegression
open M8ElectionRootInstallationRegression
open M8MoneyRootInstallationRegression
open M8RelationshipRootInstallationRegression
open M8RelationshipMaintenanceFixture
open M8ActualElectionMandateRenewalRegression
open M8AIStandingRenewalRegression
open AI.TraceWitnessedStanding
open DomainReuse

abbrev baseAuthoritySource := BaseRoot.toAuthoritativeRoot.source

def electionAuthoritySource : SourceNativeAuthoritySource N V :=
  withRenewalProjection baseAuthoritySource electionRootLaw

def moneyAuthoritySource : SourceNativeAuthoritySource N V :=
  withRenewalProjection electionAuthoritySource moneyRootLaw

def relationshipAuthoritySource : SourceNativeAuthoritySource N V :=
  withRenewalProjection moneyAuthoritySource relationshipRootLaw

def jointAuthoritySource : SourceNativeAuthoritySource N V :=
  withRenewalProjection relationshipAuthoritySource aiRenewalLaw

/-- One root, one emitter, one ledger compiler, four installed domain
coordinates. -/
def jointRoot : SourceNativeLivingRootClosure N V where
  source :=
    { base := jointAuthoritySource
      terminalHandoff := jointAuthoritySource.emptyFaithfulTerminalHandoff
        (fun _ => ⟨fun terminal => nomatch terminal⟩) }
  emitted := emitted
  compiler_commutes := fun _ => rfl

def jointVisit : SourceNativeTemporalVisitAt
    jointRoot.toAuthoritativeRoot.toLedgerRoot :=
  .finite jointRoot.toAuthoritativeRoot.toRoot.initialVisit

def electionInstallationInJoint : SourceNativeProjectionLaw.InstallationAt
    electionRootLaw.toProjectionLaw
    jointRoot.toAuthoritativeRoot.source.projectionLaw :=
  (((renewalComponent baseAuthoritySource electionRootLaw).trans
      (inheritedByRenewal electionAuthoritySource moneyRootLaw)).trans
      (inheritedByRenewal moneyAuthoritySource relationshipRootLaw)).trans
      (inheritedByRenewal relationshipAuthoritySource aiRenewalLaw)

def moneyInstallationInJoint : SourceNativeProjectionLaw.InstallationAt
    moneyRootLaw.toProjectionLaw
    jointRoot.toAuthoritativeRoot.source.projectionLaw :=
  ((renewalComponent electionAuthoritySource moneyRootLaw).trans
      (inheritedByRenewal moneyAuthoritySource relationshipRootLaw)).trans
      (inheritedByRenewal relationshipAuthoritySource aiRenewalLaw)

def relationshipInstallationInJoint :
    SourceNativeProjectionLaw.InstallationAt
      relationshipRootLaw.toProjectionLaw
      jointRoot.toAuthoritativeRoot.source.projectionLaw :=
  (renewalComponent moneyAuthoritySource relationshipRootLaw).trans
    (inheritedByRenewal relationshipAuthoritySource aiRenewalLaw)

def aiInstallationInJoint : SourceNativeProjectionLaw.InstallationAt
    aiRenewalLaw.toProjectionLaw
    jointRoot.toAuthoritativeRoot.source.projectionLaw :=
  renewalComponent relationshipAuthoritySource aiRenewalLaw

def jointElectionRecognition : SourceNativeRenewalRecognitionAt jointRoot
    (Election.electionGame electionHistory)
    (Election.electionActionController electionHistory
      M8ActualElectionMandateRenewalRegression.lineageCompiler).ActionSeed
    (Election.electionActionController electionHistory
      M8ActualElectionMandateRenewalRegression.lineageCompiler).actionSeedAt
    (Election.ElectionRenewalConsumerAt electionHistory
      M8ActualElectionMandateRenewalRegression.lineageCompiler)
    (Election.ElectionRenewalDispositionAt electionHistory
      M8ActualElectionMandateRenewalRegression.lineageCompiler) where
  law := electionRootLaw
  installation := electionInstallationInJoint

def jointMoneyRecognition : SourceNativeRenewalRecognitionAt jointRoot
    Lifecycle.actualEventGame
    M3ExchangeSettlementPriceRegression.residualConsumerCompiler.ActivationSeed
    M3ExchangeSettlementPriceRegression.residualConsumerCompiler.activationSeedAt
    RootPurchasingPowerConsumerAt RootPurchasingPowerDispositionAt where
  law := moneyRootLaw
  installation := moneyInstallationInJoint

def jointRelationshipRecognition : SourceNativeRenewalRecognitionAt jointRoot
    Lifecycle.actualEventGame
    Lifecycle.Universal.FixedAdapter.targetFace.Seed
    Lifecycle.Universal.FixedAdapter.targetFace.SeedAt
    M8RelationshipMaintenanceRenewalRegression.RelationshipConsumerAt
    M8RelationshipMaintenanceRenewalRegression.RelationshipDispositionAt where
  law := relationshipRootLaw
  installation := relationshipInstallationInJoint

def jointAIRecognition : SourceNativeRenewalRecognitionAt jointRoot
    threeAgentProcessGame ThreeCycleTime
    DomainReuse.MultiAgent.seedAt
    M8AIStandingRenewalRegression.AIConsumerAt
    M8AIStandingRenewalRegression.AIDispositionAt where
  law := aiRenewalLaw
  installation := aiInstallationInJoint

def jointElectionRenewal :
    SourceInstalledRenewalAt jointElectionRecognition jointVisit :=
  SourceInstalledRenewalAt.generate PUnit.unit rfl

def jointMoneyRenewal :
    SourceInstalledRenewalAt jointMoneyRecognition jointVisit :=
  SourceInstalledRenewalAt.generate PUnit.unit rfl

def jointRelationshipRenewal :
    SourceInstalledRenewalAt jointRelationshipRecognition jointVisit :=
  SourceInstalledRenewalAt.generate PUnit.unit rfl

def jointAIRenewal :
    SourceInstalledRenewalAt jointAIRecognition jointVisit :=
  SourceInstalledRenewalAt.generate PUnit.unit rfl

def jointElectionLocalFace :=
  jointElectionRenewal.localFace
    (fun _ exactSeed => lineageCompiler.controllerOf
      exactSeed.1.controllerSeed)
    (mandateStandingOf electionHistory lineageCompiler)

def jointMoneyLocalFace :=
  jointMoneyRenewal.localFace
    (fun _ seed =>
      (M3ExchangeSettlementPriceRegression.residualConsumerCompiler
        |>.openSettlement seed.1).obligation.lineage)
    M8AcceptanceSettlementRenewalRegression.moneyStandingOf

def jointRelationshipLocalFace :=
  jointRelationshipRenewal.localFace
    Lifecycle.Universal.FixedAdapter.targetFace.lineageOf
    M8RelationshipMaintenanceRenewalRegression.relationshipStandingOf

def jointAILocalFace :=
  jointAIRenewal.localFace DomainReuse.MultiAgent.lineageOf aiStandingOf

@[simp] theorem joint_election_power_exact :
    jointElectionLocalFace.responsibilityConsumer.1.1 =
      mandateActionPower electionHistory lineageCompiler :=
  rfl

@[simp] theorem joint_money_standing_exact :
    jointMoneyLocalFace.responsibilityConsumer =
      rootPurchasingPowerStanding :=
  rfl

def joint_relationship_selected_debt_flow :
    SelectedMaintenanceDebtFlowAt jointRelationshipLocalFace.event .a
      (M3FiniteExchangeFixture.counterparty .a) :=
  selectedMaintenanceDebtFlow .a

@[simp] theorem joint_ai_consumer_edge_exact :
    jointAILocalFace.responsibilityConsumer.edge = renewalEdge .t0 :=
  rfl

/-- All four domain restrictions share the literal temporal root occurrence
and the literal generated next; no face can supply either value. -/
structure JointM8RootInstallationCertificate : Type 3 where
  election : SourceInstalledRenewalAt jointElectionRecognition jointVisit
  money : SourceInstalledRenewalAt jointMoneyRecognition jointVisit
  relationship : SourceInstalledRenewalAt jointRelationshipRecognition jointVisit
  ai : SourceInstalledRenewalAt jointAIRecognition jointVisit
  electionPowerExact :
    jointElectionLocalFace.responsibilityConsumer.1.1 =
      mandateActionPower electionHistory lineageCompiler
  moneyStandingExact : jointMoneyLocalFace.responsibilityConsumer =
    rootPurchasingPowerStanding
  relationshipDebtFlow :
    SelectedMaintenanceDebtFlowAt jointRelationshipLocalFace.event .a
      (M3FiniteExchangeFixture.counterparty .a)
  aiConsumerEdgeExact :
    jointAILocalFace.responsibilityConsumer.edge = renewalEdge .t0
  electionFactorizes : election.RootAnswerAndNextFactorizes
  moneyFactorizes : money.RootAnswerAndNextFactorizes
  relationshipFactorizes : relationship.RootAnswerAndNextFactorizes
  aiFactorizes : ai.RootAnswerAndNextFactorizes
  sameLedgerSource : jointRoot.toAuthoritativeRoot.toLedgerRoot.source =
    BaseRoot.toAuthoritativeRoot.toLedgerRoot.source

def jointM8RootInstallationDirectConsumer :
    JointM8RootInstallationCertificate where
  election := jointElectionRenewal
  money := jointMoneyRenewal
  relationship := jointRelationshipRenewal
  ai := jointAIRenewal
  electionPowerExact := joint_election_power_exact
  moneyStandingExact := joint_money_standing_exact
  relationshipDebtFlow := joint_relationship_selected_debt_flow
  aiConsumerEdgeExact := joint_ai_consumer_edge_exact
  electionFactorizes := jointElectionRenewal.rootAnswerAndNext_factorizes
  moneyFactorizes := jointMoneyRenewal.rootAnswerAndNext_factorizes
  relationshipFactorizes :=
    jointRelationshipRenewal.rootAnswerAndNext_factorizes
  aiFactorizes := jointAIRenewal.rootAnswerAndNext_factorizes
  sameLedgerSource := rfl

end
end M8JointRootInstallationRegression
end Society
end ProcessGame
end SaturationMonoid
