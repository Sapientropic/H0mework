import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M8.Renewal.SourceInstalledRenewalProjectionRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M8.Relationship.RelationshipMaintenanceRenewalRegression

/-!
# M8 relationship-maintenance root installation

The same source-generated relationship seed, maintained responsibility,
renewal-control permission and selected debt-flow fibre are installed as one
pre-emitter root coordinate.  Reciprocal flow remains available only at its
own reciprocal event, never as a reverse flow at this occurrence.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M8RelationshipRootInstallationRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Exchange Settlement Renewal Relationship
open Lifecycle.Universal.FixedAdapter
open M3FiniteExchangeFixture
open M8RelationshipMaintenanceFixture
open M8RelationshipMaintenanceRenewalRegression
open M8SourceInstalledRenewalProjectionRegression

def relationshipRootLaw :=
  singletonRootRenewalLaw Lifecycle.actualEventGame
    targetFace.SeedAt RelationshipConsumerAt RelationshipDispositionAt
    relationshipRenewalSeed relationshipConsumer relationshipDisposition

abbrev relationshipInstalledRoot := rootWithRenewalLaw relationshipRootLaw
abbrev relationshipRootVisit := initialVisitWithRenewalLaw relationshipRootLaw
abbrev relationshipRootRecognition :=
  recognitionWithRenewalLaw relationshipRootLaw

def relationshipInstalledRenewal :
    SourceInstalledRenewalAt relationshipRootRecognition
      relationshipRootVisit :=
  installedAtInitialVisit relationshipRootLaw PUnit.unit rfl

def relationshipRootLocalFace :=
  relationshipInstalledRenewal.localFace targetFace.lineageOf
    relationshipStandingOf

@[simp] theorem relationship_root_seed_exact :
    relationshipRootLocalFace.sourceSeed = relationshipRenewalSeed :=
  rfl

@[simp] theorem relationship_root_consumer_exact :
    relationshipRootLocalFace.responsibilityConsumer =
      relationshipConsumer :=
  rfl

@[simp] theorem relationship_root_disposition_exact :
    relationshipRootLocalFace.exactDisposition =
      relationshipDisposition :=
  rfl

def relationship_root_selected_control :
    SelectedMaintenanceControlAt relationshipRootLocalFace.event .a
      (counterparty .a) :=
  selectedMaintenanceControl .a

def relationship_root_selected_debt_flow :
    SelectedMaintenanceDebtFlowAt relationshipRootLocalFace.event .a
      (counterparty .a) :=
  selectedMaintenanceDebtFlow .a

theorem relationship_root_reverse_control_empty :
    SelectedMaintenanceControlAt relationshipRootLocalFace.event
      (counterparty .a) .a → False :=
  reverseMaintenanceControl_empty .a

theorem relationship_root_reverse_debt_flow_empty :
    SelectedMaintenanceDebtFlowAt relationshipRootLocalFace.event
      (counterparty .a) .a → False :=
  reverseMaintenanceDebtFlow_empty .a

structure RelationshipRootInstallationCertificate : Type 3 where
  installed : SourceInstalledRenewalAt relationshipRootRecognition
    relationshipRootVisit
  localFace : RelationshipRenewalFace
  sourceSeedExact : localFace.sourceSeed = relationshipRenewalSeed
  selectedControl : SelectedMaintenanceControlAt localFace.event .a
    (counterparty .a)
  reverseControlEmpty : SelectedMaintenanceControlAt localFace.event
    (counterparty .a) .a → False
  selectedDebtFlow : SelectedMaintenanceDebtFlowAt localFace.event .a
    (counterparty .a)
  reverseDebtFlowEmpty : SelectedMaintenanceDebtFlowAt localFace.event
    (counterparty .a) .a → False
  rootConsumer : RenewalResponsibilityConsumerAt installed.operationalAuthority
  rootProjectionAndNext :
    let evolution := relationshipInstalledRoot.canonicalCausalAnswerAndNext
      (ULift.up relationshipRootVisit)
    evolution.generated =
        relationshipInstalledRoot.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
          relationshipRootVisit ∧
      HEq (evolution.generated.projectionOutcome
          relationshipRootRecognition.rootProjection)
        (relationshipRootRecognition.law.toProjectionLaw.outcomeAt PUnit.unit
          (relationshipInstalledRoot.emitted relationshipRootVisit.current)) ∧
      evolution.nextCurrent =
        relationshipInstalledRoot.generatedNextCurrentAt relationshipRootVisit

def relationshipRootInstallationDirectConsumer :
    RelationshipRootInstallationCertificate where
  installed := relationshipInstalledRenewal
  localFace := relationshipRootLocalFace
  sourceSeedExact := relationship_root_seed_exact
  selectedControl := relationship_root_selected_control
  reverseControlEmpty := relationship_root_reverse_control_empty
  selectedDebtFlow := relationship_root_selected_debt_flow
  reverseDebtFlowEmpty := relationship_root_reverse_debt_flow_empty
  rootConsumer := relationshipInstalledRenewal.rootResponsibilityConsumer
  rootProjectionAndNext :=
    relationshipInstalledRenewal.rootAnswerAndNext_factorizes

end
end M8RelationshipRootInstallationRegression
end Society
end ProcessGame
end SaturationMonoid
