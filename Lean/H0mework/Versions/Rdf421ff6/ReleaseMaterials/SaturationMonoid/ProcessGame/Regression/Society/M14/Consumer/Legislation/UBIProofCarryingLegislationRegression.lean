import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Legislation.ProofCarryingPolicyCoordinate
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M9.Legislation.ProofCarryingLegislationRegression
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Capture.StructuralRentCaptureRegression
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Policy.ProofCarryingExitRepairRenewalRegression
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Policy.UBIPolicySelfU8Regression
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.UBISelfU8SameRootRegression

/-!
# M14 UBI proof-carrying legislation

The existing M9 PCL and the UBI renewal are distinct projection coordinates
of one literal root.  The generic policy-coordinate splice preserves that
separation while making the UBI consumer and action disposition available to
the exact PCL occurrence.

The fixed legislation below then consumes root-installed structural rent,
the source-generated ordinary remove-capture repair, and the existing
automatic revolutionary self-U8 path.  Ordinary and revolutionary nexts stay
strictly distinct.  No second court, root, ledger, policy registry, optimizer,
branch selector, effectiveness premise, revision target, or completed future
is introduced.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14UBIProofCarryingLegislationRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Exchange Settlement Price Money UBI
open Renewal Observer Legislation Revision Capacity
open ConstructiveRoot.RootInquiryCompletion
open ConstructiveRoot.ObstructionGeneratedMinimalCoface
open Settlement.SourceOwnedSettlementCompiler
open UBI.Capture UBI.Policy
open M3FiniteExchangeFixture M3ExchangeSettlementPriceRegression
open M3SettlementDispositionRegression
open M9ProofCarryingRenewalInquiryRoot
open M9ProofCarryingRenewalInquiryRuntime
open M9ProofCarryingRenewalU8Revision
open M9ProofCarryingLegislationRegression
open M14UBIProofCarryingRootRestriction
open M14UBIExitCapacityFixture
open M14UBIPeriodicRootHistory
open M14UBIPeriodicActualServiceCapacity
open M14StructuralRentCaptureRegression
open M14ProofCarryingExitRepairRegression
open M14TenureCaptureRouteRepairNoGoRegression
open M14ProofCarryingExitRepairRenewalRegression
open M14UBIPolicyBreakingOccurrence
open M14UBIPolicySelfU8Regression
open M14UBISelfU8SameRootRegression

/-! ## Exact generic policy-coordinate splice -/

/-- The base PCL renewal and UBI renewal share the exact source entry,
selected row, and successor.  Root and visit already coincide by type. -/
theorem ubiPolicyCoordinate : SourceInstalledPolicyCoordinateAt
    installedRenewal installedUBI where
  sourceEntry_eq := rfl
  selectedRow_heq := HEq.rfl
  successor_heq := HEq.rfl

/-- Existing PCL extended by the exact UBI coordinate. -/
def proofCarryingUBIPolicyLegislation :
    ProofCarryingPolicyLegislationAt proofCarryingLegislation installedUBI
      ubiPolicyCoordinate :=
  sourceGeneratedProofCarryingPolicyLegislation
    proofCarryingLegislation installedUBI ubiPolicyCoordinate

def proofCarryingUBIPolicyLegislationConsumer :=
  proofCarryingUBIPolicyLegislation.independentConsumer

@[simp] theorem policy_consumer_is_preEmitter_ubi_restriction :
    proofCarryingUBIPolicyLegislation.policyConsumer =
      sourceGeneratedUBIRootRestriction :=
  rfl

@[simp] theorem policy_disposition_is_preEmitter_applied_repair :
    proofCarryingUBIPolicyLegislation.policyDisposition =
      sourceGeneratedUBIDisposition :=
  rfl

@[simp] theorem policy_source_entry_is_base_pcl_entry :
    installedUBI.payload.sourceEntry = installedRenewal.payload.sourceEntry :=
  proofCarryingUBIPolicyLegislation.sourceEntry_eq_base

theorem policy_selected_row_is_base_pcl_row :
    HEq installedUBI.payload.selectedRow installedRenewal.payload.selectedRow :=
  proofCarryingUBIPolicyLegislation.selectedRow_heq_base

theorem policy_successor_is_base_pcl_successor :
    HEq installedUBI.payload.successor installedRenewal.payload.successor :=
  proofCarryingUBIPolicyLegislation.successor_heq_base

theorem policy_root_factorizes : installedUBI.RootAnswerAndNextFactorizes :=
  proofCarryingUBIPolicyLegislation.policyRootAnswerAndNext_factorizes

theorem policy_and_base_pcl_coordinates_remain_distinct :
    jointUBIProjection ≠ jointProofCarryingProjection :=
  ubi_projection_ne_proofCarrying_projection

theorem policy_and_pcl_runtime_share_exact_occurrence : HEq
    ((sourceGeneratedRuntimeInquiryCoordinateAt jointRuntime 0).1.state.base.root
      |>.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
        (sourceGeneratedRuntimeInquiryCoordinateAt jointRuntime 0).1.state.base.visit)
    (jointRoot.toAuthoritativeRoot.toLedgerRoot
      |>.exactTemporalCausalEventAt jointVisit) :=
  inquiryOccurrence_is_literalInstalledOccurrence

/-! ## Fixed UBI legislative standing -/

/-- Strong source-generated UBI legislation carrier.  The constructor is
private and its producer takes no policy content or outcome. -/
structure SourceGeneratedUBIProofCarryingLegislationAt : Type 18 where
  private mk ::
  policyLegislation :
    ProofCarryingPolicyLegislationAt proofCarryingLegislation installedUBI
      ubiPolicyCoordinate
  structuralRent : SourceGeneratedStructuralRentCaptureAt 0
  ordinaryRepair : SourceInstalledProofCarryingExitRepairRenewalAt 0
    (canonicalRepairAt (tenureCaptureOriginAt 0))

/-- Sole fixed producer. -/
def sourceGeneratedUBIProofCarryingLegislation :
    SourceGeneratedUBIProofCarryingLegislationAt where
  policyLegislation := proofCarryingUBIPolicyLegislation
  structuralRent := structuralRentCaptureAt 0
  ordinaryRepair :=
    SourceInstalledProofCarryingExitRepairRenewalAt.generate 0

@[simp] theorem ordinary_repair_disposition_is_policy_disposition :
    (sourceGeneratedUBIProofCarryingLegislation.ordinaryRepair.source.installed
      ).payload.disposition =
      proofCarryingUBIPolicyLegislation.policyDisposition :=
  rfl

namespace SourceGeneratedUBIProofCarryingLegislationAt

variable (legislation : SourceGeneratedUBIProofCarryingLegislationAt)

/-- The PCL's pre-existing lifecycle residual is literally the bearer of the
open settlement captured by UBI; the capture also retains an activated,
source-owned residual consumer. -/
theorem residual_destination_commutes
    (legislation : SourceGeneratedUBIProofCarryingLegislationAt) :
    proofCarryingLegislation.residualBearer =
        OpenSettlementAt.residualBearer
          (exactOpenSettlement exactResidualActivation) ∧
      Nonempty (OpenSettlementAt.ActivatedResidualConsumerAt
        (exactOpenSettlement exactResidualActivation)) ∧
      Nonempty (SourceOwnsResponsibilityIncidence V
        (P.boundarySource
          capturedProgram.purchasingPowerStanding.activatedConsumer.activation)
        (exactOpenSettlement exactResidualActivation).obligation) := by
  constructor
  · rfl
  exact ⟨legislation.structuralRent.purposeCapture.activatedResidualConsumer,
    legislation.structuralRent.purposeCapture.sourceOwnedResidual⟩

/-- Ordinary policy disposition is the action already installed in the UBI
payload.  Outcome capacity and next are downstream calculations. -/
theorem ordinary_disposition_generates_repaired_next :
    canonicalRepairAt (tenureCaptureOriginAt 0) =
        legislation.ordinaryRepair.source.installed.payload.disposition.repairAt ∧
      canonicalRepairAt (tenureCaptureOriginAt 0) = .removeCapture ∧
      legislation.ordinaryRepair.ordinarySelectedWrite.sourceRow.CommutesWithWorld ∧
      legislation.ordinaryRepair.source.installed.RootAnswerAndNextFactorizes ∧
      legislation.ordinaryRepair.generatedNext =
        jointRoot.generatedNextCurrentAt (temporalVisitAt 0) ∧
      legislation.ordinaryRepair.generatedNext.visit = temporalVisitAt 1 ∧
      (geometryCompilerAt 1).actionableExitCapacity = 1 := by
  exact ⟨legislation.ordinaryRepair.repair_eq_appliedDisposition,
    legislation.ordinaryRepair.repair_eq_removeCapture,
    legislation.ordinaryRepair.ordinarySelectedWrite_commutes,
    legislation.ordinaryRepair.appliedReform.rootFactorization,
    legislation.ordinaryRepair.generatedNext_eq_rootCompiler,
    legislation.ordinaryRepair.generatedNext_repairedFace_capacity_eq_one.1,
    legislation.ordinaryRepair.generatedNext_repairedFace_capacity_eq_one.2.2⟩

/-- The policy coordinate cannot choose the branch.  The existing PCL
runtime selected revolution, and the UBI audit factors into that exact core. -/
theorem revolutionary_disposition_is_automatic :
    legislation.policyLegislation.branchKind =
        SourceGeneratedInstitutionalRevisionKind.revolution ∧
      Nonempty (FaithfulCofaceMorphism u8Gate.minimalCoface
        jointCore.revision.generate.toAdmissibleMinimalCoface) ∧
      SourceNativeInquiryRuntime.CofaceRealizationResumptionAt
        jointCore jointRuntime 0 ∧
      legislation.policyLegislation.revolutionaryConsumption =
        some exactRevolutionaryConsumption := by
  exact ⟨rfl, policyGate_factorizes_into_jointCore,
    runtime_consumes_jointCore_after_policy_factorization, rfl⟩

/-- Ordinary same-law repair and revolutionary revised-law update are both
accounted at the same occurrence but remain strictly different nexts. -/
theorem ordinary_and_revolutionary_nexts_distinct :
    (⟨M9ProofCarryingRenewalInquiryRoot.N,
      legislation.ordinaryRepair.generatedNext⟩ :
        AnyAuthoritativeRootCurrent) ≠
      legislation.policyLegislation.generatedNext := by
  rw [legislation.ordinaryRepair.generatedNext_eq_rootCompiler]
  exact ubi_old_next_ne_selfU8_revisedNext

/-- Observer-only policy cannot select the repair; source cause remains
necessary even after the legislation coordinate has been generated. -/
theorem capacity_observer_cannot_legislate_repair
    (_legislation : SourceGeneratedUBIProofCarryingLegislationAt) :
    ¬ ∃ reconstruct : Nat → ExactExitRepair,
      ∀ origin : RepairFailureOriginAt 0,
        reconstruct (failureCapacityReadoutAt 0 origin) =
          canonicalRepairAt origin :=
  no_capacity_only_canonical_repair_reconstruction 0

end SourceGeneratedUBIProofCarryingLegislationAt

/-! ## Independent certificate -/

structure UBIProofCarryingLegislationCertificate : Prop where
  standing : Nonempty SourceGeneratedUBIProofCarryingLegislationAt
  policyConsumerExact :
    proofCarryingUBIPolicyLegislation.policyConsumer =
      sourceGeneratedUBIRootRestriction
  policyDispositionExact :
    proofCarryingUBIPolicyLegislation.policyDisposition =
      sourceGeneratedUBIDisposition
  sameEntry :
    installedUBI.payload.sourceEntry = installedRenewal.payload.sourceEntry
  sameSelectedRow :
    HEq installedUBI.payload.selectedRow installedRenewal.payload.selectedRow
  sameSuccessor :
    HEq installedUBI.payload.successor installedRenewal.payload.successor
  coordinatesDistinct : jointUBIProjection ≠ jointProofCarryingProjection
  ordinaryDispositionIsPolicyDisposition :
    (sourceGeneratedUBIProofCarryingLegislation.ordinaryRepair.source.installed
      ).payload.disposition =
      proofCarryingUBIPolicyLegislation.policyDisposition
  pclRuntimeSameOccurrence : HEq
    ((sourceGeneratedRuntimeInquiryCoordinateAt jointRuntime 0).1.state.base.root
      |>.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
        (sourceGeneratedRuntimeInquiryCoordinateAt jointRuntime 0).1.state.base.visit)
    (jointRoot.toAuthoritativeRoot.toLedgerRoot
      |>.exactTemporalCausalEventAt jointVisit)
  ordinaryRepairSameOccurrence :
    sourceGeneratedUBIProofCarryingLegislation.ordinaryRepair.rootOccurrence =
      jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
        (temporalVisitAt 0)
  residualDestination :
    proofCarryingLegislation.residualBearer =
        OpenSettlementAt.residualBearer
          (exactOpenSettlement exactResidualActivation) ∧
      Nonempty (OpenSettlementAt.ActivatedResidualConsumerAt
        (exactOpenSettlement exactResidualActivation)) ∧
      Nonempty (SourceOwnsResponsibilityIncidence V
        (P.boundarySource
          capturedProgram.purchasingPowerStanding.activatedConsumer.activation)
        (exactOpenSettlement exactResidualActivation).obligation)
  automaticSelfU8 :
    sourceGeneratedUBIProofCarryingLegislation.policyLegislation.branchKind =
        SourceGeneratedInstitutionalRevisionKind.revolution ∧
      Nonempty (FaithfulCofaceMorphism u8Gate.minimalCoface
        jointCore.revision.generate.toAdmissibleMinimalCoface) ∧
      SourceNativeInquiryRuntime.CofaceRealizationResumptionAt
        jointCore jointRuntime 0
  distinctOrdinaryAndRevolutionaryNexts :
    (⟨M9ProofCarryingRenewalInquiryRoot.N,
      sourceGeneratedUBIProofCarryingLegislation.ordinaryRepair.generatedNext⟩ :
        AnyAuthoritativeRootCurrent) ≠
      sourceGeneratedUBIProofCarryingLegislation.policyLegislation.generatedNext
  noCapacityOnlyRepairLegislation :
    ¬ ∃ reconstruct : Nat → ExactExitRepair,
      ∀ origin : RepairFailureOriginAt 0,
        reconstruct (failureCapacityReadoutAt 0 origin) =
          canonicalRepairAt origin

theorem ubiProofCarryingLegislationDirectConsumer :
    UBIProofCarryingLegislationCertificate where
  standing := ⟨sourceGeneratedUBIProofCarryingLegislation⟩
  policyConsumerExact := policy_consumer_is_preEmitter_ubi_restriction
  policyDispositionExact := policy_disposition_is_preEmitter_applied_repair
  sameEntry := policy_source_entry_is_base_pcl_entry
  sameSelectedRow := policy_selected_row_is_base_pcl_row
  sameSuccessor := policy_successor_is_base_pcl_successor
  coordinatesDistinct := policy_and_base_pcl_coordinates_remain_distinct
  ordinaryDispositionIsPolicyDisposition :=
    ordinary_repair_disposition_is_policy_disposition
  pclRuntimeSameOccurrence := policy_and_pcl_runtime_share_exact_occurrence
  ordinaryRepairSameOccurrence :=
    sourceGeneratedUBIProofCarryingLegislation.ordinaryRepair.rootOccurrence_eq
  residualDestination :=
    sourceGeneratedUBIProofCarryingLegislation.residual_destination_commutes
  automaticSelfU8 := ⟨
    (sourceGeneratedUBIProofCarryingLegislation
      |>.revolutionary_disposition_is_automatic).1,
    (sourceGeneratedUBIProofCarryingLegislation
      |>.revolutionary_disposition_is_automatic).2.1,
    (sourceGeneratedUBIProofCarryingLegislation
      |>.revolutionary_disposition_is_automatic).2.2.1⟩
  distinctOrdinaryAndRevolutionaryNexts :=
    sourceGeneratedUBIProofCarryingLegislation
      |>.ordinary_and_revolutionary_nexts_distinct
  noCapacityOnlyRepairLegislation :=
    sourceGeneratedUBIProofCarryingLegislation
      |>.capacity_observer_cannot_legislate_repair

end
end M14UBIProofCarryingLegislationRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14UBIProofCarryingLegislationRegression.sourceGeneratedUBIProofCarryingLegislation
#print axioms SaturationMonoid.ProcessGame.Society.M14UBIProofCarryingLegislationRegression.ubiProofCarryingLegislationDirectConsumer
