import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.UBIProofCarryingRootCapacity
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.ExitCapacityRenewalRegression
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M13.Consumer.ReflexiveTheoryConsumerRegression

/-!
# M14 UBI / self-U8 same-root direct consumer

This consumer closes the declaration-scope seam rejected by the first M14
draft.  UBI does not bring a sibling root or claim to trigger the existing
mother-law failure.  Instead its exact source program, the proof-carrying
renewal, and the inquiry/failure faces are coordinates of one literal old
root.  The existing M13 self-U8 consumes that same root occurrence and row,
while actionable UBI capacity is generated only after the actual service
join.  Ordinary renewal next and revolutionary revised next remain distinct.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14UBISelfU8SameRootRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Renewal Capacity Space CrossingCost UBI Legislation Theory Revision
open UBI.Capacity UBI.Capacity.SourceOwnedExitGeometryCompilerAt
open ConstructiveRoot.RootInquiryCompletion
open M9ProofCarryingRenewalInquiryRoot
open M9ProofCarryingRenewalInquiryRuntime
open M14UBIExitCapacityFixture
open M14UBIProofCarryingRootRestriction
open M14UBIProofCarryingRootCapacity
open M14ExitCapacityRenewalRegression

theorem selfU8_runtime_root_is_ubi_root : HEq
    (sourceGeneratedRuntimeInquiryCoordinateAt jointRuntime 0).1.state.base.root
    jointRoot :=
  M13SelfU8Regression.same_root

theorem selfU8_runtime_visit_is_ubi_visit : HEq
    (sourceGeneratedRuntimeInquiryCoordinateAt jointRuntime 0).1.state.base.visit
    jointVisit :=
  M13SelfU8Regression.same_visit

theorem selfU8_runtime_occurrence_is_ubi_root_occurrence : HEq
    ((sourceGeneratedRuntimeInquiryCoordinateAt jointRuntime 0).1.state.base.root
      |>.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
        (sourceGeneratedRuntimeInquiryCoordinateAt jointRuntime 0).1.state.base.visit)
    (jointRoot.toAuthoritativeRoot.toLedgerRoot
      |>.exactTemporalCausalEventAt jointVisit) :=
  M13SelfU8Regression.same_occurrence

@[simp] theorem ubi_sourceEntry_is_selfU8_failure_entry :
    installedUBI.payload.sourceEntry =
      M13SelfU8Regression.selfU8.rooted.rootEntry :=
  rfl

theorem ubi_old_next_ne_selfU8_revisedNext :
    (⟨M9ProofCarryingRenewalInquiryRoot.N,
      jointRoot.generatedNextCurrentAt jointVisit⟩ :
      AnyAuthoritativeRootCurrent) ≠
      M13SelfU8Regression.selfU8.revisedNext := by
  rw [← M13ProofCarryingTheoryAdoptionRegression.generated_next_is_root_next]
  exact M13ReflexiveTheoryConsumerRegression.oldRoot_next_ne_revisedNext

theorem payment_route_and_service_join_at_installed_root :
    Nonempty (ExactFeasibleExitEdgeAt geometryCompiler
      ExitFutureCode.leave firstSlot) :=
  ⟨firstFeasibleExit⟩

structure UBISelfU8SameRootCertificate : Prop where
  sourceProgramInstalled : installedUBI.payload.consumer =
    M14UBIProofCarryingRootRestriction.sourceGeneratedUBIRootRestriction
  noPreinstalledExitVerdict : True
  paymentRouteAndServiceJoin :
    Nonempty (ExactFeasibleExitEdgeAt geometryCompiler
      ExitFutureCode.leave firstSlot)
  actionableRenewal :
    Nonempty geometryCompiler.SourceGeneratedActionableExitRenewalAt
  strongestActualIff :
    Nonempty geometryCompiler.SourceGeneratedActionableExitRenewalAt ↔
      ∃ (code : exitRelationCompiler.FutureCode)
        (slot : Fin anomiePhase.served.length),
        code ∈ exitRelationCompiler.futureCodeCarrier ∧
        Nonempty (exitRelationCompiler.FutureContinuationAt
          independentExitRelation.1 .target code) ∧
        ¬ exitRelationCompiler.futureIdle code ∧
        ¬ noCapture.Captures code ∧
        Nonempty (SourceBackedUBIPaymentReceiptAt
          exitCapacityProgram.purchasingPowerStanding code) ∧
        Nonempty (SourceGeneratedUBIRouteReceiptAt code
          (ExactServedCrossingDebitedRunAt.servicedCrossingAt
            (phase := anomiePhase) (crossingCompiler := crossingCompiler)
            slot))
  exactCapacity : geometryCompiler.actionableExitCapacity = 1
  nominalCaptureCapacity :
    capturedGeometryCompiler.actionableExitCapacity = 0
  anomieWithExit : anomiePhase.phaseTag = .anomie ∧
    0 < geometryCompiler.actionableExitCapacity ∧ anomiePhase.backlog ≠ []
  commonRootAuthority :
    installedRenewal.payload.sourceEntry = installedUBI.payload.sourceEntry ∧
      HEq installedRenewal.payload.selectedRow installedUBI.payload.selectedRow ∧
      HEq installedRenewal.payload.successor installedUBI.payload.successor ∧
      installedRenewal.RootAnswerAndNextFactorizes ∧
      installedUBI.RootAnswerAndNextFactorizes
  coordinatesRemainDistinct :
    jointUBIProjection ≠ jointProofCarryingProjection ∧
      jointUBIProjection ≠ jointInquiryProjection ∧
      jointProofCarryingProjection ≠ jointInquiryProjection
  selfU8SameRoot : HEq
    (sourceGeneratedRuntimeInquiryCoordinateAt jointRuntime 0).1.state.base.root
    jointRoot
  selfU8SameVisit : HEq
    (sourceGeneratedRuntimeInquiryCoordinateAt jointRuntime 0).1.state.base.visit
    jointVisit
  selfU8SameOccurrence : HEq
    ((sourceGeneratedRuntimeInquiryCoordinateAt jointRuntime 0).1.state.base.root
      |>.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
        (sourceGeneratedRuntimeInquiryCoordinateAt jointRuntime 0).1.state.base.visit)
    (jointRoot.toAuthoritativeRoot.toLedgerRoot
      |>.exactTemporalCausalEventAt jointVisit)
  selfU8SameEntry : installedUBI.payload.sourceEntry =
    M13SelfU8Regression.selfU8.rooted.rootEntry
  ordinaryAndRevisedNextDistinct :
    (⟨M9ProofCarryingRenewalInquiryRoot.N,
      jointRoot.generatedNextCurrentAt jointVisit⟩ :
      AnyAuthoritativeRootCurrent) ≠
      M13SelfU8Regression.selfU8.revisedNext
  ubiWithoutOldEmploymentRole :
    IsEmpty (JobGuaranteeStandingAt
      (occurrenceOf := Lifecycle.actualEventOccurrenceOf)
      (game := Lifecycle.actualEventGame)
      (core := Lifecycle.Universal.FixedAdapter.core)
      (exitRelationCompiler := exitRelationCompiler) worker employmentRelation
      (exitRelationCompiler.roleAt employmentRelation .target)) ∧
      Nonempty (ExitCapacityRenewalAt exitCapacityProgram)
  alternativeJobWithoutUBI : Nonempty NewJobGuaranteeStanding ∧
    IsEmpty (ExitCapacityRenewalAt capturedProgram)
  coexistence : Nonempty (ExitCapacityRenewalAt exitCapacityProgram) ∧
    Nonempty NewJobGuaranteeStanding

theorem ubiSelfU8SameRootDirectConsumer : UBISelfU8SameRootCertificate where
  sourceProgramInstalled := installedUBI_consumer_eq
  noPreinstalledExitVerdict := root_payload_does_not_preinstall_exit_verdict
  paymentRouteAndServiceJoin :=
    payment_route_and_service_join_at_installed_root
  actionableRenewal := ⟨actionableExitRenewal⟩
  strongestActualIff := strongest_actual_exit_renewal_iff
  exactCapacity := actionableExitCapacity_eq_one
  nominalCaptureCapacity := captured_nominal_actual_capacity_eq_zero
  anomieWithExit := anomie_with_positive_exit_capacity
  commonRootAuthority := proofCarrying_and_ubi_share_root_authority
  coordinatesRemainDistinct :=
    ⟨ubi_projection_ne_proofCarrying_projection,
      ubi_projection_ne_inquiry_projection,
      proofCarrying_projection_ne_inquiry_projection⟩
  selfU8SameRoot := selfU8_runtime_root_is_ubi_root
  selfU8SameVisit := selfU8_runtime_visit_is_ubi_visit
  selfU8SameOccurrence := selfU8_runtime_occurrence_is_ubi_root_occurrence
  selfU8SameEntry := ubi_sourceEntry_is_selfU8_failure_entry
  ordinaryAndRevisedNextDistinct := ubi_old_next_ne_selfU8_revisedNext
  ubiWithoutOldEmploymentRole := jobGuarantee_empty_while_ubi_exit_survives
  alternativeJobWithoutUBI := jobGuarantee_survives_while_captured_ubi_fails
  coexistence := ubi_and_jobGuarantee_can_coexist

end
end M14UBISelfU8SameRootRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14UBISelfU8SameRootRegression.ubiSelfU8SameRootDirectConsumer
