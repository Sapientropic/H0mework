import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.CrossCompiler.Readout.Recognition.Admission.Material.NoGo.SourceGeneratedPlatformGateTwoSlotMaterialNoGo

/-!
# Platform gate admission with honest material obligation

The new authority face now has its relation-generated affected bearer and
source obligation.  Both old paid channels retain their complete operational
carriers at the same right Payment and commute to one actual next.  The
existing two-slot settlement has no third non-displacing platform slot, so
the certificate records that exact material obligation instead of pretending
that U8 created service capacity.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingPlatformGateAdmissionMaterialObligation

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Exchange Settlement Price Money UBI
open Renewal Capacity Space CrossingCost
open M14EssentialAccessRelationFixture
open M14EssentialAccessSectorRegression
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedPostSettlementObserverSubmissionU8
open M14SourceGeneratedPlatformChannelRevisionCandidate
open M14SourceGeneratedCycleMemoryPlatformGateU8
open M14SourceGeneratedPlatformGateAffectedBearerIncidence
open M14ProofCarryingPlatformGateOldPaidChannelTransport
open M14SourceGeneratedPlatformGateTwoSlotMaterialNoGo

structure ProofCarryingPlatformGateAdmissionMaterialObligationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) : Prop where
  paidAuthorityFace :
    ProofCarryingCycleMemoryPlatformGateActualPaidU8UpdateAt oldVisit
      sourceIndex boundary
  affectedBearerIncidence :
    type_of% (platformGateAffectedBearerIncidence_directConsumer oldVisit
      sourceIndex boundary)
  tenurePaidTransport :
    type_of% (platformGateOldPaidChannelTransport_directConsumer oldVisit
      sourceIndex boundary tenureAuthority)
  healthPaidTransport :
    type_of% (platformGateOldPaidChannelTransport_directConsumer oldVisit
      sourceIndex boundary healthAuthority)
  oldPaidTransportsSameNext :
    type_of% (platformGateTenureHealthPaidTransports_sameNext oldVisit
      sourceIndex boundary)
  existingMaterialCannotDisplaceOldGates :
    IsEmpty (ExistingTwoSlotPlatformMaterialAdmissionAt oldVisit sourceIndex
      boundary)
  newGateSeedPlatform :
    let incidence := sourceGeneratedPlatformGateAffectedBearerIncidenceAt
      oldVisit sourceIndex boundary
    incidence.gate.seed = exactEssentialAccessSeed .platform
  newGateBearerFromRelationActor :
    let incidence := sourceGeneratedPlatformGateAffectedBearerIncidenceAt
      oldVisit sourceIndex boundary
    incidence.affectedBearer =
      M3FiniteExchangeFixture.exchangeLaw.bearerOfActor incidence.gate.actor
  newGateObligationBorne :
    let incidence := sourceGeneratedPlatformGateAffectedBearerIncidenceAt
      oldVisit sourceIndex boundary
    incidence.sourceObligation.bearer = incidence.affectedBearer
  newGateTargetRoleGenerated :
    let incidence := sourceGeneratedPlatformGateAffectedBearerIncidenceAt
      oldVisit sourceIndex boundary
    incidence.gate.targetRole = EssentialAccessRole.platformProvider
  paidRuntimeGeneratesNext :
    ((platformGateRuntimeAt oldVisit sourceIndex boundary).stateAt 1
      ).engine.node.erase =
      (platformGateFirstTickAt oldVisit sourceIndex boundary).next.node.erase

theorem proofCarryingPlatformGateAdmissionMaterialObligation
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ProofCarryingPlatformGateAdmissionMaterialObligationAt oldVisit
      sourceIndex boundary where
  paidAuthorityFace :=
    proofCarryingCycleMemoryPlatformGateActualPaidU8Update oldVisit
      sourceIndex boundary
  affectedBearerIncidence :=
    platformGateAffectedBearerIncidence_directConsumer oldVisit sourceIndex
      boundary
  tenurePaidTransport :=
    platformGateOldPaidChannelTransport_directConsumer oldVisit sourceIndex
      boundary tenureAuthority
  healthPaidTransport :=
    platformGateOldPaidChannelTransport_directConsumer oldVisit sourceIndex
      boundary healthAuthority
  oldPaidTransportsSameNext :=
    platformGateTenureHealthPaidTransports_sameNext oldVisit sourceIndex
      boundary
  existingMaterialCannotDisplaceOldGates :=
    existingTwoSlotPlatformMaterialAdmission_isEmpty oldVisit sourceIndex
      boundary
  newGateSeedPlatform :=
    (sourceGeneratedPlatformGateAffectedBearerIncidenceAt oldVisit sourceIndex
      boundary).gate.seed_eq_platform
  newGateBearerFromRelationActor :=
    (sourceGeneratedPlatformGateAffectedBearerIncidenceAt oldVisit sourceIndex
      boundary).affectedBearerFromGateActor
  newGateObligationBorne :=
    (sourceGeneratedPlatformGateAffectedBearerIncidenceAt oldVisit sourceIndex
      boundary).obligationBearerExact
  newGateTargetRoleGenerated :=
    (sourceGeneratedPlatformGateAffectedBearerIncidenceAt oldVisit sourceIndex
      boundary).targetRoleGenerated
  paidRuntimeGeneratesNext :=
    platformGateFirstTick_next_is_revisedTarget oldVisit sourceIndex boundary

theorem platformGateAdmissionMaterialObligation_directConsumer
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    Nonempty (ProofCarryingPlatformGateAdmissionMaterialObligationAt oldVisit
        sourceIndex boundary) ∧
      type_of% (platformGateAffectedBearerIncidence_directConsumer oldVisit
        sourceIndex boundary) ∧
      type_of% (platformGateOldPaidChannelTransport_directConsumer oldVisit
        sourceIndex boundary tenureAuthority) ∧
      type_of% (platformGateOldPaidChannelTransport_directConsumer oldVisit
        sourceIndex boundary healthAuthority) ∧
      IsEmpty (ExistingTwoSlotPlatformMaterialAdmissionAt oldVisit sourceIndex
        boundary) ∧
      ((platformGateRuntimeAt oldVisit sourceIndex boundary).stateAt 1
        ).engine.node.erase =
        (platformGateFirstTickAt oldVisit sourceIndex boundary).next.node.erase :=
  ⟨⟨proofCarryingPlatformGateAdmissionMaterialObligation oldVisit
      sourceIndex boundary⟩,
    platformGateAffectedBearerIncidence_directConsumer oldVisit sourceIndex
      boundary,
    platformGateOldPaidChannelTransport_directConsumer oldVisit sourceIndex
      boundary tenureAuthority,
    platformGateOldPaidChannelTransport_directConsumer oldVisit sourceIndex
      boundary healthAuthority,
    existingTwoSlotPlatformMaterialAdmission_isEmpty oldVisit sourceIndex
      boundary,
    platformGateFirstTick_next_is_revisedTarget oldVisit sourceIndex boundary⟩

end
end M14ProofCarryingPlatformGateAdmissionMaterialObligation
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPlatformGateAdmissionMaterialObligation.proofCarryingPlatformGateAdmissionMaterialObligation
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPlatformGateAdmissionMaterialObligation.platformGateAdmissionMaterialObligation_directConsumer
