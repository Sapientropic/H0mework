import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.CrossCompiler.Readout.Recognition.Admission.Material.Consumer.ProofCarryingPlatformGateMaterialFulfillment

/-!
# Full proof-carrying platform-gate admission

The revised law gate, paid U8 authority, affected bearer, both inherited paid
channels and the renewed actual material service are assembled here.  The
old Payment and the later material action retain their own generated next;
their genuinely different occurrences are not identified.  Full admission
means every authority and material obligation is consumed, not that two roots
or two temporal successors are collapsed.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingPlatformGateFullAdmission

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Exchange Settlement Price Money UBI
open Renewal
open M14EssentialAccessRelationFixture
open M14EssentialAccessSectorRegression
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityEssentialAccessChannel
open M14SourceGeneratedPlatformChannelRevisionCandidate
open M14SourceGeneratedCycleMemoryPlatformGateU8
open M14SourceGeneratedPlatformGateAffectedBearerIncidence
open M14ProofCarryingPlatformGateOldPaidChannelTransport
open M14SourceGeneratedPlatformGateTwoSlotMaterialNoGo
open M14ProofCarryingPlatformGateAdmissionMaterialObligation
open M14SourceGeneratedPlatformGateRenewedActualService
open M14ProofCarryingPlatformGateMaterialFulfillment

structure ProofCarryingPlatformGateFullAdmissionAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) : Type 14 where
  materialFulfillment :
    ProofCarryingPlatformGateMaterialFulfillmentAt oldVisit sourceIndex
      boundary
  revisedGate : RevisedPaidEssentialAccessChannelAt
    materialFulfillment.materialService.gateIncidence.candidate.obstruction
  revisedGateExact : revisedGate =
    .inr materialFulfillment.materialService.gateIncidence.gate
  gateSeedPlatform : revisedChannelSeed
      (obstruction :=
        materialFulfillment.materialService.gateIncidence.candidate.obstruction)
      revisedGate = exactEssentialAccessSeed .platform
  gateHasNoOldRepresentation : IsEmpty
    { channel : EssentialAccessChannel //
      channelSeed channel = revisedChannelSeed
        (obstruction :=
          materialFulfillment.materialService.gateIncidence.candidate.obstruction)
        revisedGate }
  tenurePaidTransport :
    type_of% (platformGateOldPaidChannelTransport_directConsumer oldVisit
      sourceIndex boundary tenureAuthority)
  healthPaidTransport :
    type_of% (platformGateOldPaidChannelTransport_directConsumer oldVisit
      sourceIndex boundary healthAuthority)
  oldPaidTransportsSameNext :
    type_of% (platformGateTenureHealthPaidTransports_sameNext oldVisit
      sourceIndex boundary)
  gateBearerGenerated :
    materialFulfillment.materialService.materialBearer =
      materialFulfillment.materialService.gateIncidence.affectedBearer
  serviceObligationMatchesGateSource :
    materialFulfillment.materialService.obligation.bearer =
      materialFulfillment.materialService.gateIncidence.sourceObligation.bearer
  targetRoleGenerated :
    materialFulfillment.materialService.gateIncidence.gate.targetRole =
      EssentialAccessRole.platformProvider
  actualMaterialService : Nonempty
    (NativeDebitedRun platformGateMaterialServiceProcess
      (platformGateMaterialDebitProcessAt boundary) .debt
      (platformGateMaterialServiceRunAt boundary))
  materialFulfilled :
    ∃ archive : TerminalArchive Lifecycle.LifecycleVocabulary,
      materialFulfillment.materialService.fulfillment.target.slots[
          (platformGateMaterialPostServiceSlotAt boundary).val]? =
        some (.terminal archive)
  materialNoReopen :
    ∀ archive : TerminalArchive Lifecycle.LifecycleVocabulary,
      IsEmpty (platformGateMaterialServiceProcess.ReopenEvent archive)
  materialCannotDisplaceOldSlots : IsEmpty
    (RenewedPlatformMaterialServiceAt oldVisit sourceIndex boundary →
      ExistingTwoSlotPlatformMaterialAdmissionAt oldVisit sourceIndex
        boundary)
  independentPaidConsumer : Nonempty
    (RenewalResponsibilityConsumerAt
      (platformGateInstalledRenewalAt oldVisit sourceIndex boundary
        ).operationalAuthority)
  paidRuntimeNext :
    ((platformGateRuntimeAt oldVisit sourceIndex boundary).stateAt 1
      ).engine.node.erase =
      (platformGateFirstTickAt oldVisit sourceIndex boundary).next.node.erase
  materialActionNext :
    materialFulfillment.materialService.generatedNext =
      ⟨materialFulfillment.materialService.sourceAction.target.TargetV,
        materialFulfillment.materialService.sourceAction.target.targetRoot.toAuthoritativeRoot,
        materialFulfillment.materialService.sourceAction.target.targetVisit⟩

def proofCarryingPlatformGateFullAdmission
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ProofCarryingPlatformGateFullAdmissionAt oldVisit sourceIndex boundary := by
  let materialFulfillment :=
    proofCarryingPlatformGateMaterialFulfillment oldVisit sourceIndex boundary
  let incidence := materialFulfillment.materialService.gateIncidence
  let revisedGate : RevisedPaidEssentialAccessChannelAt
      incidence.candidate.obstruction :=
    .inr incidence.gate
  exact
    { materialFulfillment := materialFulfillment
      revisedGate := revisedGate
      revisedGateExact := rfl
      gateSeedPlatform := incidence.gate.seed_eq_platform
      gateHasNoOldRepresentation :=
        revisedChannel_newSeed_hasNoOldRepresentation incidence.gate
      tenurePaidTransport :=
        materialFulfillment.admittedObligation.tenurePaidTransport
      healthPaidTransport :=
        materialFulfillment.admittedObligation.healthPaidTransport
      oldPaidTransportsSameNext :=
        materialFulfillment.admittedObligation.oldPaidTransportsSameNext
      gateBearerGenerated :=
        materialFulfillment.serviceBearerMatchesGate
      serviceObligationMatchesGateSource :=
        materialFulfillment.serviceObligationMatchesGateSource
      targetRoleGenerated := incidence.targetRoleGenerated
      actualMaterialService := materialFulfillment.actualDebitedService
      materialFulfilled := materialFulfillment.fulfilled
      materialNoReopen := materialFulfillment.noReopen
      materialCannotDisplaceOldSlots :=
        materialFulfillment.noCollapseIntoOldTwoSlot
      independentPaidConsumer :=
        ⟨incidence.independentPaidConsumer⟩
      paidRuntimeNext :=
        materialFulfillment.admittedObligation.paidRuntimeGeneratesNext
      materialActionNext := materialFulfillment.generatedNext }

theorem platformGateFullAdmission_directConsumer
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    let admission := proofCarryingPlatformGateFullAdmission oldVisit
      sourceIndex boundary
    Nonempty (ProofCarryingPlatformGateFullAdmissionAt oldVisit sourceIndex
        boundary) ∧
      revisedChannelSeed
          (obstruction :=
            admission.materialFulfillment.materialService.gateIncidence.candidate.obstruction)
          admission.revisedGate = exactEssentialAccessSeed .platform ∧
      IsEmpty { channel : EssentialAccessChannel //
        channelSeed channel = revisedChannelSeed
          (obstruction :=
            admission.materialFulfillment.materialService.gateIncidence.candidate.obstruction)
          admission.revisedGate } ∧
      type_of% (platformGateTenureHealthPaidTransports_sameNext oldVisit
        sourceIndex boundary) ∧
      admission.materialFulfillment.materialService.obligation.bearer =
        admission.materialFulfillment.materialService.gateIncidence.sourceObligation.bearer ∧
      Nonempty (NativeDebitedRun platformGateMaterialServiceProcess
        (platformGateMaterialDebitProcessAt boundary) .debt
        (platformGateMaterialServiceRunAt boundary)) ∧
      (∀ archive : TerminalArchive Lifecycle.LifecycleVocabulary,
        IsEmpty
          (platformGateMaterialServiceProcess.ReopenEvent archive)) ∧
      IsEmpty (RenewedPlatformMaterialServiceAt oldVisit sourceIndex
          boundary →
        ExistingTwoSlotPlatformMaterialAdmissionAt oldVisit sourceIndex
          boundary) ∧
      Nonempty (RenewalResponsibilityConsumerAt
        (platformGateInstalledRenewalAt oldVisit sourceIndex boundary
          ).operationalAuthority) ∧
      ((platformGateRuntimeAt oldVisit sourceIndex boundary).stateAt 1
        ).engine.node.erase =
        (platformGateFirstTickAt oldVisit sourceIndex boundary).next.node.erase ∧
      admission.materialFulfillment.materialService.generatedNext =
        ⟨admission.materialFulfillment.materialService.sourceAction.target.TargetV,
          admission.materialFulfillment.materialService.sourceAction.target.targetRoot.toAuthoritativeRoot,
          admission.materialFulfillment.materialService.sourceAction.target.targetVisit⟩ := by
  dsimp
  let admission := proofCarryingPlatformGateFullAdmission oldVisit
    sourceIndex boundary
  exact ⟨⟨admission⟩,
    admission.gateSeedPlatform,
    admission.gateHasNoOldRepresentation,
    admission.oldPaidTransportsSameNext,
    admission.serviceObligationMatchesGateSource,
    admission.actualMaterialService,
    admission.materialNoReopen,
    admission.materialCannotDisplaceOldSlots,
    admission.independentPaidConsumer,
    admission.paidRuntimeNext,
    admission.materialActionNext⟩

end
end M14ProofCarryingPlatformGateFullAdmission
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPlatformGateFullAdmission.proofCarryingPlatformGateFullAdmission
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPlatformGateFullAdmission.platformGateFullAdmission_directConsumer
