import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.CrossCompiler.Readout.Recognition.Admission.Consumer.ProofCarryingPlatformGateAdmissionMaterialObligation
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.CrossCompiler.Readout.Recognition.Admission.Material.Source.SourceGeneratedPlatformGateRenewedActualService

/-!
# Proof-carrying fulfillment of the platform material obligation

The old two-slot Payment remains exactly full.  The missing material is paid
by the next same-lineage platform occurrence instead: a distinct actual action
with the same relation seed and bearer generates a one-unit maintenance debit,
fulfilled lifecycle disposition, whole action receipt and next.  The negative
old fibre is retained as the non-displacement boundary rather than erased.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingPlatformGateMaterialFulfillment

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Exchange
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedCrossCompilerRelationAppendUBI
open M14SourceGeneratedSequentialCrossCompilerRelationAppend
open M14SourceGeneratedCrossCompilerRelationAppendPresentation
open M14SourceGeneratedPlatformGateAffectedBearerIncidence
open M14SourceGeneratedPlatformGateTwoSlotMaterialNoGo
open M14ProofCarryingPlatformGateAdmissionMaterialObligation
open M14SourceGeneratedPlatformGateRenewedActualService

abbrev RenewedPlatformMaterialServiceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  SourceGeneratedPlatformGateRenewedActualServiceAt oldVisit sourceIndex
    boundary

structure ProofCarryingPlatformGateMaterialFulfillmentAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) : Type 12 where
  admittedObligation :
    ProofCarryingPlatformGateAdmissionMaterialObligationAt oldVisit
      sourceIndex boundary
  materialService :
    RenewedPlatformMaterialServiceAt oldVisit sourceIndex boundary
  renewedOccurrenceDistinct :
    (crossCompilerActionPresentationAt
        (platformGateMaterialDepthAt boundary)).erase ≠
      (crossCompilerActionPresentationAt
        (platformGateAffectedBearerDepthAt boundary)).erase
  serviceSeedMatchesGate :
    materialService.materialSeed = materialService.gateIncidence.gate.seed
  serviceBearerMatchesGate :
    materialService.materialBearer =
      materialService.gateIncidence.affectedBearer
  serviceObligationMatchesGateSource :
    materialService.obligation.bearer =
      materialService.gateIncidence.sourceObligation.bearer
  actualDebitedService : Nonempty
    (NativeDebitedRun platformGateMaterialServiceProcess
      (platformGateMaterialDebitProcessAt boundary) .debt
      (platformGateMaterialServiceRunAt boundary))
  serviceSourceOwned : Nonempty
    (SourceOwnsResponsibilityIncidence Lifecycle.LifecycleVocabulary .after
      materialService.obligation)
  serviceBudgetSpent :
    platformGateMaterialBudgetAt
        (platformGateMaterialServiceSourceStateAt boundary) .debt = 1 ∧
      platformGateMaterialBudgetAt
        (platformGateMaterialPostServiceStateAt boundary) .debt = 0 ∧
      (platformGateMaterialServiceRunAt boundary).events.length = 1
  fulfilled :
    ∃ archive : TerminalArchive Lifecycle.LifecycleVocabulary,
      materialService.fulfillment.target.slots[
          (platformGateMaterialPostServiceSlotAt boundary).val]? =
        some (.terminal archive)
  noReopen : ∀ archive : TerminalArchive Lifecycle.LifecycleVocabulary,
    IsEmpty (platformGateMaterialServiceProcess.ReopenEvent archive)
  oldTwoSlotFibreRemainsEmpty :
    IsEmpty (ExistingTwoSlotPlatformMaterialAdmissionAt oldVisit sourceIndex
      boundary)
  noCollapseIntoOldTwoSlot : IsEmpty
    (RenewedPlatformMaterialServiceAt oldVisit sourceIndex boundary →
      ExistingTwoSlotPlatformMaterialAdmissionAt oldVisit sourceIndex
        boundary)
  inheritedUBI : type_of% (crossCompilerUBI_directConsumer
    (platformGateMaterialDepthAt boundary))
  wholeActionReceipt : type_of%
    (generatedCrossCompilerRelationAppendAction_directConsumer
      (platformGateMaterialDepthAt boundary))
  generatedNext : materialService.generatedNext =
    ⟨materialService.sourceAction.target.TargetV,
      materialService.sourceAction.target.targetRoot.toAuthoritativeRoot,
      materialService.sourceAction.target.targetVisit⟩

def proofCarryingPlatformGateMaterialFulfillment
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ProofCarryingPlatformGateMaterialFulfillmentAt oldVisit sourceIndex
      boundary := by
  let admittedObligation :=
    proofCarryingPlatformGateAdmissionMaterialObligation oldVisit sourceIndex
      boundary
  let materialService :=
    sourceGeneratedPlatformGateRenewedActualServiceAt oldVisit sourceIndex
      boundary
  let oldEmpty :=
    existingTwoSlotPlatformMaterialAdmission_isEmpty oldVisit sourceIndex
      boundary
  exact
    { admittedObligation := admittedObligation
      materialService := materialService
      renewedOccurrenceDistinct :=
        materialService.occurrenceDistinctFromGate
      serviceSeedMatchesGate := materialService.materialSeedEqGateSeed
      serviceBearerMatchesGate :=
        materialService.materialBearerEqAffectedBearer
      serviceObligationMatchesGateSource :=
        materialService.obligationBearerEqAffectedBearer.trans
          materialService.gateIncidence.obligationBearerExact.symm
      actualDebitedService := ⟨materialService.debitedService⟩
      serviceSourceOwned := ⟨materialService.serviceSourceOwned⟩
      serviceBudgetSpent :=
        ⟨platformGateMaterial_sourceBudget_eq_one boundary,
          platformGateMaterial_targetBudget_eq_zero boundary,
          platformGateMaterialServiceRun_events_length boundary⟩
      fulfilled := materialService.fulfillmentTerminal
      noReopen := platformGateMaterialFulfillment_hasNoReopen
      oldTwoSlotFibreRemainsEmpty := oldEmpty
      noCollapseIntoOldTwoSlot :=
        ⟨fun collapse => oldEmpty.false (collapse materialService)⟩
      inheritedUBI := crossCompilerUBI_directConsumer _
      wholeActionReceipt :=
        generatedCrossCompilerRelationAppendAction_directConsumer _
      generatedNext := materialService.generatedNextExact }

theorem platformGateMaterialFulfillment_directConsumer
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    let fulfillment := proofCarryingPlatformGateMaterialFulfillment oldVisit
      sourceIndex boundary
    Nonempty (ProofCarryingPlatformGateMaterialFulfillmentAt oldVisit
        sourceIndex boundary) ∧
      fulfillment.materialService.obligation.bearer =
        fulfillment.materialService.gateIncidence.sourceObligation.bearer ∧
      Nonempty (NativeDebitedRun platformGateMaterialServiceProcess
        (platformGateMaterialDebitProcessAt boundary) .debt
        (platformGateMaterialServiceRunAt boundary)) ∧
      platformGateMaterialBudgetAt
          (platformGateMaterialServiceSourceStateAt boundary) .debt = 1 ∧
      platformGateMaterialBudgetAt
          (platformGateMaterialPostServiceStateAt boundary) .debt = 0 ∧
      (∀ archive : TerminalArchive Lifecycle.LifecycleVocabulary,
        IsEmpty
          (platformGateMaterialServiceProcess.ReopenEvent archive)) ∧
      IsEmpty (ExistingTwoSlotPlatformMaterialAdmissionAt oldVisit
        sourceIndex boundary) ∧
      IsEmpty (RenewedPlatformMaterialServiceAt oldVisit sourceIndex
          boundary →
        ExistingTwoSlotPlatformMaterialAdmissionAt oldVisit sourceIndex
          boundary) ∧
      type_of% (generatedCrossCompilerRelationAppendAction_directConsumer
        (platformGateMaterialDepthAt boundary)) ∧
      fulfillment.materialService.generatedNext =
        ⟨fulfillment.materialService.sourceAction.target.TargetV,
          fulfillment.materialService.sourceAction.target.targetRoot.toAuthoritativeRoot,
          fulfillment.materialService.sourceAction.target.targetVisit⟩ := by
  dsimp
  let fulfillment := proofCarryingPlatformGateMaterialFulfillment oldVisit
    sourceIndex boundary
  exact ⟨⟨fulfillment⟩,
    fulfillment.serviceObligationMatchesGateSource,
    fulfillment.actualDebitedService,
    fulfillment.serviceBudgetSpent.1,
    fulfillment.serviceBudgetSpent.2.1,
    fulfillment.noReopen,
    fulfillment.oldTwoSlotFibreRemainsEmpty,
    fulfillment.noCollapseIntoOldTwoSlot,
    fulfillment.wholeActionReceipt,
    fulfillment.generatedNext⟩

end
end M14ProofCarryingPlatformGateMaterialFulfillment
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPlatformGateMaterialFulfillment.proofCarryingPlatformGateMaterialFulfillment
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPlatformGateMaterialFulfillment.platformGateMaterialFulfillment_directConsumer
