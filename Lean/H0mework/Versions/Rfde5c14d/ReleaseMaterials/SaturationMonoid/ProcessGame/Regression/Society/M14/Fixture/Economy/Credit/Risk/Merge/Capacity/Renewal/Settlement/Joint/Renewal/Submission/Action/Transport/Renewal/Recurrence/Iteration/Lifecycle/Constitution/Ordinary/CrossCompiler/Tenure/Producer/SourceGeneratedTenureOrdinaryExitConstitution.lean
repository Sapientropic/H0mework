import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccessPaymentPurposeLaw
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Producer.SourceGeneratedCanonicalSocietyCofinalReadout

/-!
# Source-generated tenure ordinary exit Constitution

Tenure is the first genuine nonemployment critical relation.  Its exact M1
occurrence now generates a tenure controller, `ActionPowerOverAt`, actionable
source continuation and target loss through the existing essential-access
relation compiler.  It is never retyped as a birth-bearer employment relation.

The critical actor and canonical UBI exit worker are aligned only in the
existing `Lifecycle.ActorBearer` codomain, through the source-generated tenure
payment-purpose counterparty.  The outside-option renewal/code/slot/Payment/
route/service material is read directly from the same finite Constitution in
the canonical root-law pulse.  No parallel ordinary program is constructed.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedTenureOrdinaryExitConstitution

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer Renewal UniversalRootGrammar
open Lifecycle Universal Relations Power Exchange Settlement Price Money UBI
open Capacity Space CrossingCost
open Lifecycle.Universal.FixedAdapter
open M3FiniteExchangeFixture M3ExchangeSettlementPriceRegression
open M8MoneyRootInstallationRegression M8PurchasingPowerStandingRegression
open M10OccurrenceCapacityDebitedRunFixture
open M14UBIPeriodicActualServiceCapacity
open M14UBIExitCapacityFixture M14EssentialAccessRelationFixture
open M14EssentialAccessPaymentPurposeLaw
open M14SourceGeneratedLossAllocationMaterial
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityBirthBearerExit
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitch
open M14SourceGeneratedPostSettlementObserverFiniteExitCapacityConstitution
open M14SourceGeneratedCycleCanonicalRootLawStep
open M14SourceGeneratedCanonicalSocietyCofinalReadout
open M14SourceGeneratedUniversalSocietyRootGrammar

/-! ## Source-generated common-bearer alignment -/

/-- The critical and exit actors remain different relation-generated values.
The only bridge is their exact source-generated bearer readout. -/
structure SourceGeneratedTenurePaymentExitBearerAlignment : Type 32 where
  private mk ::
  tenureLoss : SourceGeneratedEmploymentLossAt
    (occurrenceOf := Lifecycle.actualEventOccurrenceOf)
    (game := Lifecycle.actualEventGame)
    (core := Lifecycle.Universal.FixedAdapter.core)
    (controllerFace := Lifecycle.Universal.FixedAdapter.targetFace)
    (exitRelationCompiler := essentialAccessRelationCompiler)
    (employmentController := essentialAccessExitController)
    tenureExitControllerActor tenureActor tenureRelation
  tenureLossExact : tenureLoss = tenureRelationLoss
  exactPaymentPurpose : ExactTenurePaymentPurposeAt
  exactPaymentPurposeExact : exactPaymentPurpose = exactTenurePaymentPurpose
  tenureBearerExact : exchangeLaw.bearerOfActor tenureActor =
    sourceGeneratedLossAllocationMaterial.parentBearer
  exitWorkerBearerExact : exchangeLaw.bearerOfActor birthBearerWorker =
    sourceGeneratedLossAllocationMaterial.parentBearer
  commonBearerExact : exchangeLaw.bearerOfActor tenureActor =
    exchangeLaw.bearerOfActor birthBearerWorker

/-- Premise-free alignment producer.  No actor equality, compiler, relation,
Payment or bearer equation is accepted from the caller. -/
def sourceGeneratedTenurePaymentExitBearerAlignment :
    SourceGeneratedTenurePaymentExitBearerAlignment := by
  have tenureBearer : exchangeLaw.bearerOfActor tenureActor =
      sourceGeneratedLossAllocationMaterial.parentBearer := by
    rw [tenure_actor_is_exact_payment_counterparty]
    rfl
  exact
    { tenureLoss := tenureRelationLoss
      tenureLossExact := rfl
      exactPaymentPurpose := exactTenurePaymentPurpose
      exactPaymentPurposeExact := rfl
      tenureBearerExact := tenureBearer
      exitWorkerBearerExact := birthBearerWorker_bearer_exact
      commonBearerExact :=
        tenureBearer.trans birthBearerWorker_bearer_exact.symm }

/-! ## Existing root restrictions -/

abbrev TenureActualPassedAuditAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :=
  SourceGeneratedPassedDependentFaceAuditAt
    (universalSocietyRecognitionAt oldVisit sourceIndex)
    (universalSocietyVisitAt oldVisit sourceIndex
      (cycleCanonicalRootLawIndex initial depth)) .actual

/-- Root-controlled operational incidence, definitionally identical to the
finite Constitution's semantic incidence type. -/
abbrev RootControlledTenureOrdinaryExitIncidenceAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) : Prop :=
  ∃ semanticRenewal : ExitCapacityRenewalAt birthBearerExitCapacityProgram,
    ∃ code : birthBearerExitRelationCompiler.FutureCode,
      ∃ slot : Fin
          (anomiePhaseAt
            (cycleExitCapacityDepthAt initial depth)).served.length,
        semanticRenewal.exit.1 = code ∧
          ExitCapacitySemanticMaterialAt initial depth code slot ∧
          ExitCapacityTemporalMaterialAt initial depth code

theorem rootControlledTenureOrdinaryExitIncidenceAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary)
    (observerFuel depth : Nat) :
    RootControlledTenureOrdinaryExitIncidenceAt initial depth :=
  (exactCanonicalSocietyRenewalPulseAt initial observerFuel depth
    ).rootLawTransition.sourceConstitution.semanticRenewalIncidence

/-! ## Tenure ordinary exit Constitution -/

structure TenureOrdinaryExitConstitutionAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary)
    (observerFuel depth : Nat) : Type 32 where
  private mk ::
  alignment : SourceGeneratedTenurePaymentExitBearerAlignment
  alignmentExact : alignment =
    sourceGeneratedTenurePaymentExitBearerAlignment
  tenureRelationTrace :
    ∃ seed : essentialAccessRelationCompiler.ExactRelationSeed,
      seed.actor essentialAccessRelationCompiler = tenureActor ∧
      essentialAccessRelationCompiler.relationOf seed = tenureRelation
  tenurePower : ActionPowerOverAt essentialAccessRelationCompiler
    essentialAccessExitController tenureExitControllerActor tenureActor
      tenureRelation
  tenurePowerExact : tenurePower = tenureExitActionPower
  tenureLossExact : tenurePower.freedomChange =
    .lost .tenure (essentialAccessCode_source_actionable .tenure)
      (essentialAccessCode_target_absent .tenure)
  sourceRoleGenerated : essentialAccessRelationCompiler.RelationRoleAt
    tenureActor tenureRelation .source
    (essentialAccessRelationCompiler.roleAt tenureRelation .source)
  targetRoleGenerated : essentialAccessRelationCompiler.RelationRoleAt
    tenureActor tenureRelation .target
    (essentialAccessRelationCompiler.roleAt tenureRelation .target)
  tenureRootPassedAudit : TenureActualPassedAuditAt initial depth
  tenureRootPassedAuditExact : tenureRootPassedAudit =
    universalSocietyActualPassedAuditAt oldVisit sourceIndex
      (cycleCanonicalRootLawIndex initial depth) .essentialAccessTenure
  finiteConstitution : FiniteExitCapacityConstitutionAt initial depth
  finiteConstitutionExact : finiteConstitution =
    (exactCanonicalSocietyRenewalPulseAt initial observerFuel depth
      ).rootLawTransition.sourceConstitution
  rootOperationalIncidence :
    RootControlledTenureOrdinaryExitIncidenceAt initial depth
  fullCaptureNominal : NominalTransferReadoutAt birthBearerCapturedProgram
  fullCaptureRenewalEmpty :
    IsEmpty (ExitCapacityRenewalAt birthBearerCapturedProgram)

/-- Sole producer.  All critical, alignment, root-face and operational data
are source-generated; only the existing cycle indices are arguments. -/
def sourceGeneratedTenureOrdinaryExitConstitutionAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary)
    (observerFuel depth : Nat) :
    TenureOrdinaryExitConstitutionAt initial observerFuel depth :=
  { alignment := sourceGeneratedTenurePaymentExitBearerAlignment
    alignmentExact := rfl
    tenureRelationTrace :=
      ⟨exactEssentialAccessSeed .tenure, rfl, rfl⟩
    tenurePower := tenureExitActionPower
    tenurePowerExact := rfl
    tenureLossExact := rfl
    sourceRoleGenerated := ⟨tenureInterest, rfl⟩
    targetRoleGenerated := ⟨tenureInterest, rfl⟩
    tenureRootPassedAudit :=
      universalSocietyActualPassedAuditAt oldVisit sourceIndex
        (cycleCanonicalRootLawIndex initial depth) .essentialAccessTenure
    tenureRootPassedAuditExact := rfl
    finiteConstitution :=
      (exactCanonicalSocietyRenewalPulseAt initial observerFuel depth
        ).rootLawTransition.sourceConstitution
    finiteConstitutionExact := rfl
    rootOperationalIncidence :=
      rootControlledTenureOrdinaryExitIncidenceAt initial observerFuel depth
    fullCaptureNominal := birthBearerNominalTransfer
    fullCaptureRenewalEmpty :=
      birthBearerNominalTransfer.excludes_exitCapacityRenewal }

theorem tenureOrdinaryExit_exists_everyCycle
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary)
    (observerFuel depth : Nat) :
    Nonempty (TenureOrdinaryExitConstitutionAt initial observerFuel depth) :=
  ⟨sourceGeneratedTenureOrdinaryExitConstitutionAt initial observerFuel depth⟩

end
end M14SourceGeneratedTenureOrdinaryExitConstitution
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedTenureOrdinaryExitConstitution.sourceGeneratedTenurePaymentExitBearerAlignment
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedTenureOrdinaryExitConstitution.rootControlledTenureOrdinaryExitIncidenceAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedTenureOrdinaryExitConstitution.sourceGeneratedTenureOrdinaryExitConstitutionAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedTenureOrdinaryExitConstitution.tenureOrdinaryExit_exists_everyCycle
