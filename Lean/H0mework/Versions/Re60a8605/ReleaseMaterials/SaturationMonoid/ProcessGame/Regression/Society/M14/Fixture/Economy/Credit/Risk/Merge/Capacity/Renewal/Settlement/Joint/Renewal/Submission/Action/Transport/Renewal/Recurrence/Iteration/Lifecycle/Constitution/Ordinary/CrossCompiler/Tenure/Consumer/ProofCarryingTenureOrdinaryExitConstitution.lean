import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.Ordinary.CrossCompiler.Tenure.Producer.SourceGeneratedTenureOrdinaryExitConstitution

/-!
# Proof-carrying tenure ordinary exit Constitution

This consumer opens the source-generated tenure power and the canonical
finite Constitution at the same root-law depth.  Its literal renewal, code,
service slot, Payment, route, services, residual and future material are
eliminated from the stored operational incidence, never from a parallel
ordinary program.

The tenure actor is not identified with the UBI worker.  Their only bridge is
the source-generated common `Lifecycle.ActorBearer`; relation roles still
come from the tenure phase.  Exact-once root coverage, actual/search
same-root authority, whole-ledger/generated-next, self-U8 and compatible
FutureBirth are consumed at the same depth.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingTenureOrdinaryExitConstitution

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer Renewal UniversalRootGrammar
open Lifecycle Universal Relations Power Exchange Settlement Price Money UBI
open Capacity Space CrossingCost
open Lifecycle.Universal.FixedAdapter
open M3FiniteExchangeFixture M3ExchangeSettlementPriceRegression
open M10OccurrenceCapacityDebitedRunFixture
open M14UBIPeriodicActualServiceCapacity
open M14UBIExitCapacityFixture M14EssentialAccessRelationFixture
open M14UBIProofCarryingRootRestriction
open M14EssentialAccessPaymentPurposeLaw
open M14SourceGeneratedLossAllocationMaterial
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityBirthBearerExit
open M14SourceGeneratedPostSettlementSocietyFaceTrace
open M14SourceGeneratedPostSettlementObserverFiniteExitCapacityConstitution
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitch
open M14SourceGeneratedPaidExitLifecycleTemporalSpine
open M14SourceGeneratedCycleCanonicalRootLawStep
open M14ProofCarryingFiniteCycleCanonicalRootLaw
open M14SourceGeneratedCanonicalSocietyCofinalReadout
open M14SourceGeneratedUniversalSocietyRootGrammar
open M14SourceGeneratedTenureOrdinaryExitConstitution

/-- Literal finite-Constitution incidence consumed at the root-controlled
tenure exit.  The existential remains in `Prop`, so no completed witness
schedule or stored future is introduced. -/
structure TenureOrdinaryOperationalMaterialAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) : Prop where
  private mk ::
  incidence :
    ∃ semanticRenewal : ExitCapacityRenewalAt birthBearerExitCapacityProgram,
      ∃ code : birthBearerExitRelationCompiler.FutureCode,
        ∃ slot : Fin
            (anomiePhaseAt
              (cycleExitCapacityDepthAt initial depth)).served.length,
          semanticRenewal.exit.1 = code ∧
            ExitCapacitySemanticMaterialAt initial depth code slot ∧
            ExitCapacityTemporalMaterialAt initial depth code

/-- The direct operational projection keeps one literal code and slot across
the exit cone, source-backed Payment, actual route, services, residual and K
injectivity. -/
theorem TenureOrdinaryOperationalMaterialAt.directAuthority
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary} {depth : Nat}
    (material : TenureOrdinaryOperationalMaterialAt initial depth) :
    ∃ code : birthBearerExitRelationCompiler.FutureCode,
      ∃ slot : Fin
          (anomiePhaseAt
            (cycleExitCapacityDepthAt initial depth)).served.length,
        code ∈ birthBearerExitRelationCompiler.futureCodeCarrier ∧
          Nonempty
            (birthBearerExitRelationCompiler.FutureContinuationAt
              birthBearerIndependentExitRelation.1 .target code) ∧
          ¬ birthBearerExitRelationCompiler.futureIdle code ∧
          ¬ birthBearerNoCapture.Captures code ∧
          Nonempty
            (SourceBackedUBIPaymentReceiptAt
              birthBearerExitCapacityProgram.purchasingPowerStanding code) ∧
          Nonempty
            (SourceGeneratedUBIRouteReceiptAt code
              (ExactServedCrossingDebitedRunAt.servicedCrossingAt
                (phase := anomiePhaseAt
                  (cycleExitCapacityDepthAt initial depth))
                (crossingCompiler := crossingCompilerAt
                  (cycleExitCapacityDepthAt initial depth)) slot)) ∧
          PaidExitLifecycleExternalDispositionAt oldVisit sourceIndex
            (cycleLifecycleIndex initial depth) ∧
          PaidExitLifecycleServicesAndFutureAt oldVisit sourceIndex
            (cycleLifecycleIndex initial depth) ∧
          Function.Injective
            (paidExitLifecycleActualServiceKAt oldVisit sourceIndex
              (cycleLifecycleIndex initial depth)) := by
  rcases material.incidence with
    ⟨_renewal, code, slot, _codeExact, semantic, temporal⟩
  exact
    ⟨code, slot, semantic.codeInCarrier,
      semantic.employmentIndependentContinuation, semantic.nonIdle,
      semantic.uncaptured, semantic.sourceBackedPayment, semantic.actualRoute,
      temporal.externalResidual, temporal.actualServicesAndFuture,
      temporal.actualServiceKInjective⟩

/-- Direct proof-carrying consumer.  Every field is a proposition; generated
data remain scoped inside exact dependent incidences. -/
structure ProofCarryingTenureOrdinaryExitConstitutionAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary)
    (observerFuel depth : Nat)
    (ordinary : TenureOrdinaryExitConstitutionAt initial observerFuel depth) :
    Prop where
  private mk ::
  alignmentExact : ordinary.alignment =
    sourceGeneratedTenurePaymentExitBearerAlignment
  tenureLossExact : ordinary.alignment.tenureLoss = tenureRelationLoss
  paymentPurposeExact : ordinary.alignment.exactPaymentPurpose =
    exactTenurePaymentPurpose
  commonBearerExact : exchangeLaw.bearerOfActor tenureActor =
    exchangeLaw.bearerOfActor birthBearerWorker
  tenureRelationTrace :
    ∃ seed : essentialAccessRelationCompiler.ExactRelationSeed,
      seed.actor essentialAccessRelationCompiler = tenureActor ∧
      essentialAccessRelationCompiler.relationOf seed = tenureRelation
  tenurePowerExact : ordinary.tenurePower = tenureExitActionPower
  tenureFreedomLossExact : ordinary.tenurePower.freedomChange =
    .lost .tenure (essentialAccessCode_source_actionable .tenure)
      (essentialAccessCode_target_absent .tenure)
  tenureSourceRoleGenerated : essentialAccessRelationCompiler.RelationRoleAt
    tenureActor tenureRelation .source
      (essentialAccessRelationCompiler.roleAt tenureRelation .source)
  tenureTargetRoleGenerated : essentialAccessRelationCompiler.RelationRoleAt
    tenureActor tenureRelation .target
      (essentialAccessRelationCompiler.roleAt tenureRelation .target)
  tenureRootPassedAudit :
    ∃ audit : TenureActualPassedAuditAt initial depth,
      audit = universalSocietyActualPassedAuditAt oldVisit sourceIndex
        (cycleCanonicalRootLawIndex initial depth) .essentialAccessTenure
  tenureRootExactlyOnce :
    ∃! point :
        (universalSocietyRecognitionAt oldVisit sourceIndex).PointAt
          (universalSocietyVisitAt oldVisit sourceIndex
            (cycleCanonicalRootLawIndex initial depth)),
      point ∈
          (universalSocietyRecognitionAt oldVisit sourceIndex
            ).scenarioRestrictionAt
              (universalSocietyVisitAt oldVisit sourceIndex
                (cycleCanonicalRootLawIndex initial depth)) .actual ∧
        point.face = .essentialAccessTenure
  finiteConstitution : FiniteExitCapacityConstitutionAt initial depth
  finiteConstitutionExact : ordinary.finiteConstitution =
    (exactCanonicalSocietyRenewalPulseAt initial observerFuel depth
      ).rootLawTransition.sourceConstitution
  operationalMaterial : TenureOrdinaryOperationalMaterialAt initial depth
  sourceRootLawTransition :
    let lawStep := sourceGeneratedCycleCanonicalRootLawStep initial depth
    ProofCarryingCycleCanonicalRootLawTransitionAt initial observerFuel depth
      lawStep
  sourceActualSearchSameRoot :
    let lawStep := sourceGeneratedCycleCanonicalRootLawStep initial depth
    CycleCanonicalRootLawActualSearchSameRootAt lawStep.sourceLaw
  sourceRootLedgerAndNext :
    let lawStep := sourceGeneratedCycleCanonicalRootLawStep initial depth
    CycleCanonicalRootLawLedgerAndNextAt initial depth lawStep.sourceLaw
  selfU8Tick : ExactCanonicalSelfU8TickAt initial depth
  compatibleFutureBirth :
    ExactCanonicalCompatibleFutureBirthAt initial observerFuel depth
  fullCaptureNominal : NominalTransferReadoutAt birthBearerCapturedProgram
  fullCaptureRenewalEmpty :
    IsEmpty (ExitCapacityRenewalAt birthBearerCapturedProgram)

/-- The stored operational incidence is destructed exactly once here. -/
theorem proofCarryingTenureOrdinaryExitConstitution
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel depth : Nat}
    (ordinary : TenureOrdinaryExitConstitutionAt initial observerFuel depth) :
    ProofCarryingTenureOrdinaryExitConstitutionAt initial observerFuel depth
      ordinary := by
  rcases ordinary.rootOperationalIncidence with
    ⟨renewal, code, slot, codeExact, semantic, temporal⟩
  let pulse := exactCanonicalSocietyRenewalPulseAt initial observerFuel depth
  have exactlyOnce :=
    (universalSocietyRecognitionAt oldVisit sourceIndex
      ).scenarioFace_exactlyOnce_inRestriction
        (universalSocietyVisitAt oldVisit sourceIndex
          (cycleCanonicalRootLawIndex initial depth))
        PostSettlementSocietyScenario.actual
        PostSettlementSocietyBearingFace.essentialAccessTenure
  refine
    { alignmentExact := ordinary.alignmentExact
      tenureLossExact := ?_
      paymentPurposeExact := ?_
      commonBearerExact := ordinary.alignment.commonBearerExact
      tenureRelationTrace := ordinary.tenureRelationTrace
      tenurePowerExact := ordinary.tenurePowerExact
      tenureFreedomLossExact := ordinary.tenureLossExact
      tenureSourceRoleGenerated := ordinary.sourceRoleGenerated
      tenureTargetRoleGenerated := ordinary.targetRoleGenerated
      tenureRootPassedAudit :=
        ⟨ordinary.tenureRootPassedAudit,
          ordinary.tenureRootPassedAuditExact⟩
      tenureRootExactlyOnce := exactlyOnce
      finiteConstitution := ordinary.finiteConstitution
      finiteConstitutionExact := ordinary.finiteConstitutionExact
      operationalMaterial :=
        ⟨⟨renewal, code, slot, codeExact, semantic, temporal⟩⟩
      sourceRootLawTransition := pulse.rootLawTransition
      sourceActualSearchSameRoot :=
        pulse.rootLawTransition.sourceActualSearchSameRoot
      sourceRootLedgerAndNext :=
        pulse.rootLawTransition.sourceRootLedgerAndNext
      selfU8Tick := pulse.selfU8Tick
      compatibleFutureBirth := pulse.compatibleFutureBirth
      fullCaptureNominal := ordinary.fullCaptureNominal
      fullCaptureRenewalEmpty := ordinary.fullCaptureRenewalEmpty }
  · rw [ordinary.alignmentExact]
    exact sourceGeneratedTenurePaymentExitBearerAlignment.tenureLossExact
  · exact ordinary.alignment.exactPaymentPurposeExact

/-- Premise-free public audit at every generated cycle. -/
theorem sourceGeneratedProofCarryingTenureOrdinaryExitConstitutionAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary)
    (observerFuel depth : Nat) :
    let ordinary :=
      sourceGeneratedTenureOrdinaryExitConstitutionAt initial observerFuel depth
    ProofCarryingTenureOrdinaryExitConstitutionAt initial observerFuel depth
      ordinary :=
  proofCarryingTenureOrdinaryExitConstitution
    (sourceGeneratedTenureOrdinaryExitConstitutionAt initial observerFuel depth)

end
end M14ProofCarryingTenureOrdinaryExitConstitution
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingTenureOrdinaryExitConstitution.TenureOrdinaryOperationalMaterialAt.directAuthority
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingTenureOrdinaryExitConstitution.proofCarryingTenureOrdinaryExitConstitution
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingTenureOrdinaryExitConstitution.sourceGeneratedProofCarryingTenureOrdinaryExitConstitutionAt
