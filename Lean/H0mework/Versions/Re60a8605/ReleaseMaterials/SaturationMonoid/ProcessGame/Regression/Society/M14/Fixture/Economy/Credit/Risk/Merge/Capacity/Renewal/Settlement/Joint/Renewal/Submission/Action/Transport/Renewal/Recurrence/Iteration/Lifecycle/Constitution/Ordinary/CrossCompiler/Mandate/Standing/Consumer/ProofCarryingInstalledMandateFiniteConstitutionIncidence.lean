import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.Ordinary.CrossCompiler.Mandate.Standing.Producer.SourceInstalledMandateFiniteConstitutionIncidence
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Producer.SourceGeneratedCanonicalSocietyCofinalReadout

/-!
# Proof-carrying installed mandate / finite-Constitution incidence

This consumer keeps the exact installed mandate standing face honest: its
power is restored, its phase is renewal and its target role is held.  At the
same time it eliminates the canonical Constitution incidence whose Payment
shares that face's exact embedded M9 root occurrence.

The common lifecycle bearer is the only cross-compiler bridge.  No mandate
actor is identified with the UBI worker, and no mandate loss is claimed here.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingInstalledMandateFiniteConstitutionIncidence

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer Renewal UniversalRootGrammar
open Lifecycle Universal Relations Power Exchange Settlement Price Money UBI
open Capacity Space CrossingCost Election
open M3FiniteExchangeFixture
open M8ActualElectionMandateRenewalRegression
open M10OccurrenceCapacityDebitedRunFixture
open M14UBIPeriodicActualServiceCapacity
open M14UBIProofCarryingRootRestriction
open M14UBIExitCapacityFixture
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityBirthBearerExit
open M14SourceGeneratedPaidExitLifecycleTemporalSpine
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitch
open M14SourceGeneratedPostSettlementObserverFiniteExitCapacityConstitution
open M14SourceGeneratedCycleCanonicalRootLawStep
open M14ProofCarryingFiniteCycleCanonicalRootLaw
open M14SourceGeneratedCanonicalSocietyCofinalReadout
open M14SourceMandateRenewal
open M14SourceInstalledMandateCriticalRelationBearer
open M14SourceInstalledMandateFiniteConstitutionIncidence

/-- Literal Constitution material retained in `Prop`; no witness schedule is
stored. -/
structure InstalledMandateOperationalMaterialAt
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

theorem InstalledMandateOperationalMaterialAt.directAuthority
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary} {depth : Nat}
    (material : InstalledMandateOperationalMaterialAt initial depth) :
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
    ⟨_renewal, code, slot, _exact, semantic, temporal⟩
  exact
    ⟨code, slot, semantic.codeInCarrier,
      semantic.employmentIndependentContinuation, semantic.nonIdle,
      semantic.uncaptured, semantic.sourceBackedPayment, semantic.actualRoute,
      temporal.externalResidual, temporal.actualServicesAndFuture,
      temporal.actualServiceKInjective⟩

structure ProofCarryingInstalledMandateFiniteConstitutionIncidenceAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary)
    (observerFuel depth : Nat)
    (incidence : SourceInstalledMandateFiniteConstitutionIncidenceAt
      initial depth) : Prop where
  private mk ::
  mandateExact : incidence.mandate =
    sourceInstalledMandateCriticalRelationBearerAt
      (mandateConstitutionDepthAt initial depth)
  originalPowerPhaseRole :
    incidence.mandate.mandate.localFace.responsibilityConsumer.1.1 =
        mandateActionPower sourceMandateHistory lineageCompiler ∧
      MandateRelationCompiler.phaseStep
          incidence.mandate.mandate.localFace.standing.relation = .renew ∧
      MandateRelationCompiler.roleAt
          incidence.mandate.mandate.localFace.standing.relation .target = .held
  controllerRelationObligationExact :
    incidence.mandate.mandate.localFace.standing.controller.1 =
        incidence.mandate.mandate.localFace.standing.relation.1.controller ∧
      incidence.mandate.mandate.localFace.standing.relation.1.controller =
        incidence.mandate.mandate.localFace.standing.obligation.bearer
  criticalRelationAndControllerProvenance :
    (∃ seed : MandateRelationCompiler.ExactRelationSeed,
      (∃ state ∈ SourceMandateGame.occurrence.trace,
        state = (officeFace lineageCompiler).state SourceMandateGame.source ∧
        MandateRelationCompiler.relationSeedAt SourceMandateGame.source state
          seed.1 ∧
        (officeFace lineageCompiler).SeedAt SourceMandateGame.source state
          (MandateRelationCompiler.beneficiaryActorSeed seed.1)) ∧
      seed.actor MandateRelationCompiler =
        (M14PeriodicMandatePowerRenewal.periodicMandatePowerRenewalAt
          (mandateConstitutionDepthAt initial depth)
          ).localFace.standing.office ∧
      MandateRelationCompiler.relationOf seed =
        (M14PeriodicMandatePowerRenewal.periodicMandatePowerRenewalAt
          (mandateConstitutionDepthAt initial depth)
          ).localFace.standing.relation) ∧
      (∃ state ∈ SourceMandateGame.occurrence.trace,
        state = MandateControllerCompiler.actionState SourceMandateGame.source ∧
          MandateControllerCompiler.actionAdmittedAt
            (M14PeriodicMandatePowerRenewal.periodicMandatePowerRenewalAt
              (mandateConstitutionDepthAt initial depth)
              ).localFace.responsibilityConsumer.1.1.action.1)
  commonBearerOnly : incidence.mandate.criticalBearer.commonBearer =
    exchangeLaw.bearerOfActor birthBearerWorker
  sameEmbeddedM9Root : incidence.mandate.mandate.rootOccurrence =
    (canonicalConstitutionEmbeddedPaymentAt initial depth).rootOccurrence
  mandateRootFactorization :
    incidence.mandate.mandate.installed.RootAnswerAndNextFactorizes
  operationalMaterial : InstalledMandateOperationalMaterialAt initial depth
  sourceRootLawTransition :
    let step := sourceGeneratedCycleCanonicalRootLawStep initial depth
    ProofCarryingCycleCanonicalRootLawTransitionAt initial observerFuel depth
      step
  sourceActualSearchSameRoot :
    let step := sourceGeneratedCycleCanonicalRootLawStep initial depth
    CycleCanonicalRootLawActualSearchSameRootAt step.sourceLaw
  sourceRootLedgerAndNext :
    let step := sourceGeneratedCycleCanonicalRootLawStep initial depth
    CycleCanonicalRootLawLedgerAndNextAt initial depth step.sourceLaw
  selfU8Tick : ExactCanonicalSelfU8TickAt initial depth
  compatibleFutureBirth :
    ExactCanonicalCompatibleFutureBirthAt initial observerFuel depth

theorem proofCarryingInstalledMandateFiniteConstitutionIncidence
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel depth : Nat}
    (incidence : SourceInstalledMandateFiniteConstitutionIncidenceAt
      initial depth) :
    ProofCarryingInstalledMandateFiniteConstitutionIncidenceAt initial
      observerFuel depth incidence := by
  let pulse := exactCanonicalSocietyRenewalPulseAt initial observerFuel depth
  exact
    { mandateExact := incidence.mandateExact
      originalPowerPhaseRole := incidence.mandate.exact_power_phase_role
      controllerRelationObligationExact := by
        rw [incidence.mandate.mandateExact]
        exact installedMandate_controller_relation_obligation_exact _
      criticalRelationAndControllerProvenance :=
        incidence.mandate.exact_relation_and_controller_provenance
      commonBearerOnly := incidence.commonBearerIsExitWorker
      sameEmbeddedM9Root := incidence.sameEmbeddedM9Root
      mandateRootFactorization :=
        incidence.mandate.mandate.rootFactorization
      operationalMaterial := ⟨incidence.semanticRenewalIncidence⟩
      sourceRootLawTransition := pulse.rootLawTransition
      sourceActualSearchSameRoot :=
        pulse.rootLawTransition.sourceActualSearchSameRoot
      sourceRootLedgerAndNext :=
        pulse.rootLawTransition.sourceRootLedgerAndNext
      selfU8Tick := pulse.selfU8Tick
      compatibleFutureBirth := pulse.compatibleFutureBirth }

theorem sourceGeneratedProofCarryingInstalledMandateFiniteConstitutionAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary)
    (observerFuel depth : Nat) :
    let incidence :=
      sourceInstalledMandateFiniteConstitutionIncidenceAt initial depth
    ProofCarryingInstalledMandateFiniteConstitutionIncidenceAt initial
      observerFuel depth incidence :=
  proofCarryingInstalledMandateFiniteConstitutionIncidence
    (sourceInstalledMandateFiniteConstitutionIncidenceAt initial depth)

end
end M14ProofCarryingInstalledMandateFiniteConstitutionIncidence
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingInstalledMandateFiniteConstitutionIncidence.InstalledMandateOperationalMaterialAt.directAuthority
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingInstalledMandateFiniteConstitutionIncidence.proofCarryingInstalledMandateFiniteConstitutionIncidence
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingInstalledMandateFiniteConstitutionIncidence.sourceGeneratedProofCarryingInstalledMandateFiniteConstitutionAt
