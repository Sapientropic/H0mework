import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.CrossCompiler.Readout.Recognition.Admission.Finality.Consumer.ProofCarryingCanonicalSocietyLawFinalRuntimeOpen
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.Ordinary.CrossCompiler.Mandate.Standing.Consumer.ProofCarryingInstalledMandateFiniteConstitutionIncidence
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.Ordinary.CrossCompiler.Mandate.Standing.NoGo.SourceInstalledMandateFiniteConstitutionNoGo
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.NoGo.CaptureJob.SourceGeneratedFiniteExitCapacityCaptureJobNoGo
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.CrossCompiler.Readout.Recognition.Admission.Constitution.RootLaw.Completion.Consumer.ProofCarryingCanonicalSocietyRootLawComplete

/-!
# One source-generated canonical-Society constitutional point

One requested cofinal point fixes one actual depth `m`.  At that same depth
this file consumes the canonical root-law transition, the installed mandate
incidence, the exit-capacity/capture/Job-Guarantee no-go, the strong observer
kernel, external residual liability and the exact self-U8 successor.

This is a pointwise assembly over existing producers.  It introduces no
identity, occurrence, ledger, runtime, registry or future schedule.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedCanonicalSocietyConstitutionalPoint

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer Renewal UniversalRootGrammar
open Lifecycle Universal Relations Power Exchange Settlement Price Money UBI
open Capacity Space CrossingCost Election
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedCycleCanonicalRootLawStep
open M14SourceGeneratedCanonicalSocietyCofinalReadout
open M14ProofCarryingFiniteCycleCanonicalRootLaw
open M14ProofCarryingCanonicalSocietyCofinalReadout
open M14ProofCarryingPlatformGateCofinalFiniteLawDiagonal
open M14ProofCarryingCanonicalSocietyLawFinalRuntimeOpen
open M14SourceInstalledMandateFiniteConstitutionIncidence
open M14ProofCarryingInstalledMandateFiniteConstitutionIncidence
open M14SourceInstalledMandateFiniteConstitutionNoGo
open M14SourceGeneratedPostSettlementObserverFiniteExitCapacityConstitution
open M14SourceGeneratedFiniteExitCapacityCaptureJobNoGo
open M14ProofCarryingCanonicalSocietyRootLawComplete

/-- Concrete constitutional material at one requested later current.

The mandate, exit constitution, observer counterexample, residual liability
and self-U8 all use the same `initial/m`.  Their provenance is the shared
typed index plus the existing actual-fold/root-law producers; no proof-
irrelevance equality is used as a substitute for occurrence identity. -/
structure SourceGeneratedCanonicalSocietyConstitutionalPointAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary)
    (fuel observerFuel m : Nat) : Prop where
  private mk ::
  diagonalPoint :
    PlatformGateFiniteLawDiagonalPointAt initial fuel observerFuel m
  installedMandate :
    let incidence :=
      sourceInstalledMandateFiniteConstitutionIncidenceAt initial m
    ProofCarryingInstalledMandateFiniteConstitutionIncidenceAt initial
      observerFuel m incidence
  installedMandateNoGo :
    InstalledMandateFiniteConstitutionNoGoAt initial m
  exitCaptureJob : FiniteExitCapacityCaptureJobNoGoAt initial m
  mandatePowerPhaseRole :
    type_of% installedMandate.originalPowerPhaseRole
  mandateControllerRelationObligation :
    type_of% installedMandate.controllerRelationObligationExact
  mandateSourceProvenance :
    type_of% installedMandate.criticalRelationAndControllerProvenance
  mandateSameEmbeddedM9Root :
    type_of% installedMandate.sameEmbeddedM9Root
  mandateRootFactorization :
    type_of% installedMandate.mandateRootFactorization
  actualSearchSameRoot :
    type_of% installedMandate.sourceActualSearchSameRoot
  searchHasNoActualWrite :
    type_of% installedMandate.sourceRootLawTransition.sourceGrammarExhaustion.searchHasNoActualWrite
  actualPathsDistinct :
    type_of% diagonalPoint.pointMaterial.selfU8ActualPathsDistinct
  sameNormalFormDifferentK :
    type_of% diagonalPoint.pointMaterial.selfU8SameNormalDifferentK
  noOccurrenceReconstruction :
    type_of% diagonalPoint.pointMaterial.selfU8NoOccurrenceReconstruction
  noAuthorityFactorization :
    type_of% diagonalPoint.pointMaterial.selfU8NoAuthorityFactorization
  noFaithfulReconstruction :
    type_of% diagonalPoint.pointMaterial.selfU8NoFaithfulReconstruction
  rootLawCompleteAndU8Available :
    CanonicalSocietyRootLawCompletionAt diagonalPoint.pointMaterial
  positiveExternalLiability :
    type_of% diagonalPoint.pointMaterial.canonicalMacroFutureBirthAudit.externalLiability
  targetResidualDeletionNoGo :
    type_of% diagonalPoint.pointMaterial.targetDeletionNoGo
  selfU8Tick : ExactCanonicalSelfU8TickAt initial m
  unrevisableRuntimeEmpty :
    let lawStep := sourceGeneratedCycleCanonicalRootLawStep initial m
    IsEmpty
      (M14SourceGeneratedCycleCanonicalRootLawStepNoGo.FinalUnrevisableRuntimeConstitutionAt
        lawStep)
  generatedNextExact :
    generatedFinalNextCycleAt initial m = cycleAt initial (m + 1)

theorem sourceGeneratedCanonicalSocietyConstitutionalPointAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {fuel observerFuel m : Nat}
    (point : PlatformGateFiniteLawDiagonalPointAt initial fuel observerFuel m) :
    SourceGeneratedCanonicalSocietyConstitutionalPointAt initial fuel
      observerFuel m := by
  let incidence :=
    sourceInstalledMandateFiniteConstitutionIncidenceAt initial m
  let mandate :
      ProofCarryingInstalledMandateFiniteConstitutionIncidenceAt initial
        observerFuel m incidence :=
    proofCarryingInstalledMandateFiniteConstitutionIncidence incidence
  let mandateNoGo :=
    sourceInstalledMandateFiniteConstitutionNoGoAt initial m
  let exitCaptureJob :=
    sourceGeneratedFiniteExitCapacityCaptureJobNoGoAt initial m
  exact
    { diagonalPoint := point
      installedMandate := mandate
      installedMandateNoGo := mandateNoGo
      exitCaptureJob := exitCaptureJob
      mandatePowerPhaseRole := mandate.originalPowerPhaseRole
      mandateControllerRelationObligation :=
        mandate.controllerRelationObligationExact
      mandateSourceProvenance :=
        mandate.criticalRelationAndControllerProvenance
      mandateSameEmbeddedM9Root := mandate.sameEmbeddedM9Root
      mandateRootFactorization := mandate.mandateRootFactorization
      actualSearchSameRoot := mandate.sourceActualSearchSameRoot
      searchHasNoActualWrite :=
        mandate.sourceRootLawTransition.sourceGrammarExhaustion
          |>.searchHasNoActualWrite
      actualPathsDistinct :=
        point.pointMaterial.selfU8ActualPathsDistinct
      sameNormalFormDifferentK :=
        point.pointMaterial.selfU8SameNormalDifferentK
      noOccurrenceReconstruction :=
        point.pointMaterial.selfU8NoOccurrenceReconstruction
      noAuthorityFactorization :=
        point.pointMaterial.selfU8NoAuthorityFactorization
      noFaithfulReconstruction :=
        point.pointMaterial.selfU8NoFaithfulReconstruction
      rootLawCompleteAndU8Available :=
        canonicalSocietyRootLawCompletion_directConsumer
          point.pointMaterial
      positiveExternalLiability :=
        point.pointMaterial.canonicalMacroFutureBirthAudit.externalLiability
      targetResidualDeletionNoGo :=
        point.pointMaterial.targetDeletionNoGo
      selfU8Tick := point.pointMaterial.selfU8Tick
      unrevisableRuntimeEmpty :=
        point.pointMaterial.runtimeFinalityReportEmpty
      generatedNextExact := point.generatedFinalNextExact }

/-- Request-driven producer.  It creates only the one later point demanded by
`fuel/observerFuel`; no cofinal witness family is stored. -/
theorem everyRequestedCanonicalSocietyConstitutionalPoint
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    (maximum : ProofCarryingCanonicalSocietyLawFinalRuntimeOpenAt initial)
    (fuel observerFuel : Nat) :
    ∃ m, SourceGeneratedCanonicalSocietyConstitutionalPointAt initial fuel
      observerFuel m := by
  rcases maximum.runtimeOpen fuel observerFuel with ⟨m, point⟩
  exact ⟨m, sourceGeneratedCanonicalSocietyConstitutionalPointAt point⟩

end
end M14SourceGeneratedCanonicalSocietyConstitutionalPoint
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyConstitutionalPoint.sourceGeneratedCanonicalSocietyConstitutionalPointAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyConstitutionalPoint.everyRequestedCanonicalSocietyConstitutionalPoint
