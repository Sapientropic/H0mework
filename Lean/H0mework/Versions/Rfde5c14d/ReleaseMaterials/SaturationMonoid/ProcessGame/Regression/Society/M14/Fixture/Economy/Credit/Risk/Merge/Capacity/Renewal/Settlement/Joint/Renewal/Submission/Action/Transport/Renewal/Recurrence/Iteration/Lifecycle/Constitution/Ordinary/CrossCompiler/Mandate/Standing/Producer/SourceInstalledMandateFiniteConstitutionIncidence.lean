import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Mandate.Bearer.SourceInstalledMandateCriticalRelationBearer
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Producer.SourceGeneratedCycleCanonicalRootLawStep

/-!
# Installed mandate standing / finite-Constitution incidence

At the lifecycle-selected actual-service depth, the already installed mandate
coordinate and the canonical outside-option Payment are restrictions of the
same M9 temporal root event.  This file closes that commuting seam before any
mandate-loss claim is attempted.

The mandate side remains the actual continuing face (`renew / held /
restored`).  The Constitution is projected from the canonical actual-fold
maximum, and its semantic incidence is eliminated only downstream.  No
parallel root, mandate compiler, Payment, Constitution or future is stored.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceInstalledMandateFiniteConstitutionIncidence

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Power Exchange Settlement Price Money UBI
open Renewal Capacity Space CrossingCost
open M3FiniteExchangeFixture
open M14UBIPeriodicRootHistory
open M14UBIPeriodicActualServiceCapacity
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityBirthBearerExit
open M14SourceGeneratedPaidSuccessorBearerRoleIndependentContinuation
open M14SourceGeneratedPaidExitLifecycleTemporalSpine
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitch
open M14SourceGeneratedPostSettlementObserverFiniteExitCapacityConstitution
open M14SourceGeneratedCycleCanonicalRootLawStep
open M14SourceInstalledMandateCriticalRelationBearer

def mandateConstitutionDepthAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) : Nat :=
  cycleExitCapacityDepthAt initial depth

/-- The exact M9 Payment occurrence embedded in the canonical root-law
maximum's role-independent continuation. -/
def canonicalConstitutionEmbeddedPaymentAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :=
  (cycleCanonicalRootLawAt initial depth
    ).lifecycleFromActualContinuation.lifecycleMaximum.continuation
      |>.successorContinuationCarrier
      |>.response
      |>.bearerExit
      |>.existingPaymentOccurrence

theorem canonicalConstitutionEmbeddedPayment_eq_periodic
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    canonicalConstitutionEmbeddedPaymentAt initial depth =
      periodicSourceBackedPaymentAt (mandateConstitutionDepthAt initial depth) :=
  (cycleCanonicalRootLawAt initial depth
    ).lifecycleFromActualContinuation.lifecycleMaximum.continuation
      |>.successorContinuationCarrier
      |>.response
      |>.bearerExit
      |>.paymentOccurrence_eq_canonical

/-- The mandate restriction and the embedded outside-option Payment have the
same exact M9 root occurrence at the lifecycle-selected depth. -/
theorem installedMandate_and_constitutionPayment_sameRoot
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    (sourceInstalledMandateCriticalRelationBearerAt
      (mandateConstitutionDepthAt initial depth)).mandate.rootOccurrence =
        (canonicalConstitutionEmbeddedPaymentAt initial depth).rootOccurrence := by
  rw [(sourceInstalledMandateCriticalRelationBearerAt
    (mandateConstitutionDepthAt initial depth)).mandateExact]
  rw [canonicalConstitutionEmbeddedPayment_eq_periodic]

/-- Zero-choice integration carrier.  It stores the existing installed
mandate bearer seal and only propositional commuting facts about the canonical
root law. -/
structure SourceInstalledMandateFiniteConstitutionIncidenceAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) : Type 32 where
  private mk ::
  mandate : SourceInstalledMandateCriticalRelationBearerAt
    (mandateConstitutionDepthAt initial depth)
  mandateExact : mandate = sourceInstalledMandateCriticalRelationBearerAt
    (mandateConstitutionDepthAt initial depth)
  actualFoldMaximumExact :
    (cycleCanonicalRootLawAt initial depth
      ).lifecycleFromActualContinuation.lifecycleMaximum =
      cycleLifecycleMaximum initial depth
  commonBearerIsExitWorker : mandate.criticalBearer.commonBearer =
    exchangeLaw.bearerOfActor birthBearerWorker
  sameEmbeddedM9Root : mandate.mandate.rootOccurrence =
    (canonicalConstitutionEmbeddedPaymentAt initial depth).rootOccurrence

/-- Sole producer; its public mouth is only the canonical cycle and depth. -/
def sourceInstalledMandateFiniteConstitutionIncidenceAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    SourceInstalledMandateFiniteConstitutionIncidenceAt initial depth := by
  let mandate := sourceInstalledMandateCriticalRelationBearerAt
    (mandateConstitutionDepthAt initial depth)
  exact
    { mandate := mandate
      mandateExact := rfl
      actualFoldMaximumExact :=
        cycleCanonicalRootLawActualFoldMaximum_eq_cycleMaximum initial depth
      commonBearerIsExitWorker := by
        rw [mandate.commonBearer_eq_parent]
        exact birthBearerWorker_bearer_exact.symm
      sameEmbeddedM9Root :=
        installedMandate_and_constitutionPayment_sameRoot initial depth }

namespace SourceInstalledMandateFiniteConstitutionIncidenceAt

variable {oldVisit : OldVisit} {sourceIndex boundary : Nat}
variable {initial : CycleAt oldVisit sourceIndex boundary} {depth : Nat}
variable (incidence :
  SourceInstalledMandateFiniteConstitutionIncidenceAt initial depth)

include incidence
/-- Operational material is literally the semantic incidence of that
projected Constitution. -/
theorem semanticRenewalIncidence :
    ∃ semanticRenewal : ExitCapacityRenewalAt birthBearerExitCapacityProgram,
      ∃ code : birthBearerExitRelationCompiler.FutureCode,
        ∃ slot : Fin
            (anomiePhaseAt
              (cycleExitCapacityDepthAt initial depth)).served.length,
          semanticRenewal.exit.1 = code ∧
            ExitCapacitySemanticMaterialAt initial depth code slot ∧
            ExitCapacityTemporalMaterialAt initial depth code :=
  by
    cases incidence
    exact
      (cycleCanonicalRootLawConstitutionFromActualFold initial depth
        ).semanticRenewalIncidence

/-- The installed mandate coordinate retains its root factorization and next
while sharing the outside-option Payment occurrence. -/
theorem mandateRootFactorizationAndPayment :
    incidence.mandate.mandate.installed.RootAnswerAndNextFactorizes ∧
      incidence.mandate.mandate.rootOccurrence =
        (canonicalConstitutionEmbeddedPaymentAt initial depth).rootOccurrence :=
  ⟨incidence.mandate.mandate.rootFactorization,
    incidence.sameEmbeddedM9Root⟩

end SourceInstalledMandateFiniteConstitutionIncidenceAt

end
end M14SourceInstalledMandateFiniteConstitutionIncidence
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceInstalledMandateFiniteConstitutionIncidence.canonicalConstitutionEmbeddedPayment_eq_periodic
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceInstalledMandateFiniteConstitutionIncidence.installedMandate_and_constitutionPayment_sameRoot
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceInstalledMandateFiniteConstitutionIncidence.sourceInstalledMandateFiniteConstitutionIncidenceAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceInstalledMandateFiniteConstitutionIncidence.SourceInstalledMandateFiniteConstitutionIncidenceAt.semanticRenewalIncidence
