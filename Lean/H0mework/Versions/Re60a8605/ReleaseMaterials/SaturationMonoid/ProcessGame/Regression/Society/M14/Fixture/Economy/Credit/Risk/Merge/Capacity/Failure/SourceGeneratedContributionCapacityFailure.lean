import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Action.SourceGeneratedContributionCapacityCutActionState

/-!
# Same-occurrence contribution-capacity failure

The capacity action's first whole-ledger image contains both its spent
contribution row and the obstruction-continuity row.  This module roots the
exact source-generated capacity residual on that latter row.  The action and
search therefore share one target occurrence while retaining distinct causal
row authority.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityFailure

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open ConstructiveRoot.ObstructionGeneratedMinimalCoface
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityCutWorld
open M14SourceGeneratedContributionCapacityCutCompiler
open M14SourceGeneratedContributionCapacityCutRoot
open M14SourceGeneratedContributionCapacityCutActionSource

abbrev CapacityRootAt (oldVisit : OldVisit) :=
  contributionCapacityLivingRoot (capacityActionRootedAt oldVisit)

abbrev CapacityVisitAt (oldVisit : OldVisit) :=
  contributionCapacityRootTargetVisit (capacityActionRootedAt oldVisit)

theorem capacityFailureRootDispositionCommutesAt
    (oldVisit : OldVisit) :
    U7DemandEntryRootDispositionCommutesAt
      (contributionCapacityCalculus (capacityActionRootedAt oldVisit))
      (contributionCapacityU7Event (capacityActionRootedAt oldVisit))
      (contributionCapacityCutTargetObstruction
        (capacityActionRootedAt oldVisit))
      (((CapacityRootAt oldVisit).toAuthoritativeRoot.toLedgerRoot.source
        |>.ledgerCompiler.compile
          ((CapacityRootAt oldVisit).emitted
            (CapacityVisitAt oldVisit).current)).entryDisposition
              (contributionCapacityCutTargetObstruction
                (capacityActionRootedAt oldVisit))) :=
  ⟨HEq.rfl, HEq.rfl⟩

def capacityFailureFaceAt
    (oldVisit : OldVisit) :
    SourceNativeRootExpressibilityFailureFaceAt
      (CapacityRootAt oldVisit).toAuthoritativeRoot
      (CapacityVisitAt oldVisit)
      (U7 := contributionCapacityU7 (capacityActionRootedAt oldVisit))
      (contributionCapacityOperationalFailure
        (capacityActionRootedAt oldVisit)) where
  lawSurface_eq := rfl
  projection := ContributionCapacityProjection.failure
  active := PUnit.unit
  classifier_eq := rfl
  calculus := contributionCapacityCalculus (capacityActionRootedAt oldVisit)
  u7Event := contributionCapacityU7Event (capacityActionRootedAt oldVisit)
  u7Event_eq_emit := rfl
  theoryAudit := contributionCapacityU7Gate (capacityActionRootedAt oldVisit)
  support_eq := rfl
  rootEntry := contributionCapacityCutTargetObstruction
    (capacityActionRootedAt oldVisit)
  rootEntryAtFailure_eq := rfl
  rootDispositionCommutes := capacityFailureRootDispositionCommutesAt oldVisit
  project_heq := HEq.rfl

def capacityFailureSuccessorAt
    (oldVisit : OldVisit) :
    CausalEntrySuccessorAt
      (CapacityRootAt oldVisit).toAuthoritativeRoot.toLedgerRoot
      (CapacityVisitAt oldVisit)
      (contributionCapacityCutTargetObstruction
        (capacityActionRootedAt oldVisit)) :=
  CausalEntrySuccessorAt.ofNonterminal rfl

def capacityRootedFailureAt
    (oldVisit : OldVisit) :
    RootedActualExpressibilityFailureAt
      (CapacityRootAt oldVisit).toAuthoritativeRoot
      (CapacityVisitAt oldVisit)
      (contributionCapacityU7 (capacityActionRootedAt oldVisit))
      (contributionCapacityOperationalFailure
        (capacityActionRootedAt oldVisit)) :=
  RootedActualExpressibilityFailureAt.ofRootFailureFace
    (capacityFailureFaceAt oldVisit)
    (contributionCapacityRootTargetObstructionAuthority
      (capacityActionRootedAt oldVisit)).toAuthoritativeAuthority
    (capacityFailureSuccessorAt oldVisit)

def capacityGeneratedMinimalCofaceAt
    (oldVisit : OldVisit) :
    GeneratedMinimalCofaceAt (capacityRootedFailureAt oldVisit) :=
  root_obstruction_generates_minimal_coface
    (capacityRootedFailureAt oldVisit)

@[simp] theorem capacityRootedFailure_entry_exact
    (oldVisit : OldVisit) :
    (capacityRootedFailureAt oldVisit).rootEntry =
      contributionCapacityCutTargetObstruction
        (capacityActionRootedAt oldVisit) :=
  rfl

@[simp] theorem capacityRootedFailure_occurrence_exact
    (oldVisit : OldVisit) :
    (capacityRootedFailureAt oldVisit).oldBoundaryEvolution.occurrence =
      contributionCapacityCutEmitted
        (capacityActionRootedAt oldVisit) 1 :=
  rfl

end
end M14SourceGeneratedContributionCapacityFailure
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityFailure.capacityFailureFaceAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityFailure.capacityRootedFailureAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityFailure.capacityGeneratedMinimalCofaceAt
