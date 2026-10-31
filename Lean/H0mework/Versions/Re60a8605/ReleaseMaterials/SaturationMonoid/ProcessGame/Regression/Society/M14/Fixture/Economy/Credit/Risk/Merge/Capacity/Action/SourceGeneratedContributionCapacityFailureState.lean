import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.U8.SourceGeneratedContributionCapacityU8Revision

/-!
# Capacity-target state that emits self-U8

This state consumes the obstruction row generated alongside the capacity
action's spent contribution row.  Its exact root projection, U7 theory-audit
gate and operational failure compile the unique self-U8 core.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityFailureState

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityCutWorld
open M14SourceGeneratedContributionCapacityCutRoot
open M14SourceGeneratedContributionCapacityCutActionSource
open M14SourceGeneratedContributionCapacityFailure
open M14SourceGeneratedContributionCapacityU8Revision

def contributionCapacityFailureStateAt
    (oldVisit : OldVisit) :
    RootInquiryStateAt
      (CutN (capacityActionRootedAt oldVisit))
      (M14SourceGeneratedContributionCapacityCutCompiler.TargetV
        (capacityActionRootedAt oldVisit)) where
  root := CapacityRootAt oldVisit
  visit := CapacityVisitAt oldVisit
  U7 := contributionCapacityU7 (capacityActionRootedAt oldVisit)
  calculus := contributionCapacityCalculus (capacityActionRootedAt oldVisit)
  Query := Unit
  entryAt := fun _ => contributionCapacityCutTargetObstruction
    (capacityActionRootedAt oldVisit)
  authorityAt := fun _ => contributionCapacityRootTargetObstructionAuthority
    (capacityActionRootedAt oldVisit)
  compilationProgramAt := fun _ =>
    contributionCapacityRequiresU8CompilationProgramAt oldVisit
  compilationFaceAt := fun _ =>
    { projection := ContributionCapacityProjection.inquiry
      active := PUnit.unit
      classifier_eq := rfl
      project_heq := HEq.rfl }
  u7RootDisposition_commutes := by
    intro _query _obstruction _audit audit_eq
    cases audit_eq
    exact capacityFailureRootDispositionCommutesAt oldVisit

def contributionCapacityFailureEngineStateAt
    (oldVisit : OldVisit) :=
  RootInquiryEngineStateAt.create
    (contributionCapacityFailureStateAt oldVisit)

def contributionCapacityFailurePresentationAt
    (oldVisit : OldVisit) : RootInquiryStatePresentation where
  N := CutN (capacityActionRootedAt oldVisit)
  V := M14SourceGeneratedContributionCapacityCutCompiler.TargetV
    (capacityActionRootedAt oldVisit)
  state := contributionCapacityFailureEngineStateAt oldVisit

@[simp] theorem contributionCapacityFailureState_compiles_selfU8
    (oldVisit : OldVisit) :
    (contributionCapacityFailureStateAt oldVisit).compileInquiry () =
      .requiresU8
        (contributionCapacityResidual (capacityActionRootedAt oldVisit))
        (contributionCapacityU7Gate (capacityActionRootedAt oldVisit))
        (contributionCapacityOperationalFailure
          (capacityActionRootedAt oldVisit))
        (generatedContributionCapacityU8CoreAt oldVisit) :=
  rfl

set_option linter.defProp false in
def contributionCapacityFailureCompilation_factorizes
    (oldVisit : OldVisit) :=
  (contributionCapacityFailureEngineStateAt oldVisit)
    |>.generatedCompilation_factorizes ()

end
end M14SourceGeneratedContributionCapacityFailureState
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityFailureState.contributionCapacityFailureState_compiles_selfU8
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityFailureState.contributionCapacityFailureCompilation_factorizes
