import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Action.SourceGeneratedSequentialContributionCapacityCut

/-!
# Merge-root state that emits the contribution-capacity cut

This inquiry-engine state is fixed at current `1` of the generated merge
root.  It consumes the contribution row and the root's separate
`contributionAction` projection; obstruction inquiry authority is neither
retyped nor borrowed.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityCutActionState

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M14SourceGeneratedContributionMergeRoot
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityCutActionSource
open M14SourceGeneratedSequentialContributionCapacityCut

def contributionCapacityCutActionStateAt
    (oldVisit : OldVisit) :
    RootInquiryStateAt (capacityActionSourceNAt oldVisit)
      (capacityActionSourceVAt oldVisit) where
  root := capacityActionSourceRootAt oldVisit
  visit := capacityActionSourceVisitAt oldVisit
  U7 := contributionMergeU7 (capacityActionRootedAt oldVisit)
  calculus := contributionMergeCalculus (capacityActionRootedAt oldVisit)
  Query := Unit
  entryAt := fun _ => capacityActionSourceEntryAt oldVisit
  authorityAt := fun _ => capacityActionSourceAuthorityAt oldVisit
  compilationProgramAt := fun _ =>
    contributionCapacityCutActionCompilationProgramAt oldVisit
  compilationFaceAt := fun _ =>
    { projection := ContributionMergeProjection.contributionAction
      active := PUnit.unit
      classifier_eq := rfl
      project_heq := HEq.rfl }
  u7RootDisposition_commutes := by
    intro _query _obstruction _audit audit_eq
    cases audit_eq

def contributionCapacityCutActionEngineStateAt
    (oldVisit : OldVisit) :
    RootInquiryEngineStateAt (capacityActionSourceNAt oldVisit)
      (capacityActionSourceVAt oldVisit) :=
  RootInquiryEngineStateAt.create
    (contributionCapacityCutActionStateAt oldVisit)

def contributionCapacityCutActionPresentationAt
    (oldVisit : OldVisit) : RootInquiryStatePresentation where
  N := capacityActionSourceNAt oldVisit
  V := capacityActionSourceVAt oldVisit
  state := contributionCapacityCutActionEngineStateAt oldVisit

@[simp] theorem contributionCapacityCutActionState_compiles_generated
    (oldVisit : OldVisit) :
    (contributionCapacityCutActionStateAt oldVisit).compileInquiry () =
      .actualAction (generatedContributionCapacityCutActionAt oldVisit) :=
  rfl

set_option linter.defProp false in
def contributionCapacityCutActionCompilation_factorizes
    (oldVisit : OldVisit) :=
  (contributionCapacityCutActionEngineStateAt oldVisit)
    |>.generatedCompilation_factorizes ()

end
end M14SourceGeneratedContributionCapacityCutActionState
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityCutActionState.contributionCapacityCutActionState_compiles_generated
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityCutActionState.contributionCapacityCutActionCompilation_factorizes
