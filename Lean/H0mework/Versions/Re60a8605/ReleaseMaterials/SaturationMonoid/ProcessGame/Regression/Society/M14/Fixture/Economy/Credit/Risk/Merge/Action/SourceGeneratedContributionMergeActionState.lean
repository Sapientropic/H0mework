import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Action.SourceGeneratedSequentialContributionMerge

/-!
# Revised-root state that emits the contribution merge

This is the ordinary inquiry-engine presentation of revised current `2`.
It consumes the revised root's existing inquiry projection and the exact
sequential merge program.  No target state or runtime is defined here.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionMergeActionState

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M9ProofCarryingRenewalInquiryRoot
open M9ProofCarryingRenewalU8RevisedWorld
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedSequentialContributionMerge

def contributionMergeActionStateAt
    (oldVisit : OldVisit) :
    RootInquiryStateAt (actionSourceNAt oldVisit)
      (actionSourceVAt oldVisit) where
  root := actionSourceRootAt oldVisit
  visit := actionSourceVisitAt oldVisit
  U7 := revisedU7At oldVisit
  calculus := revisedCalculusAt oldVisit
  Query := Unit
  entryAt := fun _ => actionSourceEntryAt oldVisit
  authorityAt := fun _ => actionSourceAuthorityAt oldVisit
  compilationProgramAt := fun _ =>
    contributionMergeActionCompilationProgramAt oldVisit
  compilationFaceAt := fun _ =>
    { projection := RevisedProjection.inquiry
      active := PUnit.unit
      classifier_eq := rfl
      project_heq := HEq.rfl }
  u7RootDisposition_commutes := by
    intro _query _obstruction _audit audit_eq
    cases audit_eq

def contributionMergeActionEngineStateAt
    (oldVisit : OldVisit) :
    RootInquiryEngineStateAt (actionSourceNAt oldVisit)
      (actionSourceVAt oldVisit) :=
  RootInquiryEngineStateAt.create
    (contributionMergeActionStateAt oldVisit)

def contributionMergeActionPresentationAt
    (oldVisit : OldVisit) : RootInquiryStatePresentation where
  N := actionSourceNAt oldVisit
  V := actionSourceVAt oldVisit
  state := contributionMergeActionEngineStateAt oldVisit

@[simp] theorem contributionMergeActionState_compiles_generated
    (oldVisit : OldVisit) :
    (contributionMergeActionStateAt oldVisit).compileInquiry () =
      .actualAction (generatedContributionMergeActionAt oldVisit) :=
  rfl

set_option linter.defProp false in
def contributionMergeActionCompilation_factorizes
    (oldVisit : OldVisit) :=
  (contributionMergeActionEngineStateAt oldVisit)
    |>.generatedCompilation_factorizes ()

/-! Initial-old-visit facade used by the canonical M9 runtime. -/

abbrev initialOldVisit := jointRoot.toAuthoritativeRoot.toRoot.initialVisit

def contributionMergeActionState :=
  contributionMergeActionStateAt initialOldVisit

def contributionMergeActionEngineState :=
  contributionMergeActionEngineStateAt initialOldVisit

def contributionMergeActionPresentation :=
  contributionMergeActionPresentationAt initialOldVisit

def generatedContributionMergeAction :=
  generatedContributionMergeActionAt initialOldVisit

end
end M14SourceGeneratedContributionMergeActionState
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionMergeActionState.contributionMergeActionState_compiles_generated
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionMergeActionState.contributionMergeActionCompilation_factorizes
