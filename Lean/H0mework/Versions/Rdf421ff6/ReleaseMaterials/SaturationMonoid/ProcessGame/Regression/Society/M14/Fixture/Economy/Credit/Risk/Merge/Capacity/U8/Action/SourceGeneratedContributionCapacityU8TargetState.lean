import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Action.SourceGeneratedContributionCapacityFailureState

/-!
# Generated self-U8 target states

The U8 core's first whole-ledger write carries the newly addressable residual
row to current `1`.  Runtime-facing states follow only that generated row and
its `.next` authority chain; the initial coface occurrence is not exposed as
an independently selectable future.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityU8TargetState

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityU8Lifecycle
open M14SourceGeneratedContributionCapacityU8Compiler
open M14SourceGeneratedContributionCapacityU8Root
open M14SourceGeneratedContributionCapacityU8Revision

abbrev CapacityU8RootAt (oldVisit : OldVisit) :=
  contributionCapacityU8LivingRoot oldVisit

abbrev CapacityU8RootVisitAt (oldVisit : OldVisit) :=
  RootVisit (CapacityU8RootAt oldVisit).toAuthoritativeRoot.toRoot

def contributionCapacityU8RootVisitAt
    (oldVisit : OldVisit) : Nat → CapacityU8RootVisitAt oldVisit
  | 0 => (CapacityU8RootAt oldVisit).toAuthoritativeRoot.toRoot.initialVisit
  | index + 1 =>
      (contributionCapacityU8RootVisitAt oldVisit index).next rfl

def contributionCapacityU8TemporalVisitAt
    (oldVisit : OldVisit) (index : Nat) :
    ContributionCapacityU8RootVisitAt oldVisit :=
  .finite (contributionCapacityU8RootVisitAt oldVisit index)

@[simp] theorem contributionCapacityU8Visit_current_exact
    (oldVisit : OldVisit) (index : Nat) :
    (show Nat from
      (contributionCapacityU8TemporalVisitAt oldVisit index).current) = index := by
  induction index with
  | zero => rfl
  | succ index inductionHypothesis =>
      change
        (show Nat from
          (contributionCapacityU8RootVisitAt oldVisit index).current) + 1 =
          index + 1
      exact congrArg (fun current : Nat => current + 1) inductionHypothesis

theorem contributionCapacityU8NextEqAt
    (oldVisit : OldVisit) (index : Nat) :
    ((CapacityU8RootAt oldVisit).toAuthoritativeRoot.toRoot.evolutionAt
      (contributionCapacityU8TemporalVisitAt oldVisit index).current
      ).nextCurrent? =
        some
          (contributionCapacityU8TemporalVisitAt oldVisit
            (index + 1)).current :=
  rfl

def contributionCapacityU8InitialResidualAuthorityAt
    (oldVisit : OldVisit) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt
      (CapacityU8RootAt oldVisit)
      (contributionCapacityU8TemporalVisitAt oldVisit 0)
      (contributionCapacityU8GeneratedResidual oldVisit) :=
  SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitialRow
    (CapacityU8RootAt oldVisit)
    (contributionCapacityU8GeneratedResidual oldVisit)
    (contributionCapacityU8GeneratedResidualRow oldVisit)

def contributionCapacityU8ResidualAuthorityAt
    (oldVisit : OldVisit) :
    (index : Nat) →
      SourceNativeLivingTemporalCausalEntryAuthorityAt
        (CapacityU8RootAt oldVisit)
        (contributionCapacityU8TemporalVisitAt oldVisit index)
        (contributionCapacityU8GeneratedResidual oldVisit)
  | 0 => contributionCapacityU8InitialResidualAuthorityAt oldVisit
  | index + 1 =>
      (contributionCapacityU8ResidualAuthorityAt oldVisit index).next
        (contributionCapacityU8NextEqAt oldVisit index)

/-! ## Runtime target starts after the U8 first-write answer-and-next -/

def contributionCapacityU8RuntimeVisitAt
    (oldVisit : OldVisit) (index : Nat) :
    ContributionCapacityU8RootVisitAt oldVisit :=
  contributionCapacityU8TemporalVisitAt oldVisit (index + 2)

abbrev contributionCapacityU8RuntimeAuthorityAt
    (oldVisit : OldVisit) (index : Nat) :=
  contributionCapacityU8ResidualAuthorityAt oldVisit (index + 2)

def contributionCapacityU8InquiryEventAt
    (oldVisit : OldVisit) (index : Nat) :=
  ULift.up.{1, 0}
    ((CapacityU8RootAt oldVisit).emitted
      (contributionCapacityU8RuntimeVisitAt oldVisit index).current)

def contributionCapacityU8AnswerFaceAt
    (oldVisit : OldVisit) (index : Nat) :
    SourceNativeRootSemanticFaceAt
      (CapacityU8RootAt oldVisit)
      (contributionCapacityU8RuntimeVisitAt oldVisit index) where
  projection := ContributionCapacityU8Projection.answer
  active := PUnit.unit
  classifier_eq := rfl

def contributionCapacityU8AnswerConsumerAt
    (oldVisit : OldVisit) (index : Nat) :
    SourceNativeInquiryAnswerConsumerAt ()
      (contributionCapacityU8InquiryEventAt oldVisit index)
      (contributionCapacityU8GeneratedResidual oldVisit)
      (contributionCapacityU8AnswerFaceAt oldVisit index) where
  projection := ContributionCapacityU8Projection.consumer 2
  active := PUnit.unit
  classifier_eq := rfl
  project_heq := HEq.rfl

def contributionCapacityU8AnsweredCompilationAt
    (oldVisit : OldVisit) (index : Nat) :
    SourceNativeInquiryCompilationAt
      (CapacityU8RootAt oldVisit)
      (contributionCapacityU8RuntimeVisitAt oldVisit index)
      (contributionCapacityRevisedU7 oldVisit)
      (contributionCapacityRevisedCalculus oldVisit)
      (contributionCapacityRevisedTheory oldVisit) ()
      (contributionCapacityU8InquiryEventAt oldVisit index)
      (contributionCapacityU8GeneratedResidual oldVisit)
      (contributionCapacityU8RuntimeAuthorityAt oldVisit index) :=
  .answered (contributionCapacityU8AnswerFaceAt oldVisit index)
    (contributionCapacityU8AnswerConsumerAt oldVisit index)

def contributionCapacityU8TargetStateAt
    (oldVisit : OldVisit) (index : Nat) :
    RootInquiryStateAt (CapacityU8NAt oldVisit) (CapacityU8VAt oldVisit) where
  root := CapacityU8RootAt oldVisit
  visit := contributionCapacityU8RuntimeVisitAt oldVisit index
  U7 := contributionCapacityRevisedU7 oldVisit
  calculus := contributionCapacityRevisedCalculus oldVisit
  Query := Unit
  entryAt := fun _ => contributionCapacityU8GeneratedResidual oldVisit
  authorityAt := fun _ => contributionCapacityU8RuntimeAuthorityAt oldVisit index
  compilationProgramAt := fun _ =>
    { compile := fun _ => contributionCapacityU8AnsweredCompilationAt
        oldVisit index }
  compilationFaceAt := fun _ =>
    { projection := ContributionCapacityU8Projection.inquiry
      active := PUnit.unit
      classifier_eq := rfl
      project_heq := HEq.rfl }
  u7RootDisposition_commutes := by
    intro _query _obstruction _audit audit_eq
    cases audit_eq

def contributionCapacityU8TargetEngineStateAt
    (oldVisit : OldVisit) (index : Nat) :=
  RootInquiryEngineStateAt.create
    (contributionCapacityU8TargetStateAt oldVisit index)

def contributionCapacityU8TargetPresentationAt
    (oldVisit : OldVisit) (index : Nat) : RootInquiryStatePresentation where
  N := CapacityU8NAt oldVisit
  V := CapacityU8VAt oldVisit
  state := contributionCapacityU8TargetEngineStateAt oldVisit index

@[simp] theorem contributionCapacityU8TargetState_compiles_answered
    (oldVisit : OldVisit) (index : Nat) :
    (contributionCapacityU8TargetStateAt oldVisit index).compileInquiry () =
      .answered (contributionCapacityU8AnswerFaceAt oldVisit index)
        (contributionCapacityU8AnswerConsumerAt oldVisit index) :=
  rfl

theorem contributionCapacityU8Authority_one_is_coreTarget
    (oldVisit : OldVisit) :
    HEq (contributionCapacityU8ResidualAuthorityAt oldVisit 1)
      (TypedSemanticWorldNetworkU8Lifecycle.newFirstWriteTargetAuthority
        (contributionCapacityFieldGroundedRevisionAt oldVisit)) :=
  HEq.rfl

end
end M14SourceGeneratedContributionCapacityU8TargetState
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityU8TargetState.contributionCapacityU8TargetState_compiles_answered
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityU8TargetState.contributionCapacityU8Authority_one_is_coreTarget
