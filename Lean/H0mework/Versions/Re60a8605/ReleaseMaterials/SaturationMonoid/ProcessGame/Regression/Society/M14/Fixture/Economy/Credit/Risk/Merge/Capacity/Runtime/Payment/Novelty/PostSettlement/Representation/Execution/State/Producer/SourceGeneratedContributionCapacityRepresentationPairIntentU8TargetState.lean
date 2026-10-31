import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Novelty.PostSettlement.Representation.Execution.Compilation.Producer.SourceGeneratedContributionCapacityRepresentationPairIntentU8Compilation

/-!
# Pair-intent U8 revised target state

The revised runtime follows the generated obstruction row of the canonical
coface root.  Temporal visits are generated recursively by that root.  The
runtime enters absolute visit two, after the initial first write and its exact
new-row answer-and-next, so the source U8 transition and revised ordinary
continuation remain two successive visits.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityRepresentationPairIntentU8TargetState

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open ConstructiveRoot.TypedSemanticWorldNetworkU8Lifecycle
open ConstructiveRoot.TypedSemanticWorldNetworkU8Recovery
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Lifecycle
open M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Compiler
open M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Root
open M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Revision

abbrev RepresentationIntentU8RootAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  representationIntentU8LivingRoot oldVisit sourceIndex boundary

abbrev RepresentationIntentU8RootVisitAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  RootVisit
    (RepresentationIntentU8RootAt oldVisit sourceIndex boundary
      ).toAuthoritativeRoot.toRoot

def representationIntentU8RootVisitAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    Nat → RepresentationIntentU8RootVisitAt oldVisit sourceIndex boundary
  | 0 =>
      (RepresentationIntentU8RootAt oldVisit sourceIndex boundary
        ).toAuthoritativeRoot.toRoot.initialVisit
  | index + 1 =>
      (representationIntentU8RootVisitAt oldVisit sourceIndex boundary index
        ).next rfl

def representationIntentU8TemporalVisitAt
    (oldVisit : OldVisit) (sourceIndex boundary index : Nat) :
    SourceNativeTemporalVisitAt
      (RepresentationIntentU8RootAt oldVisit sourceIndex boundary
        ).toAuthoritativeRoot.toLedgerRoot :=
  .finite
    (representationIntentU8RootVisitAt oldVisit sourceIndex boundary index)

@[simp] theorem representationIntentU8TemporalVisit_one_current_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (representationIntentU8TemporalVisitAt oldVisit sourceIndex boundary 1
      ).current = true :=
  rfl

@[simp] theorem representationIntentU8TemporalVisit_two_current_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (representationIntentU8TemporalVisitAt oldVisit sourceIndex boundary 2
      ).current = true :=
  rfl

theorem representationIntentU8NextEqAt
    (oldVisit : OldVisit) (sourceIndex boundary index : Nat) :
    ((RepresentationIntentU8RootAt oldVisit sourceIndex boundary
      ).toAuthoritativeRoot.toRoot.evolutionAt
        (representationIntentU8TemporalVisitAt oldVisit sourceIndex boundary
          index).current).nextCurrent? =
      some
        (representationIntentU8TemporalVisitAt oldVisit sourceIndex boundary
          (index + 1)).current :=
  rfl

theorem representationIntentU8GeneratedNextCurrent_exact
    (oldVisit : OldVisit) (sourceIndex boundary index : Nat) :
    (RepresentationIntentU8RootAt oldVisit sourceIndex boundary
      ).generatedNextCurrentAt
        (representationIntentU8TemporalVisitAt oldVisit sourceIndex boundary
          index) =
      ⟨RepresentationIntentU8VAt oldVisit sourceIndex boundary,
        representationIntentU8AuthoritativeRoot oldVisit sourceIndex boundary,
        representationIntentU8TemporalVisitAt oldVisit sourceIndex boundary
          (index + 1)⟩ := by
  cases index <;> rfl

def representationIntentU8InitialObstructionAuthority
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt
      (RepresentationIntentU8RootAt oldVisit sourceIndex boundary)
      (representationIntentU8TemporalVisitAt oldVisit sourceIndex boundary 0)
      (representationIntentU8GeneratedEntryAt oldVisit sourceIndex boundary) :=
  SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitialRow
    (RepresentationIntentU8RootAt oldVisit sourceIndex boundary)
    (representationIntentU8GeneratedEntryAt oldVisit sourceIndex boundary)
    (representationIntentU8GeneratedRow oldVisit sourceIndex boundary)

def representationIntentU8ObstructionAuthorityAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (index : Nat) →
      SourceNativeLivingTemporalCausalEntryAuthorityAt
        (RepresentationIntentU8RootAt oldVisit sourceIndex boundary)
        (representationIntentU8TemporalVisitAt oldVisit sourceIndex boundary
          index)
        (representationIntentU8GeneratedEntryAt oldVisit sourceIndex boundary)
  | 0 =>
      representationIntentU8InitialObstructionAuthority oldVisit sourceIndex
        boundary
  | index + 1 =>
      (representationIntentU8ObstructionAuthorityAt oldVisit sourceIndex
        boundary index).next
          (representationIntentU8NextEqAt oldVisit sourceIndex boundary index)

def representationIntentU8RuntimeVisitAt
    (oldVisit : OldVisit) (sourceIndex boundary index : Nat) :=
  representationIntentU8TemporalVisitAt oldVisit sourceIndex boundary index

abbrev representationIntentU8RuntimeAuthorityAt
    (oldVisit : OldVisit) (sourceIndex boundary index : Nat) :=
  representationIntentU8ObstructionAuthorityAt oldVisit sourceIndex boundary
    index

def representationIntentU8RevisedInquiryEventAt
    (oldVisit : OldVisit) (sourceIndex boundary index : Nat) :=
  ULift.up.{1, 0}
    ((RepresentationIntentU8RootAt oldVisit sourceIndex boundary).emitted
      (representationIntentU8RuntimeVisitAt oldVisit sourceIndex boundary
        index).current)

def representationIntentU8AnswerFaceAt
    (oldVisit : OldVisit) (sourceIndex boundary index : Nat) :
    SourceNativeRootSemanticFaceAt
      (RepresentationIntentU8RootAt oldVisit sourceIndex boundary)
      (representationIntentU8RuntimeVisitAt oldVisit sourceIndex boundary
        index) where
  projection := RepresentationIntentU8Projection.answer
  active := PUnit.unit
  classifier_eq := rfl

def representationIntentU8AnswerConsumerAt
    (oldVisit : OldVisit) (sourceIndex boundary index : Nat) :
    SourceNativeInquiryAnswerConsumerAt ()
      (representationIntentU8RevisedInquiryEventAt oldVisit sourceIndex
        boundary index)
      (representationIntentU8GeneratedEntryAt oldVisit sourceIndex boundary)
      (representationIntentU8AnswerFaceAt oldVisit sourceIndex boundary
        index) where
  projection := RepresentationIntentU8Projection.consumer (Fin.last 3)
  active := PUnit.unit
  classifier_eq := rfl
  project_heq := HEq.rfl

def representationIntentU8AnsweredCompilationAt
    (oldVisit : OldVisit) (sourceIndex boundary index : Nat) :
    SourceNativeInquiryCompilationAt
      (RepresentationIntentU8RootAt oldVisit sourceIndex boundary)
      (representationIntentU8RuntimeVisitAt oldVisit sourceIndex boundary
        index)
      (representationIntentU8RevisedU7 oldVisit sourceIndex boundary)
      (representationIntentU8RevisedCalculus oldVisit sourceIndex boundary)
      (representationIntentU8RevisedTheory oldVisit sourceIndex boundary) ()
      (representationIntentU8RevisedInquiryEventAt oldVisit sourceIndex
        boundary index)
      (representationIntentU8GeneratedEntryAt oldVisit sourceIndex boundary)
      (representationIntentU8RuntimeAuthorityAt oldVisit sourceIndex boundary
        index) :=
  .answered
    (representationIntentU8AnswerFaceAt oldVisit sourceIndex boundary index)
    (representationIntentU8AnswerConsumerAt oldVisit sourceIndex boundary
      index)

def representationIntentU8RevisedCompilationProgramAt
    (oldVisit : OldVisit) (sourceIndex boundary index : Nat) :
    SourceNativeInquiryCompilationProgramAt
      (RepresentationIntentU8RootAt oldVisit sourceIndex boundary)
      (representationIntentU8RuntimeVisitAt oldVisit sourceIndex boundary
        index)
      (representationIntentU8RevisedU7 oldVisit sourceIndex boundary)
      (representationIntentU8RevisedCalculus oldVisit sourceIndex boundary)
      (representationIntentU8RevisedTheory oldVisit sourceIndex boundary) ()
      (representationIntentU8RevisedInquiryEventAt oldVisit sourceIndex
        boundary index)
      (representationIntentU8GeneratedEntryAt oldVisit sourceIndex boundary)
      (representationIntentU8RuntimeAuthorityAt oldVisit sourceIndex boundary
        index) where
  compile := fun _ =>
    representationIntentU8AnsweredCompilationAt oldVisit sourceIndex boundary
      index

def representationIntentU8RevisedCompilationFaceAt
    (oldVisit : OldVisit) (sourceIndex boundary index : Nat) :
    SourceNativeRootInquiryCompilationFaceCoreAt
      (RepresentationIntentU8RootAt oldVisit sourceIndex boundary)
      (representationIntentU8RuntimeVisitAt oldVisit sourceIndex boundary
        index) ()
      (representationIntentU8RevisedInquiryEventAt oldVisit sourceIndex
        boundary index)
      (representationIntentU8GeneratedEntryAt oldVisit sourceIndex boundary)
      (representationIntentU8RuntimeAuthorityAt oldVisit sourceIndex boundary
        index)
      (representationIntentU8RevisedCompilationProgramAt oldVisit sourceIndex
        boundary index).generate.output where
  projection := RepresentationIntentU8Projection.inquiry
  active := PUnit.unit
  classifier_eq := rfl
  project_heq := HEq.rfl

def representationIntentU8TargetStateAt
    (oldVisit : OldVisit) (sourceIndex boundary index : Nat) :
    RootInquiryStateAt
      (RepresentationIntentU8NAt oldVisit sourceIndex boundary)
      (RepresentationIntentU8VAt oldVisit sourceIndex boundary) where
  root := RepresentationIntentU8RootAt oldVisit sourceIndex boundary
  visit :=
    representationIntentU8RuntimeVisitAt oldVisit sourceIndex boundary index
  U7 := representationIntentU8RevisedU7 oldVisit sourceIndex boundary
  calculus := representationIntentU8RevisedCalculus oldVisit sourceIndex boundary
  Query := Unit
  entryAt := fun _ =>
    representationIntentU8GeneratedEntryAt oldVisit sourceIndex boundary
  authorityAt := fun _ =>
    representationIntentU8RuntimeAuthorityAt oldVisit sourceIndex boundary
      index
  compilationProgramAt := fun _ =>
    representationIntentU8RevisedCompilationProgramAt oldVisit sourceIndex
      boundary index
  compilationFaceAt := fun _ =>
    representationIntentU8RevisedCompilationFaceAt oldVisit sourceIndex
      boundary index
  u7RootDisposition_commutes := by
    intro _query _obstruction _audit audit_eq
    cases audit_eq

def representationIntentU8TargetEngineStateAt
    (oldVisit : OldVisit) (sourceIndex boundary index : Nat) :=
  RootInquiryEngineStateAt.create
    (representationIntentU8TargetStateAt oldVisit sourceIndex boundary index)

def representationIntentU8TargetPresentationAt
    (oldVisit : OldVisit) (sourceIndex boundary index : Nat) :
    RootInquiryStatePresentation where
  N := RepresentationIntentU8NAt oldVisit sourceIndex boundary
  V := RepresentationIntentU8VAt oldVisit sourceIndex boundary
  state := representationIntentU8TargetEngineStateAt oldVisit sourceIndex
    boundary index

def representationIntentU8RevisedAnswerAndNextAt
    (oldVisit : OldVisit) (sourceIndex boundary index : Nat) :=
  (representationIntentU8TargetStateAt oldVisit sourceIndex boundary index
    ).oldAnswerAndNext ()

@[simp] theorem representationIntentU8TargetState_compiles_answered
    (oldVisit : OldVisit) (sourceIndex boundary index : Nat) :
    (representationIntentU8TargetStateAt oldVisit sourceIndex boundary index
      ).compileInquiry () =
      .answered
        (representationIntentU8AnswerFaceAt oldVisit sourceIndex boundary index)
        (representationIntentU8AnswerConsumerAt oldVisit sourceIndex boundary
          index) :=
  rfl

theorem representationIntentU8ObstructionAuthority_one_is_coreTarget
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    HEq
      (representationIntentU8ObstructionAuthorityAt oldVisit sourceIndex
        boundary 1)
      (newFirstWriteTargetAuthority
        (representationIntentFieldGroundedRevision oldVisit sourceIndex
          boundary)) :=
  HEq.rfl

theorem representationIntentU8RevisedAnswerAndNext_generatedNext_exact
    (oldVisit : OldVisit) (sourceIndex boundary index : Nat) :
    (representationIntentU8RevisedAnswerAndNextAt oldVisit sourceIndex boundary
      index).nextCurrent =
      ⟨RepresentationIntentU8VAt oldVisit sourceIndex boundary,
        representationIntentU8AuthoritativeRoot oldVisit sourceIndex boundary,
        representationIntentU8TemporalVisitAt oldVisit sourceIndex boundary
          (index + 1)⟩ :=
  representationIntentU8GeneratedNextCurrent_exact oldVisit sourceIndex
    boundary index

theorem representationIntentU8TargetPresentation_next_eq
    (oldVisit : OldVisit) (sourceIndex boundary index : Nat) :
    (representationIntentU8TargetPresentationAt oldVisit sourceIndex boundary
      (index + 1)).erase =
      ⟨RepresentationIntentU8NAt oldVisit sourceIndex boundary,
        (representationIntentU8RevisedAnswerAndNextAt oldVisit sourceIndex
          boundary index).nextCurrent⟩ :=
  congrArg
    (fun current : SourceNativeAuthoritativeRootCurrentAt
        (RepresentationIntentU8NAt oldVisit sourceIndex boundary) =>
      ({ N := RepresentationIntentU8NAt oldVisit sourceIndex boundary
         current := current } : AnyAuthoritativeRootCurrent))
    (representationIntentU8GeneratedNextCurrent_exact oldVisit sourceIndex
      boundary index).symm

theorem representationIntentU8TargetPresentation_two_is_generatedNext
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (representationIntentU8TargetPresentationAt oldVisit sourceIndex boundary
      2).erase =
      ⟨RepresentationIntentU8NAt oldVisit sourceIndex boundary,
        (generatedNewTargetAnswerAndNext
          (representationIntentFieldGroundedRevision oldVisit sourceIndex
            boundary)).nextCurrent⟩ :=
  rfl

end
end M14SourceGeneratedContributionCapacityRepresentationPairIntentU8TargetState
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentU8TargetState.representationIntentU8TargetState_compiles_answered
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentU8TargetState.representationIntentU8ObstructionAuthority_one_is_coreTarget
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentU8TargetState.representationIntentU8RevisedAnswerAndNext_generatedNext_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentU8TargetState.representationIntentU8TargetPresentation_next_eq
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentU8TargetState.representationIntentU8TargetPresentation_two_is_generatedNext
