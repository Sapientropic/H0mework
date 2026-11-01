import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Runtime.SourceGeneratedPostSettlementObserverSubmissionRevisedAuthority
import H0mework.Versions.Rdf421ff6.Foundation.Runtime.Inquiry

/-!
# Named runtime consuming the observer-submission U8 core

The initial state is the exact old joint-root Payment visit.  Its fixed
inquiry compiler generates the submission-augmented richer revised core.  The first
macro successor is the revised first write's generated target, and every
later tick follows that revised root's answer-and-next.  The runtime stores no
schedule, sibling compiler, alternative core or completed future.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedPostSettlementObserverSubmissionU8

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open ConstructiveRoot.TypedSemanticWorldNetworkU8Lifecycle
open M9ProofCarryingRenewalInquiryRoot
open M9ProofCarryingRenewalU8Failure
open M14SourceGeneratedContributionMergeActionSource

def revisedAnswerFaceAt (oldVisit : OldVisit) (sourceIndex boundary index : Nat) :
    SourceNativeRootSemanticFaceAt
      (revisedLivingRootAt oldVisit sourceIndex boundary)
      (revisedTemporalVisitAt oldVisit sourceIndex boundary index) where
  projection := .inherited .answer
  active := PUnit.unit
  classifier_eq := rfl

def revisedAnswerConsumerAt (oldVisit : OldVisit)
    (sourceIndex boundary index : Nat) :
    SourceNativeInquiryAnswerConsumerAt ()
      (revisedInquiryEventAt oldVisit sourceIndex boundary index)
      (revisedInquiryEntryAt oldVisit sourceIndex boundary index)
      (revisedAnswerFaceAt oldVisit sourceIndex boundary index) where
  projection := .inherited .consumer
  active := PUnit.unit
  classifier_eq := rfl
  project_heq := HEq.rfl

abbrev revisedInquiryCompilationAt (oldVisit : OldVisit)
    (sourceIndex boundary index : Nat) :
    SourceNativeInquiryCompilationAt
      (revisedLivingRootAt oldVisit sourceIndex boundary)
      (revisedTemporalVisitAt oldVisit sourceIndex boundary index)
      (revisedU7At oldVisit sourceIndex boundary)
      (revisedCalculusAt oldVisit sourceIndex boundary)
      (revisedTheoryAt oldVisit sourceIndex boundary) ()
      (revisedInquiryEventAt oldVisit sourceIndex boundary index)
      (revisedInquiryEntryAt oldVisit sourceIndex boundary index)
      (revisedInquiryAuthorityAt oldVisit sourceIndex boundary index) :=
  .answered (revisedAnswerFaceAt oldVisit sourceIndex boundary index)
    (revisedAnswerConsumerAt oldVisit sourceIndex boundary index)

def revisedCompilationProgramAt (oldVisit : OldVisit)
    (sourceIndex boundary index : Nat) :
    SourceNativeInquiryCompilationProgramAt
      (revisedLivingRootAt oldVisit sourceIndex boundary)
      (revisedTemporalVisitAt oldVisit sourceIndex boundary index)
      (revisedU7At oldVisit sourceIndex boundary)
      (revisedCalculusAt oldVisit sourceIndex boundary)
      (revisedTheoryAt oldVisit sourceIndex boundary) ()
      (revisedInquiryEventAt oldVisit sourceIndex boundary index)
      (revisedInquiryEntryAt oldVisit sourceIndex boundary index)
      (revisedInquiryAuthorityAt oldVisit sourceIndex boundary index) where
  compile := fun _exactEvent =>
    revisedInquiryCompilationAt oldVisit sourceIndex boundary index

def revisedCompilationFaceAt (oldVisit : OldVisit)
    (sourceIndex boundary index : Nat) :
    SourceNativeRootInquiryCompilationFaceCoreAt
      (revisedLivingRootAt oldVisit sourceIndex boundary)
      (revisedTemporalVisitAt oldVisit sourceIndex boundary index) ()
      (revisedInquiryEventAt oldVisit sourceIndex boundary index)
      (revisedInquiryEntryAt oldVisit sourceIndex boundary index)
      (revisedInquiryAuthorityAt oldVisit sourceIndex boundary index)
      (revisedCompilationProgramAt oldVisit sourceIndex boundary index
        ).generate.output where
  projection := .inherited .inquiry
  active := PUnit.unit
  classifier_eq := rfl
  project_heq := HEq.rfl

def revisedStateAt (oldVisit : OldVisit) (sourceIndex boundary index : Nat) :
    RootInquiryStateAt (NewNAt oldVisit sourceIndex boundary)
      (NewVAt oldVisit sourceIndex boundary) where
  root := revisedLivingRootAt oldVisit sourceIndex boundary
  visit := revisedTemporalVisitAt oldVisit sourceIndex boundary index
  U7 := revisedU7At oldVisit sourceIndex boundary
  calculus := revisedCalculusAt oldVisit sourceIndex boundary
  Query := Unit
  entryAt := fun _ => revisedInquiryEntryAt oldVisit sourceIndex boundary index
  authorityAt := fun _ =>
    revisedInquiryAuthorityAt oldVisit sourceIndex boundary index
  compilationProgramAt := fun _ =>
    revisedCompilationProgramAt oldVisit sourceIndex boundary index
  compilationFaceAt := fun _ =>
    revisedCompilationFaceAt oldVisit sourceIndex boundary index
  u7RootDisposition_commutes := by
    intro _query _obstruction _audit audit_eq
    cases audit_eq

def revisedPresentationAt (oldVisit : OldVisit)
    (sourceIndex boundary index : Nat) : RootInquiryStatePresentation where
  N := NewNAt oldVisit sourceIndex boundary
  V := NewVAt oldVisit sourceIndex boundary
  state := RootInquiryEngineStateAt.create
    (revisedStateAt oldVisit sourceIndex boundary index)

inductive RuntimeState
  | source
  | revised (index : Nat)

def processPresentationAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) : RuntimeState → RootInquiryStatePresentation
  | .source => sourcePresentationAt oldVisit sourceIndex boundary
  | .revised index =>
      revisedPresentationAt oldVisit sourceIndex boundary index

def erasedCurrentLabel (erased : AnyAuthoritativeRootCurrent) :
    Sigma fun Carrier : Type => Carrier :=
  ⟨erased.current.V.Current, erased.current.visit.current⟩

def expectedCurrentLabel : RuntimeState → Sigma fun Carrier : Type => Carrier
  | .source => ⟨Unit, ()⟩
  | .revised index => ⟨Nat, index⟩

theorem processPresentation_currentLabel_exact (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) (state : RuntimeState) :
    erasedCurrentLabel
        (processPresentationAt oldVisit sourceIndex boundary state).erase =
      expectedCurrentLabel state := by
  cases state with
  | source => rfl
  | revised index =>
      unfold erasedCurrentLabel processPresentationAt revisedPresentationAt
      dsimp [RootInquiryStatePresentation.erase, revisedStateAt]
      refine Sigma.ext rfl ?_
      exact heq_of_eq
        (revisedVisit_current_exact oldVisit sourceIndex boundary index)

theorem revisedPresentation_next_eq (oldVisit : OldVisit)
    (sourceIndex boundary index : Nat) :
    (revisedPresentationAt oldVisit sourceIndex boundary (index + 1)).erase =
      ⟨NewNAt oldVisit sourceIndex boundary,
        ((revisedStateAt oldVisit sourceIndex boundary index
          ).oldAnswerAndNext ()).nextCurrent⟩ :=
  congrArg
    (fun current : SourceNativeAuthoritativeRootCurrentAt
        (NewNAt oldVisit sourceIndex boundary) =>
      ({ N := NewNAt oldVisit sourceIndex boundary
         current := current } : AnyAuthoritativeRootCurrent))
    (revisedLivingRoot_generatedNextCurrentAt_eq oldVisit sourceIndex
      boundary index).symm

def processAt (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeInquiryEngineProcess.{0} where
  State := RuntimeState
  stateAt := fun state =>
    .active (processPresentationAt oldVisit sourceIndex boundary state)
  erase_injective := by
    intro left right leftState rightState leftActive rightActive equality
    cases leftActive
    cases rightActive
    cases left with
    | source =>
        cases right with
        | source => rfl
        | revised rightIndex =>
            have cardEquality := congrArg
              (fun erased : AnyAuthoritativeRootCurrent =>
                Nat.card erased.current.V.Current) equality
            change Nat.card Unit = Nat.card Nat at cardEquality
            simp at cardEquality
    | revised leftIndex =>
        cases right with
        | source =>
            have cardEquality := congrArg
              (fun erased : AnyAuthoritativeRootCurrent =>
                Nat.card erased.current.V.Current) equality
            change Nat.card Nat = Nat.card Unit at cardEquality
            simp at cardEquality
        | revised rightIndex =>
            have labelEquality := congrArg erasedCurrentLabel equality
            rw [processPresentation_currentLabel_exact oldVisit sourceIndex
                  boundary (.revised leftIndex),
              processPresentation_currentLabel_exact oldVisit sourceIndex
                  boundary (.revised rightIndex)] at labelEquality
            have indexEquality : leftIndex = rightIndex := by
              simpa [expectedCurrentLabel] using labelEquality
            cases indexEquality
            rfl
  initial := .source
  successorAt := by
    intro state query
    cases state with
    | source =>
        refine ⟨.revised 2, ?_, ?_⟩
        · change
            (revisedPresentationAt oldVisit sourceIndex boundary 2).erase =
              ⟨NewNAt oldVisit sourceIndex boundary,
                (ConstructiveRoot.TypedSemanticWorldNetworkU8Recovery.generatedNewTargetAnswerAndNext
                  (typedRevisionSourceAt oldVisit sourceIndex boundary)
                  ).nextCurrent⟩
          rfl
        · exact HEq.rfl
    | revised index =>
        change Unit at query
        cases query
        refine ⟨.revised (index + 1), ?_⟩
        exact RootInquiryProcessNode.active_directlyAnswered_successor_valid
          (revisedPresentationAt oldVisit sourceIndex boundary index)
          (revisedPresentationAt oldVisit sourceIndex boundary (index + 1))
          PUnit.unit
          (revisedAnswerFaceAt oldVisit sourceIndex boundary index)
          (revisedAnswerConsumerAt oldVisit sourceIndex boundary index)
          rfl
          (revisedPresentation_next_eq oldVisit sourceIndex boundary index)
          HEq.rfl

@[simp] theorem process_source_successor (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    ((processAt oldVisit sourceIndex boundary).successorAt .source ()).1 =
      .revised 2 :=
  rfl

@[simp] theorem process_revised_successor (oldVisit : OldVisit)
    (sourceIndex boundary index : Nat) :
    ((processAt oldVisit sourceIndex boundary).successorAt
      (.revised index) ()).1 = .revised (index + 1) :=
  rfl

def initialQueryAt (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ((processAt oldVisit sourceIndex boundary).stateAt
      (processAt oldVisit sourceIndex boundary).initial).Query :=
  ()

theorem initialQuery_unique (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (candidate : ((processAt oldVisit sourceIndex boundary).stateAt
      (processAt oldVisit sourceIndex boundary).initial).Query) :
    candidate = initialQueryAt oldVisit sourceIndex boundary := by
  cases candidate
  rfl

def nextQueryAt (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (state : RuntimeState)
    (query : ((processAt oldVisit sourceIndex boundary).stateAt state).Query) :
    ((processAt oldVisit sourceIndex boundary).stateAt
      ((processAt oldVisit sourceIndex boundary).successorAt state query).1
      ).Query := by
  cases state with
  | source =>
      change Unit at query
      cases query
      rw [process_source_successor oldVisit sourceIndex boundary]
      exact ()
  | revised index =>
      change Unit at query
      cases query
      rw [process_revised_successor oldVisit sourceIndex boundary index]
      exact ()

theorem nextQuery_unique (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (state : RuntimeState)
    (query : ((processAt oldVisit sourceIndex boundary).stateAt state).Query)
    (candidate : ((processAt oldVisit sourceIndex boundary).stateAt
      ((processAt oldVisit sourceIndex boundary).successorAt state query).1
      ).Query) :
    candidate = nextQueryAt oldVisit sourceIndex boundary state query := by
  cases state with
  | source =>
      change Unit at query
      cases query
      rw [process_source_successor oldVisit sourceIndex boundary] at candidate
      change Unit at candidate
      cases candidate
      rfl
  | revised index =>
      change Unit at query
      cases query
      rw [process_revised_successor oldVisit sourceIndex boundary index]
        at candidate
      change Unit at candidate
      cases candidate
      rfl

def runtimeAt (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeInquiryRuntime (processAt oldVisit sourceIndex boundary) where
  activationLaw := Engine.SourceNativeInquiryActivationLaw.ofUnique
    (initialQueryAt oldVisit sourceIndex boundary)
    (initialQuery_unique oldVisit sourceIndex boundary)
    (nextQueryAt oldVisit sourceIndex boundary)
    (nextQuery_unique oldVisit sourceIndex boundary)

def firstTickAt (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (runtimeAt oldVisit sourceIndex boundary).tickAt 0

@[simp] theorem firstTick_resolution_isExactCore (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    (firstTickAt oldVisit sourceIndex boundary).resolution =
      .revised RootInquiryU8CompletionRegression.obstruction
        RootInquiryU8CompletionRegression.u7Gate
        RootInquiryU8CompletionRegression.failure
        (generatedU8CoreAt oldVisit sourceIndex boundary) :=
  rfl

theorem runtimeConsumesExactCore (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    SourceNativeInquiryRuntime.CofaceRealizationResumptionAt
      (generatedU8CoreAt oldVisit sourceIndex boundary)
      (runtimeAt oldVisit sourceIndex boundary) 0 where
  contains_core := by
    rw [firstTick_resolution_isExactCore oldVisit sourceIndex boundary]
    exact HEq.rfl

theorem cofaceRealizationInstalled (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    SourceNativeInquiryRuntime.CofaceRealizationInstalledAt
      (failureFrontierAt oldVisit sourceIndex boundary)
      (realizationCandidateAt oldVisit sourceIndex boundary)
      (runtimeAt oldVisit sourceIndex boundary) 0 :=
  ⟨generatedU8CoreAt oldVisit sourceIndex boundary,
    realizationCertificationAt oldVisit sourceIndex boundary,
    runtimeConsumesExactCore oldVisit sourceIndex boundary⟩

theorem runtimeCore_unique (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) {Core : Type 11} {candidate : Core}
    (resumed : SourceNativeInquiryRuntime.CofaceRealizationResumptionAt
      candidate (runtimeAt oldVisit sourceIndex boundary) 0) :
    HEq candidate (generatedU8CoreAt oldVisit sourceIndex boundary) :=
  resumed.core_heq (runtimeConsumesExactCore oldVisit sourceIndex boundary)

theorem firstTick_next_is_revisedTarget (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    ((runtimeAt oldVisit sourceIndex boundary).stateAt 1).engine.node.erase =
      (firstTickAt oldVisit sourceIndex boundary).next.node.erase :=
  rfl

end
end M14SourceGeneratedPostSettlementObserverSubmissionU8
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverSubmissionU8.runtimeConsumesExactCore
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverSubmissionU8.cofaceRealizationInstalled
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverSubmissionU8.runtimeCore_unique
