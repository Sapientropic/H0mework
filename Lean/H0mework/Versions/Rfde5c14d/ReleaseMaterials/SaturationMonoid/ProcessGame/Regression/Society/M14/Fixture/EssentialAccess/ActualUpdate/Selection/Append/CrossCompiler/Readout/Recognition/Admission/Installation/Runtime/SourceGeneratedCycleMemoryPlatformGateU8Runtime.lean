import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.CrossCompiler.Readout.Recognition.Admission.Installation.Runtime.Authority.SourceGeneratedCycleMemoryPlatformGateRevisedAuthority
import H0mework.Versions.R2.Foundation.Runtime.Inquiry

/-!
# Runtime consuming the cycle-memory platform-gate U8 core

The initial state is the exact old joint-root Payment visit.  Its fixed
compiler generates the platform-gate richer core; the first macro successor
is that revision's generated target, and every later tick follows the same
revised root.  No future schedule, alternative core or sibling compiler is
stored.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedCycleMemoryPlatformGateU8

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open ConstructiveRoot.TypedSemanticWorldNetworkU8Lifecycle
open M9ProofCarryingRenewalInquiryRoot
open M9ProofCarryingRenewalU8Failure
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedPostSettlementObserverSubmissionU8

def platformGateRevisedAnswerFaceAt (oldVisit : OldVisit)
    (sourceIndex boundary index : Nat) :
    SourceNativeRootSemanticFaceAt
      (platformGateRevisedLivingRootAt oldVisit sourceIndex boundary)
      (platformGateRevisedTemporalVisitAt oldVisit sourceIndex boundary index) where
  projection := .inherited (.inherited .answer)
  active := PUnit.unit
  classifier_eq := rfl

def platformGateRevisedAnswerConsumerAt (oldVisit : OldVisit)
    (sourceIndex boundary index : Nat) :
    SourceNativeInquiryAnswerConsumerAt ()
      (platformGateRevisedInquiryEventAt oldVisit sourceIndex boundary index)
      (platformGateRevisedInquiryEntryAt oldVisit sourceIndex boundary index)
      (platformGateRevisedAnswerFaceAt oldVisit sourceIndex boundary index) where
  projection := .inherited (.inherited .consumer)
  active := PUnit.unit
  classifier_eq := rfl
  project_heq := HEq.rfl

abbrev platformGateRevisedInquiryCompilationAt (oldVisit : OldVisit)
    (sourceIndex boundary index : Nat) :
    SourceNativeInquiryCompilationAt
      (platformGateRevisedLivingRootAt oldVisit sourceIndex boundary)
      (platformGateRevisedTemporalVisitAt oldVisit sourceIndex boundary index)
      (platformGateRevisedU7At oldVisit sourceIndex boundary)
      (platformGateRevisedCalculusAt oldVisit sourceIndex boundary)
      (platformGateRevisedTheoryAt oldVisit sourceIndex boundary) ()
      (platformGateRevisedInquiryEventAt oldVisit sourceIndex boundary index)
      (platformGateRevisedInquiryEntryAt oldVisit sourceIndex boundary index)
      (platformGateRevisedInquiryAuthorityAt oldVisit sourceIndex boundary
        index) :=
  .answered
    (platformGateRevisedAnswerFaceAt oldVisit sourceIndex boundary index)
    (platformGateRevisedAnswerConsumerAt oldVisit sourceIndex boundary index)

def platformGateRevisedCompilationProgramAt (oldVisit : OldVisit)
    (sourceIndex boundary index : Nat) :
    SourceNativeInquiryCompilationProgramAt
      (platformGateRevisedLivingRootAt oldVisit sourceIndex boundary)
      (platformGateRevisedTemporalVisitAt oldVisit sourceIndex boundary index)
      (platformGateRevisedU7At oldVisit sourceIndex boundary)
      (platformGateRevisedCalculusAt oldVisit sourceIndex boundary)
      (platformGateRevisedTheoryAt oldVisit sourceIndex boundary) ()
      (platformGateRevisedInquiryEventAt oldVisit sourceIndex boundary index)
      (platformGateRevisedInquiryEntryAt oldVisit sourceIndex boundary index)
      (platformGateRevisedInquiryAuthorityAt oldVisit sourceIndex boundary
        index) where
  compile := fun _exactEvent =>
    platformGateRevisedInquiryCompilationAt oldVisit sourceIndex boundary
      index

def platformGateRevisedCompilationFaceAt (oldVisit : OldVisit)
    (sourceIndex boundary index : Nat) :
    SourceNativeRootInquiryCompilationFaceCoreAt
      (platformGateRevisedLivingRootAt oldVisit sourceIndex boundary)
      (platformGateRevisedTemporalVisitAt oldVisit sourceIndex boundary index)
      ()
      (platformGateRevisedInquiryEventAt oldVisit sourceIndex boundary index)
      (platformGateRevisedInquiryEntryAt oldVisit sourceIndex boundary index)
      (platformGateRevisedInquiryAuthorityAt oldVisit sourceIndex boundary
        index)
      (platformGateRevisedCompilationProgramAt oldVisit sourceIndex boundary
        index).generate.output where
  projection := .inherited (.inherited .inquiry)
  active := PUnit.unit
  classifier_eq := rfl
  project_heq := HEq.rfl

def platformGateRevisedStateAt (oldVisit : OldVisit)
    (sourceIndex boundary index : Nat) :
    RootInquiryStateAt
      (AugmentedNewNAt oldVisit sourceIndex boundary)
      (AugmentedNewVAt oldVisit sourceIndex boundary) where
  root := platformGateRevisedLivingRootAt oldVisit sourceIndex boundary
  visit := platformGateRevisedTemporalVisitAt oldVisit sourceIndex boundary
    index
  U7 := platformGateRevisedU7At oldVisit sourceIndex boundary
  calculus := platformGateRevisedCalculusAt oldVisit sourceIndex boundary
  Query := Unit
  entryAt := fun _ =>
    platformGateRevisedInquiryEntryAt oldVisit sourceIndex boundary index
  authorityAt := fun _ =>
    platformGateRevisedInquiryAuthorityAt oldVisit sourceIndex boundary index
  compilationProgramAt := fun _ =>
    platformGateRevisedCompilationProgramAt oldVisit sourceIndex boundary index
  compilationFaceAt := fun _ =>
    platformGateRevisedCompilationFaceAt oldVisit sourceIndex boundary index
  u7RootDisposition_commutes := by
    intro _query _obstruction _audit audit_eq
    cases audit_eq

def platformGateRevisedPresentationAt (oldVisit : OldVisit)
    (sourceIndex boundary index : Nat) : RootInquiryStatePresentation where
  N := AugmentedNewNAt oldVisit sourceIndex boundary
  V := AugmentedNewVAt oldVisit sourceIndex boundary
  state := RootInquiryEngineStateAt.create
    (platformGateRevisedStateAt oldVisit sourceIndex boundary index)

inductive PlatformGateRuntimeState
  | source
  | revised (index : Nat)

def platformGateProcessPresentationAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    PlatformGateRuntimeState → RootInquiryStatePresentation
  | .source =>
      platformGateSourcePresentationAt oldVisit sourceIndex boundary
  | .revised index =>
      platformGateRevisedPresentationAt oldVisit sourceIndex boundary index

def platformGateErasedCurrentLabel (erased : AnyAuthoritativeRootCurrent) :
    Sigma fun Carrier : Type => Carrier :=
  ⟨erased.current.V.Current, erased.current.visit.current⟩

def platformGateExpectedCurrentLabel :
    PlatformGateRuntimeState → Sigma fun Carrier : Type => Carrier
  | .source => ⟨Unit, ()⟩
  | .revised index => ⟨Nat, index⟩

theorem platformGateProcessPresentation_currentLabel_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (state : PlatformGateRuntimeState) :
    platformGateErasedCurrentLabel
        (platformGateProcessPresentationAt oldVisit sourceIndex boundary state
          ).erase =
      platformGateExpectedCurrentLabel state := by
  cases state with
  | source => rfl
  | revised index =>
      unfold platformGateErasedCurrentLabel
        platformGateProcessPresentationAt platformGateRevisedPresentationAt
      dsimp [RootInquiryStatePresentation.erase, platformGateRevisedStateAt]
      refine Sigma.ext rfl ?_
      exact heq_of_eq
        (platformGateRevisedVisit_current_exact oldVisit sourceIndex boundary
          index)

theorem platformGateRevisedPresentation_next_eq (oldVisit : OldVisit)
    (sourceIndex boundary index : Nat) :
    (platformGateRevisedPresentationAt oldVisit sourceIndex boundary
      (index + 1)).erase =
      ⟨AugmentedNewNAt oldVisit sourceIndex boundary,
        ((platformGateRevisedStateAt oldVisit sourceIndex boundary index
          ).oldAnswerAndNext ()).nextCurrent⟩ :=
  congrArg
    (fun current : SourceNativeAuthoritativeRootCurrentAt
        (AugmentedNewNAt oldVisit sourceIndex boundary) =>
      ({ N := AugmentedNewNAt oldVisit sourceIndex boundary
         current := current } : AnyAuthoritativeRootCurrent))
    (platformGateRevisedLivingRoot_generatedNextCurrentAt_eq oldVisit
      sourceIndex boundary index).symm

def platformGateProcessAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) : SourceNativeInquiryEngineProcess.{0} where
  State := PlatformGateRuntimeState
  stateAt := fun state =>
    .active
      (platformGateProcessPresentationAt oldVisit sourceIndex boundary state)
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
            have labelEquality := congrArg platformGateErasedCurrentLabel
              equality
            rw [platformGateProcessPresentation_currentLabel_exact oldVisit
                  sourceIndex boundary (.revised leftIndex),
              platformGateProcessPresentation_currentLabel_exact oldVisit
                  sourceIndex boundary (.revised rightIndex)] at labelEquality
            have indexEquality : leftIndex = rightIndex := by
              simpa [platformGateExpectedCurrentLabel] using labelEquality
            cases indexEquality
            rfl
  initial := .source
  successorAt := by
    intro state query
    cases state with
    | source =>
        refine ⟨.revised 2, ?_, ?_⟩
        · change
            (platformGateRevisedPresentationAt oldVisit sourceIndex boundary 2
              ).erase =
              ⟨AugmentedNewNAt oldVisit sourceIndex boundary,
                (ConstructiveRoot.TypedSemanticWorldNetworkU8Recovery.generatedNewTargetAnswerAndNext
                  (platformGateTypedRevisionSourceAt oldVisit sourceIndex
                    boundary)).nextCurrent⟩
          rfl
        · exact HEq.rfl
    | revised index =>
        change Unit at query
        cases query
        refine ⟨.revised (index + 1), ?_⟩
        exact RootInquiryProcessNode.active_directlyAnswered_successor_valid
          (platformGateRevisedPresentationAt oldVisit sourceIndex boundary
            index)
          (platformGateRevisedPresentationAt oldVisit sourceIndex boundary
            (index + 1))
          PUnit.unit
          (platformGateRevisedAnswerFaceAt oldVisit sourceIndex boundary index)
          (platformGateRevisedAnswerConsumerAt oldVisit sourceIndex boundary
            index)
          rfl
          (platformGateRevisedPresentation_next_eq oldVisit sourceIndex
            boundary index)
          HEq.rfl

@[simp] theorem platformGateProcess_source_successor (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    ((platformGateProcessAt oldVisit sourceIndex boundary).successorAt
      .source ()).1 = .revised 2 :=
  rfl

@[simp] theorem platformGateProcess_revised_successor (oldVisit : OldVisit)
    (sourceIndex boundary index : Nat) :
    ((platformGateProcessAt oldVisit sourceIndex boundary).successorAt
      (.revised index) ()).1 = .revised (index + 1) :=
  rfl

def platformGateInitialQueryAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    ((platformGateProcessAt oldVisit sourceIndex boundary).stateAt
      (platformGateProcessAt oldVisit sourceIndex boundary).initial).Query :=
  ()

theorem platformGateInitialQuery_unique (oldVisit : OldVisit)
    (sourceIndex boundary : Nat)
    (candidate : ((platformGateProcessAt oldVisit sourceIndex boundary).stateAt
      (platformGateProcessAt oldVisit sourceIndex boundary).initial).Query) :
    candidate = platformGateInitialQueryAt oldVisit sourceIndex boundary := by
  cases candidate
  rfl

def platformGateNextQueryAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) (state : PlatformGateRuntimeState)
    (query : ((platformGateProcessAt oldVisit sourceIndex boundary).stateAt
      state).Query) :
    ((platformGateProcessAt oldVisit sourceIndex boundary).stateAt
      ((platformGateProcessAt oldVisit sourceIndex boundary).successorAt
        state query).1).Query := by
  cases state with
  | source =>
      change Unit at query
      cases query
      rw [platformGateProcess_source_successor oldVisit sourceIndex boundary]
      exact ()
  | revised index =>
      change Unit at query
      cases query
      rw [platformGateProcess_revised_successor oldVisit sourceIndex boundary
        index]
      exact ()

theorem platformGateNextQuery_unique (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) (state : PlatformGateRuntimeState)
    (query : ((platformGateProcessAt oldVisit sourceIndex boundary).stateAt
      state).Query)
    (candidate : ((platformGateProcessAt oldVisit sourceIndex boundary).stateAt
      ((platformGateProcessAt oldVisit sourceIndex boundary).successorAt
        state query).1).Query) :
    candidate = platformGateNextQueryAt oldVisit sourceIndex boundary state
      query := by
  cases state with
  | source =>
      change Unit at query
      cases query
      rw [platformGateProcess_source_successor oldVisit sourceIndex boundary]
        at candidate
      change Unit at candidate
      cases candidate
      rfl
  | revised index =>
      change Unit at query
      cases query
      rw [platformGateProcess_revised_successor oldVisit sourceIndex boundary
        index] at candidate
      change Unit at candidate
      cases candidate
      rfl

def platformGateRuntimeAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    SourceNativeInquiryRuntime
      (platformGateProcessAt oldVisit sourceIndex boundary) where
  activationLaw := Engine.SourceNativeInquiryActivationLaw.ofUnique
    (platformGateInitialQueryAt oldVisit sourceIndex boundary)
    (platformGateInitialQuery_unique oldVisit sourceIndex boundary)
    (platformGateNextQueryAt oldVisit sourceIndex boundary)
    (platformGateNextQuery_unique oldVisit sourceIndex boundary)

def platformGateFirstTickAt (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :=
  (platformGateRuntimeAt oldVisit sourceIndex boundary).tickAt 0

@[simp] theorem platformGateFirstTick_resolution_isExactCore
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (platformGateFirstTickAt oldVisit sourceIndex boundary).resolution =
      .revised RootInquiryU8CompletionRegression.obstruction
        RootInquiryU8CompletionRegression.u7Gate
        RootInquiryU8CompletionRegression.failure
        (platformGateU8CoreAt oldVisit sourceIndex boundary) :=
  rfl

theorem platformGateRuntimeConsumesExactCore (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    SourceNativeInquiryRuntime.CofaceRealizationResumptionAt
      (platformGateU8CoreAt oldVisit sourceIndex boundary)
      (platformGateRuntimeAt oldVisit sourceIndex boundary) 0 where
  contains_core := by
    rw [platformGateFirstTick_resolution_isExactCore oldVisit sourceIndex
      boundary]
    exact HEq.rfl

theorem platformGateCofaceRealizationInstalled (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    SourceNativeInquiryRuntime.CofaceRealizationInstalledAt
      (platformGateFailureFrontierAt oldVisit sourceIndex boundary)
      (platformGateRealizationCandidateAt oldVisit sourceIndex boundary)
      (platformGateRuntimeAt oldVisit sourceIndex boundary) 0 :=
  ⟨platformGateU8CoreAt oldVisit sourceIndex boundary,
    platformGateRealizationCertificationAt oldVisit sourceIndex boundary,
    platformGateRuntimeConsumesExactCore oldVisit sourceIndex boundary⟩

theorem platformGateRuntimeCore_unique (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) {Core : Type 11} {candidate : Core}
    (resumed : SourceNativeInquiryRuntime.CofaceRealizationResumptionAt
      candidate (platformGateRuntimeAt oldVisit sourceIndex boundary) 0) :
    HEq candidate (platformGateU8CoreAt oldVisit sourceIndex boundary) :=
  resumed.core_heq
    (platformGateRuntimeConsumesExactCore oldVisit sourceIndex boundary)

theorem platformGateFirstTick_next_is_revisedTarget (oldVisit : OldVisit)
    (sourceIndex boundary : Nat) :
    ((platformGateRuntimeAt oldVisit sourceIndex boundary).stateAt 1
      ).engine.node.erase =
      (platformGateFirstTickAt oldVisit sourceIndex boundary).next.node.erase :=
  rfl

end
end M14SourceGeneratedCycleMemoryPlatformGateU8
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCycleMemoryPlatformGateU8.platformGateRuntimeConsumesExactCore
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCycleMemoryPlatformGateU8.platformGateCofaceRealizationInstalled
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCycleMemoryPlatformGateU8.platformGateRuntimeCore_unique
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCycleMemoryPlatformGateU8.platformGateFirstTick_next_is_revisedTarget
