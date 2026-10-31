import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Novelty.PostSettlement.Representation.Execution.State.Producer.SourceGeneratedContributionCapacityRepresentationPairIntentU8TargetState
import H0mework.Foundation.Runtime.Inquiry

/-!
# Pair-intent canonical self-U8 runtime

One process begins at the exact active pair-intent occurrence, consumes its
installed U8 compilation, and enters absolute coface visit two.  Later states
follow the same revised root's generated answer-and-next chain.  State
injectivity observes the fixed projection inventory and already-generated
temporal history; it stores no failure schedule, second runtime, or future.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Runtime

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open ConstructiveRoot.TypedSemanticWorldNetworkU8Recovery
open Renewal
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityRepresentationClaimWorld
open M14SourceGeneratedContributionCapacityRepresentationPairIntentTheory
open M14SourceGeneratedContributionCapacityRepresentationPairIntentRoot
open M14SourceGeneratedContributionCapacityRepresentationPairIntentRootedFailure
open M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Lifecycle
open M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Root
open M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Revision
open M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Compilation
open M14SourceGeneratedContributionCapacityRepresentationPairIntentU8TargetState

def representationIntentReachableDepth
    {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
    {root : RootClosure N V} {current : V.Current} :
    root.ReachableAt current → Nat
  | .initial => 0
  | .step prior _nextEq => representationIntentReachableDepth prior + 1

def representationIntentTemporalDepth
    {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
    {root : SourceNativeLedgerRootClosure N V}
    (visit : SourceNativeTemporalVisitAt root) : Nat :=
  match visit.history with
  | .finite history => representationIntentReachableDepth history
  | .postCofinal _history => 0

def representationIntentErasedRuntimeLabel
    (erased : AnyAuthoritativeRootCurrent) : Nat × Nat :=
  (Nat.card erased.current.root.source.projectionLaw.Projection,
    representationIntentTemporalDepth erased.current.visit)

def representationIntentSourceProjectionEquivFin5 :
    SourceNativeRenewalProjection RepresentationIntentProjection ≃ Fin 5 where
  toFun
    | .renewal => 0
    | .inherited .ledger => 1
    | .inherited .intent => 2
    | .inherited .failure => 3
    | .inherited .inquiry => 4
  invFun :=
    Fin.cases .renewal
      (Fin.cases (.inherited .ledger)
        (Fin.cases (.inherited .intent)
          (Fin.cases (.inherited .failure)
            (fun _ => .inherited .inquiry))))
  left_inv projection := by
    cases projection with
    | renewal => rfl
    | inherited inherited => cases inherited <;> rfl
  right_inv index := by fin_cases index <;> rfl

theorem representationIntentSourceProjection_card :
    Nat.card (SourceNativeRenewalProjection RepresentationIntentProjection) =
      5 := by
  rw [Nat.card_congr representationIntentSourceProjectionEquivFin5]
  simp

def representationIntentU8ProjectionEquivFin7 :
    RepresentationIntentU8Projection ≃ Fin 7 where
  toFun
    | .ledgerLifecycle => 0
    | .inquiry => 1
    | .answer => 2
    | .consumer index => ⟨index.val + 3, by omega⟩
  invFun :=
    Fin.cases .ledgerLifecycle
      (Fin.cases .inquiry
        (Fin.cases .answer (fun index => .consumer index)))
  left_inv projection := by
    cases projection with
    | ledgerLifecycle => rfl
    | inquiry => rfl
    | answer => rfl
    | consumer index => fin_cases index <;> rfl
  right_inv index := by fin_cases index <;> rfl

theorem representationIntentU8Projection_card :
    Nat.card RepresentationIntentU8Projection = 7 := by
  rw [Nat.card_congr representationIntentU8ProjectionEquivFin7]
  simp

theorem representationIntentU8TemporalDepth_exact
    (oldVisit : OldVisit) (sourceIndex boundary index : Nat) :
    representationIntentTemporalDepth
        (representationIntentU8TemporalVisitAt oldVisit sourceIndex boundary
          index) = index := by
  induction index with
  | zero => rfl
  | succ index inductionHypothesis =>
      change
        representationIntentReachableDepth
            (representationIntentU8RootVisitAt oldVisit sourceIndex boundary
              index).history + 1 =
          index + 1
      exact congrArg (fun depth => depth + 1) inductionHypothesis

inductive RepresentationIntentU8RuntimeState
  | source
  | revised (index : Nat)

def representationIntentU8ProcessPresentation
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    RepresentationIntentU8RuntimeState → RootInquiryStatePresentation
  | .source =>
      representationIntentU8SourcePresentation oldVisit sourceIndex boundary
  | .revised index =>
      representationIntentU8TargetPresentationAt oldVisit sourceIndex boundary
        index

def representationIntentU8ExpectedRuntimeLabel
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    RepresentationIntentU8RuntimeState → Nat × Nat
  | .source =>
      (5, representationIntentTemporalDepth
        (InstalledRepresentationIntentVisitAt oldVisit sourceIndex boundary))
  | .revised index => (7, index)

theorem representationIntentU8ProcessPresentation_label_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (state : RepresentationIntentU8RuntimeState) :
    representationIntentErasedRuntimeLabel
        (representationIntentU8ProcessPresentation oldVisit sourceIndex
          boundary state).erase =
      representationIntentU8ExpectedRuntimeLabel oldVisit sourceIndex boundary
        state := by
  cases state with
  | source =>
      change
        (Nat.card
            (SourceNativeRenewalProjection RepresentationIntentProjection),
          representationIntentTemporalDepth
            (InstalledRepresentationIntentVisitAt oldVisit sourceIndex
              boundary)) =
        (5, representationIntentTemporalDepth
          (InstalledRepresentationIntentVisitAt oldVisit sourceIndex boundary))
      rw [representationIntentSourceProjection_card]
  | revised index =>
      change
        (Nat.card RepresentationIntentU8Projection,
          representationIntentTemporalDepth
            (representationIntentU8TemporalVisitAt oldVisit sourceIndex
              boundary index)) =
          (7, index)
      rw [representationIntentU8Projection_card,
        representationIntentU8TemporalDepth_exact oldVisit sourceIndex
          boundary index]

def representationIntentU8Process
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeInquiryEngineProcess.{0} where
  State := RepresentationIntentU8RuntimeState
  stateAt := fun state =>
    .active
      (representationIntentU8ProcessPresentation oldVisit sourceIndex boundary
        state)
  erase_injective := by
    intro left right leftState rightState leftActive rightActive equality
    cases leftActive
    cases rightActive
    have labelEquality :=
      congrArg representationIntentErasedRuntimeLabel equality
    rw [representationIntentU8ProcessPresentation_label_exact oldVisit
          sourceIndex boundary left,
      representationIntentU8ProcessPresentation_label_exact oldVisit
        sourceIndex boundary right] at labelEquality
    cases left with
    | source =>
        cases right with
        | source => rfl
        | revised rightIndex =>
            have impossible : (5 : Nat) = 7 :=
              congrArg Prod.fst labelEquality
            omega
    | revised leftIndex =>
        cases right with
        | source =>
            have impossible : (7 : Nat) = 5 :=
              congrArg Prod.fst labelEquality
            omega
        | revised rightIndex =>
            have indexEquality : leftIndex = rightIndex :=
              congrArg Prod.snd labelEquality
            cases indexEquality
            rfl
  initial := .source
  successorAt := by
    intro state query
    cases state with
    | source =>
        change Unit at query
        cases query
        refine ⟨.revised 2, ?_, ?_⟩
        · exact representationIntentU8TargetPresentation_two_is_generatedNext
            oldVisit sourceIndex boundary
        · exact HEq.rfl
    | revised index =>
        change Unit at query
        cases query
        refine ⟨.revised (index + 1), ?_⟩
        exact RootInquiryProcessNode.active_directlyAnswered_successor_valid
          (representationIntentU8TargetPresentationAt oldVisit sourceIndex
            boundary index)
          (representationIntentU8TargetPresentationAt oldVisit sourceIndex
            boundary (index + 1))
          PUnit.unit
          (representationIntentU8AnswerFaceAt oldVisit sourceIndex boundary
            index)
          (representationIntentU8AnswerConsumerAt oldVisit sourceIndex boundary
            index)
          rfl
          (representationIntentU8TargetPresentation_next_eq oldVisit
            sourceIndex boundary index)
          HEq.rfl

@[simp] theorem representationIntentU8Process_source_successor
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ((representationIntentU8Process oldVisit sourceIndex boundary).successorAt
      .source ()).1 = .revised 2 :=
  rfl

@[simp] theorem representationIntentU8Process_revised_successor
    (oldVisit : OldVisit) (sourceIndex boundary index : Nat) :
    ((representationIntentU8Process oldVisit sourceIndex boundary).successorAt
      (.revised index) ()).1 = .revised (index + 1) :=
  rfl

def representationIntentU8InitialQuery
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ((representationIntentU8Process oldVisit sourceIndex boundary).stateAt
      (representationIntentU8Process oldVisit sourceIndex boundary
        ).initial).Query :=
  ()

theorem representationIntentU8InitialQuery_unique
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (candidate :
      ((representationIntentU8Process oldVisit sourceIndex boundary).stateAt
        (representationIntentU8Process oldVisit sourceIndex boundary
          ).initial).Query) :
    candidate =
      representationIntentU8InitialQuery oldVisit sourceIndex boundary := by
  cases candidate
  rfl

def representationIntentU8NextQuery
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (state : RepresentationIntentU8RuntimeState)
    (query : ((representationIntentU8Process oldVisit sourceIndex boundary
      ).stateAt state).Query) :
    ((representationIntentU8Process oldVisit sourceIndex boundary).stateAt
      ((representationIntentU8Process oldVisit sourceIndex boundary
        ).successorAt state query).1).Query := by
  cases state with
  | source =>
      change Unit at query
      cases query
      rw [representationIntentU8Process_source_successor oldVisit sourceIndex
        boundary]
      exact ()
  | revised index =>
      change Unit at query
      cases query
      rw [representationIntentU8Process_revised_successor oldVisit sourceIndex
        boundary index]
      exact ()

theorem representationIntentU8NextQuery_unique
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (state : RepresentationIntentU8RuntimeState)
    (query : ((representationIntentU8Process oldVisit sourceIndex boundary
      ).stateAt state).Query)
    (candidate :
      ((representationIntentU8Process oldVisit sourceIndex boundary).stateAt
        ((representationIntentU8Process oldVisit sourceIndex boundary
          ).successorAt state query).1).Query) :
    candidate =
      representationIntentU8NextQuery oldVisit sourceIndex boundary state
        query := by
  cases state with
  | source =>
      change Unit at query
      cases query
      rw [representationIntentU8Process_source_successor oldVisit sourceIndex
        boundary] at candidate
      change Unit at candidate
      cases candidate
      rfl
  | revised index =>
      change Unit at query
      cases query
      rw [representationIntentU8Process_revised_successor oldVisit sourceIndex
        boundary index] at candidate
      change Unit at candidate
      cases candidate
      rfl

def representationIntentU8Runtime
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeInquiryRuntime
      (representationIntentU8Process oldVisit sourceIndex boundary) where
  activationLaw := Engine.SourceNativeInquiryActivationLaw.ofUnique
    (representationIntentU8InitialQuery oldVisit sourceIndex boundary)
    (representationIntentU8InitialQuery_unique oldVisit sourceIndex boundary)
    (representationIntentU8NextQuery oldVisit sourceIndex boundary)
    (representationIntentU8NextQuery_unique oldVisit sourceIndex boundary)

private theorem representationIntentU8Process_revised_successor_node
    (oldVisit : OldVisit) (sourceIndex boundary index : Nat)
    (state : RepresentationIntentU8RuntimeState)
    (state_eq : state = .revised index)
    (query :
      ((representationIntentU8Process oldVisit sourceIndex boundary).stateAt
        state).Query) :
    (representationIntentU8Process oldVisit sourceIndex boundary).stateAt
        ((representationIntentU8Process oldVisit sourceIndex boundary
          ).successorAt state query).1 =
      .active
        (representationIntentU8TargetPresentationAt oldVisit sourceIndex
          boundary (index + 1)) := by
  subst state
  change Unit at query
  cases query
  rfl

private theorem representationIntentU8Runtime_revisedState_next
    (oldVisit : OldVisit) (sourceIndex boundary index : Nat)
    (state :
      (representationIntentU8Runtime oldVisit sourceIndex boundary).State)
    (active : state.engine.node =
      .active
        (representationIntentU8TargetPresentationAt oldVisit sourceIndex
          boundary index)) :
    state.tick.next.node =
      .active
        (representationIntentU8TargetPresentationAt oldVisit sourceIndex
          boundary (index + 1)) := by
  have hiddenState_eq :=
    (representationIntentU8Process oldVisit sourceIndex boundary
      ).erase_injective (right := .revised index) active rfl rfl
  exact
    representationIntentU8Process_revised_successor_node oldVisit sourceIndex
      boundary index _ hiddenState_eq state.activation.query

@[simp] theorem representationIntentU8Runtime_stateAt_succ_node_exact
    (oldVisit : OldVisit) (sourceIndex boundary depth : Nat) :
    ((representationIntentU8Runtime oldVisit sourceIndex boundary).stateAt
      (depth + 1)).engine.node =
      .active
        (representationIntentU8TargetPresentationAt oldVisit sourceIndex
          boundary (depth + 2)) := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      rw [SourceNativeInquiryRuntime.stateAt_succ_engine]
      simpa [Nat.add_assoc] using
        representationIntentU8Runtime_revisedState_next oldVisit sourceIndex
          boundary (depth + 2)
          ((representationIntentU8Runtime oldVisit sourceIndex boundary).stateAt
            (depth + 1)) inductionHypothesis

@[simp] theorem representationIntentU8Runtime_stateAt_succ_exact
    (oldVisit : OldVisit) (sourceIndex boundary depth : Nat) :
    ((representationIntentU8Runtime oldVisit sourceIndex boundary).stateAt
      (depth + 1)).engine.node.erase =
      (representationIntentU8TargetPresentationAt oldVisit sourceIndex
        boundary (depth + 2)).erase := by
  exact congrArg RootInquiryProcessNode.erase
    (representationIntentU8Runtime_stateAt_succ_node_exact oldVisit sourceIndex
      boundary depth)

def representationIntentU8FirstTick
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (representationIntentU8Runtime oldVisit sourceIndex boundary).tickAt 0

@[simp] theorem representationIntentU8FirstTick_resolution_isExactCore
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (representationIntentU8FirstTick oldVisit sourceIndex boundary).resolution =
      .revised
        (generatedRepresentationObstructionAt oldVisit sourceIndex boundary)
        (representationIntentU7GateAt oldVisit sourceIndex boundary)
        (representationPairIntentFailureAt oldVisit sourceIndex boundary)
        (representationIntentGeneratedU8Core oldVisit sourceIndex boundary) :=
  rfl

theorem representationIntentU8Runtime_consumesExactCore
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeInquiryRuntime.CofaceRealizationResumptionAt
      (representationIntentGeneratedU8Core oldVisit sourceIndex boundary)
      (representationIntentU8Runtime oldVisit sourceIndex boundary) 0 where
  contains_core := by
    rw [representationIntentU8FirstTick_resolution_isExactCore oldVisit
      sourceIndex boundary]
    exact HEq.rfl

theorem representationIntentU8CofaceRealization_installed
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeInquiryRuntime.CofaceRealizationInstalledAt
      (representationIntentFailureFrontier oldVisit sourceIndex boundary)
      (representationIntentCofaceRealizationCandidate oldVisit sourceIndex
        boundary)
      (representationIntentU8Runtime oldVisit sourceIndex boundary) 0 :=
  ⟨representationIntentGeneratedU8Core oldVisit sourceIndex boundary,
    representationIntentCofaceRealizationCertification oldVisit sourceIndex
      boundary,
    representationIntentU8Runtime_consumesExactCore oldVisit sourceIndex
      boundary⟩

theorem representationIntentU8Runtime_core_unique
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    {Core : Type 11} {candidate : Core}
    (resumed : SourceNativeInquiryRuntime.CofaceRealizationResumptionAt
      candidate
      (representationIntentU8Runtime oldVisit sourceIndex boundary) 0) :
    HEq candidate
      (representationIntentGeneratedU8Core oldVisit sourceIndex boundary) :=
  resumed.core_heq
    (representationIntentU8Runtime_consumesExactCore oldVisit sourceIndex
      boundary)

theorem representationIntentU8FirstTick_next_isRevisedCofaceTarget
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ((representationIntentU8Runtime oldVisit sourceIndex boundary).stateAt 1
      ).engine.node.erase =
      (representationIntentU8TargetPresentationAt oldVisit sourceIndex boundary
        2).erase :=
  rfl

theorem representationIntentU8FirstRevisedTick_generatesNext
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ((representationIntentU8Runtime oldVisit sourceIndex boundary).stateAt 2
      ).engine.node.erase =
      ⟨RepresentationIntentU8NAt oldVisit sourceIndex boundary,
        (representationIntentU8RevisedAnswerAndNextAt oldVisit sourceIndex
          boundary 2).nextCurrent⟩ := by
  change
    (representationIntentU8TargetPresentationAt oldVisit sourceIndex boundary
      3).erase =
      ⟨RepresentationIntentU8NAt oldVisit sourceIndex boundary,
        (representationIntentU8RevisedAnswerAndNextAt oldVisit sourceIndex
          boundary 2).nextCurrent⟩
  exact representationIntentU8TargetPresentation_next_eq oldVisit sourceIndex
    boundary 2

/-- Every positive finite runtime depth is generated by the preceding exact
tick and remains inquiry-active at the corresponding revised visit.  The
natural number indexes the recursively generated `stateAt`; it is not a
preinstalled table of future currents. -/
theorem representationIntentU8EveryFiniteDepth_remainsInquiryActive
    (oldVisit : OldVisit) (sourceIndex boundary depth : Nat) :
    Nonempty
      ((representationIntentU8Runtime oldVisit sourceIndex boundary).stateAt
        (depth + 1)).engine.Query := by
  change Nonempty
    (((representationIntentU8Runtime oldVisit sourceIndex boundary).stateAt
      (depth + 1)).engine.node.Query)
  rw [show
    ((representationIntentU8Runtime oldVisit sourceIndex boundary).stateAt
      (depth + 1)).engine.node =
        .active
          (representationIntentU8TargetPresentationAt oldVisit sourceIndex
            boundary (depth + 2)) from
      representationIntentU8Runtime_stateAt_succ_node_exact oldVisit
        sourceIndex boundary depth]
  exact ⟨()⟩

/-- Every revised tick consumes the answer/consumer installed at its exact
visit and generates the next visit of the same named runtime. -/
theorem representationIntentU8EveryRevisedTick_generatesNext
    (oldVisit : OldVisit) (sourceIndex boundary depth : Nat) :
    ((representationIntentU8Runtime oldVisit sourceIndex boundary).tickAt
      (depth + 1)).next.node.erase =
      ⟨RepresentationIntentU8NAt oldVisit sourceIndex boundary,
        (representationIntentU8RevisedAnswerAndNextAt oldVisit sourceIndex
          boundary (depth + 2)).nextCurrent⟩ := by
  calc
    ((representationIntentU8Runtime oldVisit sourceIndex boundary).tickAt
        (depth + 1)).next.node.erase =
        ((representationIntentU8Runtime oldVisit sourceIndex boundary).stateAt
          ((depth + 1) + 1)).engine.node.erase := rfl
    _ =
        (representationIntentU8TargetPresentationAt oldVisit sourceIndex
          boundary ((depth + 1) + 2)).erase :=
      representationIntentU8Runtime_stateAt_succ_exact oldVisit sourceIndex
        boundary (depth + 1)
    _ =
        ⟨RepresentationIntentU8NAt oldVisit sourceIndex boundary,
          (representationIntentU8RevisedAnswerAndNextAt oldVisit sourceIndex
            boundary (depth + 2)).nextCurrent⟩ := by
      simpa [Nat.add_assoc] using
        representationIntentU8TargetPresentation_next_eq oldVisit sourceIndex
          boundary (depth + 2)

/-- Finite depths of the revised runtime remain distinct after authoritative
erasure because the exact generated `RootVisit` history is part of the
current.  Repeated Bool labels therefore cannot collapse occurrences. -/
theorem representationIntentU8RevisedStates_injective
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    Function.Injective
      (fun depth =>
        ((representationIntentU8Runtime oldVisit sourceIndex boundary).stateAt
          (depth + 1)).engine.node.erase) := by
  intro left right equality
  change
    ((representationIntentU8Runtime oldVisit sourceIndex boundary).stateAt
        (left + 1)).engine.node.erase =
      ((representationIntentU8Runtime oldVisit sourceIndex boundary).stateAt
        (right + 1)).engine.node.erase at equality
  rw [representationIntentU8Runtime_stateAt_succ_exact oldVisit sourceIndex
      boundary left,
    representationIntentU8Runtime_stateAt_succ_exact oldVisit sourceIndex
      boundary right] at equality
  have labelEquality :=
    congrArg representationIntentErasedRuntimeLabel equality
  have leftLabel :
      representationIntentErasedRuntimeLabel
          (representationIntentU8TargetPresentationAt oldVisit sourceIndex
            boundary (left + 2)).erase = (7, left + 2) := by
    simpa [representationIntentU8ProcessPresentation,
      representationIntentU8ExpectedRuntimeLabel] using
      representationIntentU8ProcessPresentation_label_exact oldVisit
        sourceIndex boundary (.revised (left + 2))
  have rightLabel :
      representationIntentErasedRuntimeLabel
          (representationIntentU8TargetPresentationAt oldVisit sourceIndex
            boundary (right + 2)).erase = (7, right + 2) := by
    simpa [representationIntentU8ProcessPresentation,
      representationIntentU8ExpectedRuntimeLabel] using
      representationIntentU8ProcessPresentation_label_exact oldVisit
        sourceIndex boundary (.revised (right + 2))
  rw [leftLabel, rightLabel] at labelEquality
  have depthEquality : left + 2 = right + 2 := congrArg Prod.snd labelEquality
  omega

/-- No positive finite period can identify two revised runtime occurrences.
In particular the named runtime has no fixed terminal state at any generated
finite depth. -/
theorem representationIntentU8Runtime_noFinitePeriod
    (oldVisit : OldVisit) (sourceIndex boundary start period : Nat)
    (periodPositive : 0 < period) :
    ((representationIntentU8Runtime oldVisit sourceIndex boundary).stateAt
      (start + 1)).engine.node.erase ≠
      ((representationIntentU8Runtime oldVisit sourceIndex boundary).stateAt
        ((start + period) + 1)).engine.node.erase := by
  intro equality
  have depthEquality :=
    representationIntentU8RevisedStates_injective oldVisit sourceIndex
      boundary equality
  omega

/-- Compact consumer for query-generated runtime openness at every finite
depth.  It exposes neither a scheduler nor a completed future. -/
theorem representationIntentU8Runtime_allFiniteGeneratedContinuation
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (∀ depth : Nat,
      ((representationIntentU8Runtime oldVisit sourceIndex boundary).stateAt
        (depth + 1)).engine.node =
        .active
          (representationIntentU8TargetPresentationAt oldVisit sourceIndex
            boundary (depth + 2))) ∧
      (∀ depth : Nat,
        Nonempty
          ((representationIntentU8Runtime oldVisit sourceIndex boundary
            ).stateAt (depth + 1)).engine.Query) ∧
      (∀ depth : Nat,
        ((representationIntentU8Runtime oldVisit sourceIndex boundary).tickAt
          (depth + 1)).next.node.erase =
          ⟨RepresentationIntentU8NAt oldVisit sourceIndex boundary,
            (representationIntentU8RevisedAnswerAndNextAt oldVisit sourceIndex
              boundary (depth + 2)).nextCurrent⟩) ∧
      Function.Injective
        (fun depth =>
          ((representationIntentU8Runtime oldVisit sourceIndex boundary
            ).stateAt (depth + 1)).engine.node.erase) ∧
      (∀ start period : Nat, 0 < period →
        ((representationIntentU8Runtime oldVisit sourceIndex boundary).stateAt
          (start + 1)).engine.node.erase ≠
          ((representationIntentU8Runtime oldVisit sourceIndex boundary
            ).stateAt ((start + period) + 1)).engine.node.erase) :=
  ⟨representationIntentU8Runtime_stateAt_succ_node_exact oldVisit sourceIndex
      boundary,
    representationIntentU8EveryFiniteDepth_remainsInquiryActive oldVisit
      sourceIndex boundary,
    representationIntentU8EveryRevisedTick_generatesNext oldVisit sourceIndex
      boundary,
    representationIntentU8RevisedStates_injective oldVisit sourceIndex
      boundary,
    representationIntentU8Runtime_noFinitePeriod oldVisit sourceIndex
      boundary⟩

/-- Reusing the visit-two engine state after its answer would replay stale
authority.  The generated next is the distinct visit-three history even
though both currents carry the Bool label `true`. -/
theorem representationIntentU8SingleRevisedState_selfLoop_isStale
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (representationIntentU8TargetPresentationAt oldVisit sourceIndex boundary
      2).erase ≠
      ⟨RepresentationIntentU8NAt oldVisit sourceIndex boundary,
        (representationIntentU8RevisedAnswerAndNextAt oldVisit sourceIndex
          boundary 2).nextCurrent⟩ := by
  rw [← representationIntentU8TargetPresentation_next_eq oldVisit sourceIndex
    boundary 2]
  intro erased_eq
  have label_eq :=
    congrArg representationIntentErasedRuntimeLabel erased_eq
  have left_label :
      representationIntentErasedRuntimeLabel
          (representationIntentU8TargetPresentationAt oldVisit sourceIndex
            boundary 2).erase = (7, 2) := by
    simpa [representationIntentU8ProcessPresentation,
      representationIntentU8ExpectedRuntimeLabel] using
      representationIntentU8ProcessPresentation_label_exact oldVisit
        sourceIndex boundary (.revised 2)
  have right_label :
      representationIntentErasedRuntimeLabel
          (representationIntentU8TargetPresentationAt oldVisit sourceIndex
            boundary 3).erase = (7, 3) := by
    simpa [representationIntentU8ProcessPresentation,
      representationIntentU8ExpectedRuntimeLabel] using
      representationIntentU8ProcessPresentation_label_exact oldVisit
        sourceIndex boundary (.revised 3)
  rw [left_label, right_label] at label_eq
  have impossible : (2 : Nat) = 3 := congrArg Prod.snd label_eq
  omega

theorem representationIntentU8Runtime_directConsumer
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (representationIntentU8FirstTick oldVisit sourceIndex boundary).resolution =
        .revised
          (generatedRepresentationObstructionAt oldVisit sourceIndex boundary)
          (representationIntentU7GateAt oldVisit sourceIndex boundary)
          (representationPairIntentFailureAt oldVisit sourceIndex boundary)
          (representationIntentGeneratedU8Core oldVisit sourceIndex boundary) ∧
      ((representationIntentU8Runtime oldVisit sourceIndex boundary).stateAt 1
        ).engine.node.erase =
        (representationIntentU8TargetPresentationAt oldVisit sourceIndex
          boundary 2).erase ∧
      ((representationIntentU8Runtime oldVisit sourceIndex boundary).stateAt 2
        ).engine.node.erase =
        ⟨RepresentationIntentU8NAt oldVisit sourceIndex boundary,
          (representationIntentU8RevisedAnswerAndNextAt oldVisit sourceIndex
            boundary 2).nextCurrent⟩ :=
  ⟨rfl, rfl,
    representationIntentU8FirstRevisedTick_generatesNext oldVisit sourceIndex
      boundary⟩

end
end M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Runtime
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Runtime.representationIntentU8Process
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Runtime.representationIntentU8Runtime_consumesExactCore
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Runtime.representationIntentU8CofaceRealization_installed
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Runtime.representationIntentU8Runtime_core_unique
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Runtime.representationIntentU8FirstRevisedTick_generatesNext
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Runtime.representationIntentU8Runtime_stateAt_succ_node_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Runtime.representationIntentU8EveryRevisedTick_generatesNext
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Runtime.representationIntentU8RevisedStates_injective
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Runtime.representationIntentU8Runtime_noFinitePeriod
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Runtime.representationIntentU8Runtime_allFiniteGeneratedContinuation
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Runtime.representationIntentU8SingleRevisedState_selfLoop_isStale
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Runtime.representationIntentU8Runtime_directConsumer
