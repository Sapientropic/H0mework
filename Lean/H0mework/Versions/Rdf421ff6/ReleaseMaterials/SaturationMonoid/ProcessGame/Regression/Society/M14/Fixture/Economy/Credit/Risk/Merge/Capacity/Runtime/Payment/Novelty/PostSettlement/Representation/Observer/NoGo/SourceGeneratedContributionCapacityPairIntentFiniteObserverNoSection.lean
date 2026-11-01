import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Novelty.PostSettlement.Representation.Observer.NoGo.SourceGeneratedContributionCapacityPairIntentOpenRuntimeClassicalNoSection

/-!
# PairIntent complete observer-truth classification

For an arbitrary observer language, exact factorization of the named PairIntent
runtime authority exists precisely when the observer is injective on all
generated depths.  Hence every noninjective observer has no section; restricting
the forced injection to `Fin (Fintype.card Visible + 1)` rules out every finite
observer automatically.

The stationary Bool no-section remains the exact classical instance.  This
module introduces no second Bool fibre, runtime or observer registry.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityPairIntentFiniteObserverNoSection

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Runtime
open M14SourceGeneratedContributionCapacityPairIntentOpenRuntimeClassicalNoSection

/-- Raw reconstruction syntax for any observer language.  Its inhabitant is
source-derived from the exact named runtime state at generated depth zero and
does not depend on a failure theorem. -/
def pairIntentFiniteObserverRawReconstructor
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) (Visible : Type) :
    Visible → AnyAuthoritativeRootCurrent :=
  fun _visible =>
    pairIntentRuntimeAuthorityAt oldVisit sourceIndex boundary 0

theorem pairIntentFiniteObserverRawReconstructor_nonempty
    {Visible : Type} [Fintype Visible]
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (_observe : Nat → Visible) :
    Nonempty (Visible → AnyAuthoritativeRootCurrent.{0}) :=
  ⟨pairIntentFiniteObserverRawReconstructor oldVisit sourceIndex boundary
    Visible⟩

/-- Candidate exact factorization of the generated authoritative runtime
through one observer language.  This is ordinary reconstruction syntax plus
the commuting requirement, not an authority registry. -/
structure PairIntentAuthorityFactorizationThroughObserverAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    {Visible : Type} (observe : Nat → Visible) where
  reconstruct : Visible → AnyAuthoritativeRootCurrent
  commutes : ∀ depth : Nat,
    reconstruct (observe depth) =
      pairIntentRuntimeAuthorityAt oldVisit sourceIndex boundary depth

/-- Exact reconstruction forces the observer to distinguish every generated
runtime depth. -/
theorem pairIntentObserverFactorization_forces_observe_injective
    {Visible : Type}
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (observe : Nat → Visible)
    (factorization :
      PairIntentAuthorityFactorizationThroughObserverAt oldVisit sourceIndex
        boundary observe) :
    Function.Injective observe := by
  intro left right observationEquality
  apply representationIntentU8RevisedStates_injective oldVisit sourceIndex
    boundary
  have authorityEquality :
      pairIntentRuntimeAuthorityAt oldVisit sourceIndex boundary left =
        pairIntentRuntimeAuthorityAt oldVisit sourceIndex boundary right := by
    rw [← factorization.commutes left, ← factorization.commutes right,
      observationEquality]
  simpa [pairIntentRuntimeAuthorityAt] using authorityEquality

/-- An injective observer can reconstruct the exact named runtime authority:
`Function.invFun` chooses the unique generated depth on the observer image and
still returns a named generated depth off that image. -/
noncomputable def pairIntentAuthorityFactorizationOfInjective
    {Visible : Type}
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (observe : Nat → Visible)
    (observeInjective : Function.Injective observe) :
    PairIntentAuthorityFactorizationThroughObserverAt oldVisit sourceIndex
      boundary observe := by
  classical
  exact
    { reconstruct := fun visible =>
        pairIntentRuntimeAuthorityAt oldVisit sourceIndex boundary
          (Function.invFun observe visible)
      commutes := by
        intro depth
        rw [Function.leftInverse_invFun observeInjective depth] }

/-- Complete observer-truth classification: exact authority reconstruction is
possible precisely when the observer preserves every generated lineage depth. -/
theorem pairIntentAuthorityFactorization_nonempty_iff_observe_injective
    {Visible : Type}
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (observe : Nat → Visible) :
    Nonempty
        (PairIntentAuthorityFactorizationThroughObserverAt oldVisit sourceIndex
          boundary observe) ↔
      Function.Injective observe := by
  constructor
  · rintro ⟨factorization⟩
    exact pairIntentObserverFactorization_forces_observe_injective oldVisit
      sourceIndex boundary observe factorization
  · intro observeInjective
    exact ⟨pairIntentAuthorityFactorizationOfInjective oldVisit sourceIndex
      boundary observe observeInjective⟩

/-- Category-level no-section: every observer which identifies any two
generated depths, finite or infinite, is too coarse to reconstruct exact
authority. -/
theorem pairIntentAuthorityFactorizationThroughNoninjectiveObserver_isEmpty
    {Visible : Type}
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (observe : Nat → Visible)
    (notInjective : ¬ Function.Injective observe) :
    IsEmpty
      (PairIntentAuthorityFactorizationThroughObserverAt oldVisit sourceIndex
        boundary observe) :=
  ⟨fun factorization =>
    notInjective
      (pairIntentObserverFactorization_forces_observe_injective oldVisit
        sourceIndex boundary observe factorization)⟩

/-- Exact dual classification of observer failure. -/
theorem pairIntentAuthorityFactorization_isEmpty_iff_observe_notInjective
    {Visible : Type}
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (observe : Nat → Visible) :
    IsEmpty
        (PairIntentAuthorityFactorizationThroughObserverAt oldVisit sourceIndex
          boundary observe) ↔
      ¬ Function.Injective observe := by
  constructor
  · intro factorizationEmpty observeInjective
    exact factorizationEmpty.false
      (pairIntentAuthorityFactorizationOfInjective oldVisit sourceIndex boundary
        observe observeInjective)
  · exact pairIntentAuthorityFactorizationThroughNoninjectiveObserver_isEmpty
      oldVisit sourceIndex boundary observe

/-- No exact factorization of the open runtime authority can pass through any
finite observer language. -/
theorem pairIntentAuthorityFactorizationThroughFiniteObserver_isEmpty
    {Visible : Type} [Fintype Visible]
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (observe : Nat → Visible) :
    IsEmpty
      (PairIntentAuthorityFactorizationThroughObserverAt oldVisit sourceIndex
        boundary observe) :=
  ⟨fun factorization => by
    have observeInjective : Function.Injective observe :=
      pairIntentObserverFactorization_forces_observe_injective oldVisit
        sourceIndex boundary observe factorization
    let restricted : Fin (Fintype.card Visible + 1) → Visible :=
      fun index => observe index
    have restrictedInjective : Function.Injective restricted := by
      intro left right equality
      apply Fin.ext
      exact observeInjective equality
    have cardLe :
        Fintype.card (Fin (Fintype.card Visible + 1)) ≤
          Fintype.card Visible :=
      Fintype.card_le_of_injective restricted restrictedInjective
    simp only [Fintype.card_fin] at cardLe
    omega⟩

/-- A generic factorization through the exact stationary classical readout is
literally consumable by the committed Bool factorization mouth. -/
def pairIntentStationaryBoolFactorization_toClassical
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (factorization :
      PairIntentAuthorityFactorizationThroughObserverAt oldVisit sourceIndex
        boundary
        (pairIntentClassicalCurrentAt oldVisit sourceIndex boundary)) :
    PairIntentAuthorityFactorizationThroughBoolAt oldVisit sourceIndex
      boundary where
  reconstruct := factorization.reconstruct
  commutes := factorization.commutes

/-- Exact Bool instance of the generic observer candidate, discharged by the
existing stationary-classical no-section rather than a competing Bool proof. -/
theorem pairIntentStationaryBoolFactorization_isEmpty_fromClassical
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    IsEmpty
      (PairIntentAuthorityFactorizationThroughObserverAt oldVisit sourceIndex
        boundary
        (pairIntentClassicalCurrentAt oldVisit sourceIndex boundary)) :=
  ⟨fun factorization =>
    (pairIntentAuthorityFactorizationThroughBool_isEmpty oldVisit sourceIndex
      boundary).false
      (pairIntentStationaryBoolFactorization_toClassical oldVisit sourceIndex
        boundary factorization)⟩

/-- Compact consumer: every noninjective observer has no exact section, every
finite observer has inhabited raw syntax but no exact section, and the full
stationary-Bool fibre theorem is retained as the precise classical instance. -/
theorem pairIntentObserverNoSection_directConsumer
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (∀ (Visible : Type) (observe : Nat → Visible),
      Nonempty
          (PairIntentAuthorityFactorizationThroughObserverAt oldVisit
            sourceIndex boundary observe) ↔
        Function.Injective observe) ∧
      (∀ (Visible : Type) (observe : Nat → Visible),
      (¬ Function.Injective observe) →
        IsEmpty
          (PairIntentAuthorityFactorizationThroughObserverAt oldVisit
            sourceIndex boundary observe)) ∧
      (∀ (Visible : Type) [Fintype Visible] (observe : Nat → Visible),
      Nonempty (Visible → AnyAuthoritativeRootCurrent.{0}) ∧
        IsEmpty
          (PairIntentAuthorityFactorizationThroughObserverAt oldVisit
            sourceIndex boundary observe)) ∧
      type_of%
        (pairIntentOpenRuntimeClassicalNoSection_directConsumer oldVisit
          sourceIndex boundary) ∧
      IsEmpty
        (PairIntentAuthorityFactorizationThroughObserverAt oldVisit sourceIndex
          boundary
          (pairIntentClassicalCurrentAt oldVisit sourceIndex boundary)) := by
  constructor
  · intro Visible observe
    exact pairIntentAuthorityFactorization_nonempty_iff_observe_injective
      oldVisit sourceIndex boundary observe
  constructor
  · intro Visible observe notInjective
    exact
      pairIntentAuthorityFactorizationThroughNoninjectiveObserver_isEmpty
        oldVisit sourceIndex boundary observe notInjective
  constructor
  · intro Visible _inst observe
    exact
      ⟨pairIntentFiniteObserverRawReconstructor_nonempty oldVisit sourceIndex
          boundary observe,
        pairIntentAuthorityFactorizationThroughFiniteObserver_isEmpty oldVisit
          sourceIndex boundary observe⟩
  constructor
  · exact pairIntentOpenRuntimeClassicalNoSection_directConsumer oldVisit
      sourceIndex boundary
  · exact pairIntentStationaryBoolFactorization_isEmpty_fromClassical
      oldVisit sourceIndex boundary

end
end M14SourceGeneratedContributionCapacityPairIntentFiniteObserverNoSection
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityPairIntentFiniteObserverNoSection.pairIntentFiniteObserverRawReconstructor_nonempty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityPairIntentFiniteObserverNoSection.pairIntentObserverFactorization_forces_observe_injective
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityPairIntentFiniteObserverNoSection.pairIntentAuthorityFactorizationOfInjective
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityPairIntentFiniteObserverNoSection.pairIntentAuthorityFactorization_nonempty_iff_observe_injective
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityPairIntentFiniteObserverNoSection.pairIntentAuthorityFactorizationThroughNoninjectiveObserver_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityPairIntentFiniteObserverNoSection.pairIntentAuthorityFactorization_isEmpty_iff_observe_notInjective
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityPairIntentFiniteObserverNoSection.pairIntentAuthorityFactorizationThroughFiniteObserver_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityPairIntentFiniteObserverNoSection.pairIntentStationaryBoolFactorization_isEmpty_fromClassical
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityPairIntentFiniteObserverNoSection.pairIntentObserverNoSection_directConsumer
