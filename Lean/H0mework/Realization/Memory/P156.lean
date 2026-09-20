/-
  Proposition 156: topological understanding regions for feedback memory.

  P148 deliberately stopped at the signed-feedback algebra: zero sign iff no
  recollectable potential, and F-only feedback has zero sign everywhere.  P150
  through P152 then proved the structural F-only no-go for reflexive/stateful
  query trees.

  This file closes the next modest topological step.  It does not declare that
  "understanding" has been solved.  It proves the precise region theorem that
  the notes asked for:

    * the feedback understanding region is exactly positive-support ∪
      negative-support;
    * if both support predicates are open, that region is open;
    * F-only feedback has an empty understanding region;
    * any point in an open support component has locally stable recollectable
      potential;
    * an open bipolar region therefore supplies both positive and negative
      locally stable potential witnesses.

  Boundary: the theorem is sufficient, not necessary.  It assumes a topology in
  which the runtime support predicates are open.  Proving that a concrete
  reducer's `η > 0` / `λ ≠ 0` predicates are open is a mechanism-faithfulness
  obligation for that reducer, not a free consequence of this file.
-/

import H0mework.Realization.QueryPlans.P152
import Mathlib.Topology.Basic

open Set

/-! ## Understanding region as recollectable-potential support -/

/-- The feedback understanding region: states where the signed recollection act
has recollectable potential. -/
def FeedbackUnderstandingRegion {State : Type*}
    (S : FeedbackSupport State) : Set State :=
  {x | RecollectableMemoryPotential (feedbackRecollectionAct S) x}

/-- THEOREM 1: the feedback understanding region is exactly the union of the
positive and negative feedback support predicates. -/
theorem feedbackUnderstandingRegion_eq_support_union
    {State : Type*} (S : FeedbackSupport State) :
    FeedbackUnderstandingRegion S =
      {x | S.positive x} ∪ {x | S.negative x} := by
  ext x
  constructor
  · intro hpot
    exact (feedbackMemoryProduced_iff_recollectablePotential S x).mpr hpot
  · intro hprod
    exact (feedbackMemoryProduced_iff_recollectablePotential S x).mp hprod

/-- THEOREM 2: if both feedback supports are open predicates, the understanding
region is open. -/
theorem isOpen_feedbackUnderstandingRegion
    {State : Type*} [TopologicalSpace State]
    (S : FeedbackSupport State)
    (hpos : IsOpen {x | S.positive x})
    (hneg : IsOpen {x | S.negative x}) :
    IsOpen (FeedbackUnderstandingRegion S) := by
  rw [feedbackUnderstandingRegion_eq_support_union]
  exact hpos.union hneg

/-- Local stability of recollectable potential: near `x`, the canonical
feedback recollection act keeps firing. -/
def LocallyStableRecollectablePotential
    {State : Type*} [TopologicalSpace State]
    (S : FeedbackSupport State) (x : State) : Prop :=
  exists U : Set State,
    IsOpen U /\ x ∈ U /\
      forall y, y ∈ U ->
        RecollectableMemoryPotential (feedbackRecollectionAct S) y

/-- THEOREM 3: membership in an open understanding region gives local
stability of recollectable potential. -/
theorem locallyStable_of_open_feedbackUnderstandingRegion
    {State : Type*} [TopologicalSpace State]
    (S : FeedbackSupport State)
    (hopen : IsOpen (FeedbackUnderstandingRegion S))
    {x : State} (hx : x ∈ FeedbackUnderstandingRegion S) :
    LocallyStableRecollectablePotential S x := by
  refine ⟨FeedbackUnderstandingRegion S, hopen, hx, ?_⟩
  intro y hy
  exact hy

/-- THEOREM 4: an open positive-support component gives a locally stable
positive memory-production point. -/
theorem locallyStable_of_positive_open
    {State : Type*} [TopologicalSpace State]
    (S : FeedbackSupport State)
    (hpos : IsOpen {x | S.positive x})
    {x : State} (hx : S.positive x) :
    LocallyStableRecollectablePotential S x := by
  refine ⟨{y | S.positive y}, hpos, hx, ?_⟩
  intro y hy
  exact (feedbackMemoryProduced_iff_recollectablePotential S y).mp
    (Or.inl hy)

/-- THEOREM 5: an open negative-support component gives a locally stable
negative memory-production point. -/
theorem locallyStable_of_negative_open
    {State : Type*} [TopologicalSpace State]
    (S : FeedbackSupport State)
    (hneg : IsOpen {x | S.negative x})
    {x : State} (hx : S.negative x) :
    LocallyStableRecollectablePotential S x := by
  refine ⟨{y | S.negative y}, hneg, hx, ?_⟩
  intro y hy
  exact (feedbackMemoryProduced_iff_recollectablePotential S y).mp
    (Or.inr hy)

/-! ## F-only topological no-go -/

/-- THEOREM 6: F-only feedback has empty topological understanding region. -/
theorem fOnly_feedbackUnderstandingRegion_empty
    {State : Type*} (S : FeedbackSupport State)
    (hF : FOnlyFeedback S) :
    FeedbackUnderstandingRegion S = ∅ := by
  ext x
  constructor
  · intro hx
    exact (fOnly_no_recollectablePotential S hF x) hx
  · intro hx
    cases hx

/-- THEOREM 7: under F-only feedback, no subset can sit inside a nonempty
understanding region.  The open-set version is an immediate corollary; no
openness is needed for the contradiction. -/
theorem fOnly_no_understandingSubregion
    {State : Type*} (S : FeedbackSupport State)
    (hF : FOnlyFeedback S) {U : Set State}
    (hsub : U ⊆ FeedbackUnderstandingRegion S) :
    U = ∅ := by
  rw [fOnly_feedbackUnderstandingRegion_empty S hF] at hsub
  exact subset_empty_iff.mp hsub

/-! ## Open bipolar regions -/

/-- A bipolar feedback region carried by an open subregion.  It records that
both polarities occur somewhere inside one open patch; pointwise necessity of
both polarities is intentionally not built into the definition. -/
structure OpenBipolarFeedbackRegion
    {State : Type*} [TopologicalSpace State]
    (S : FeedbackSupport State) (Region : Set State) where
  carrier : Set State
  isOpen : IsOpen carrier
  subset_region : carrier ⊆ Region
  positive_witness : exists x, x ∈ carrier /\ S.positive x
  negative_witness : exists x, x ∈ carrier /\ S.negative x

/-- THEOREM 8: an open bipolar region supplies a positive locally stable
recollectable-potential witness and a negative one. -/
theorem openBipolarRegion_has_locallyStable_polar_witnesses
    {State : Type*} [TopologicalSpace State]
    {S : FeedbackSupport State} {Region : Set State}
    (B : OpenBipolarFeedbackRegion S Region)
    (hpos : IsOpen {x | S.positive x})
    (hneg : IsOpen {x | S.negative x}) :
    (exists x, x ∈ Region /\ S.positive x /\
      LocallyStableRecollectablePotential S x) /\
    (exists x, x ∈ Region /\ S.negative x /\
      LocallyStableRecollectablePotential S x) := by
  constructor
  · rcases B.positive_witness with ⟨x, hxCarrier, hxPos⟩
    exact ⟨x, B.subset_region hxCarrier, hxPos,
      locallyStable_of_positive_open S hpos hxPos⟩
  · rcases B.negative_witness with ⟨x, hxCarrier, hxNeg⟩
    exact ⟨x, B.subset_region hxCarrier, hxNeg,
      locallyStable_of_negative_open S hneg hxNeg⟩

/-- THEOREM 9: an open bipolar region cannot be F-only on its carrier. -/
theorem openBipolarRegion_not_locally_fOnly
    {State : Type*} [TopologicalSpace State]
    {S : FeedbackSupport State} {Region : Set State}
    (B : OpenBipolarFeedbackRegion S Region) :
    ¬ (forall x, x ∈ B.carrier -> ¬ FeedbackMemoryProduced S x) := by
  intro hF
  rcases B.positive_witness with ⟨x, hxCarrier, hxPos⟩
  exact hF x hxCarrier (Or.inl hxPos)

/-!
  Summary:
  - N2 is now a theorem under the natural support-open hypothesis:
    `{x | recollectable potential}` is an open region and F-only systems make
    it empty.
  - N1 is proved in its sufficient/certified form: an open bipolar patch
    supplies both positive and negative locally stable recollectable-potential
    witnesses.

  Remaining boundary:
  - This does not prove that a concrete runtime reducer's support predicates
    are open.  That is exactly the runtime certification layer N5 asks for.
  - It also does not prove the stronger necessity claim that stable
    understanding requires both polarities throughout an open neighborhood.
-/
