/-
  Proposition 12: canonical obstruction support.

  Proposition 9 allowed an arbitrary `obstruction : State -> Obstruction`.
  Proposition 10 then connected one concrete classifier to a reopen taxonomy.
  The risk is that the taxonomy could be merely chosen.

  This file proves the representation-independent core:

    * the canonical obstruction of a state is not a chosen label, but the
      support predicate of all failed safety atoms;
    * unsafe states are exactly those with nonempty canonical support;
    * any sound-and-complete obstruction presentation is unique up to decoded
      support equivalence;
    * the first-failure classifier is sound, but it can be complete only when
      the support has at most one atom.

  Thus a taxonomy is canonical only insofar as it presents this support object
  without losing information.
-/

import H0mework.Realization.Observation.DomainOrder

/-! ## Canonical support object -/

/-- The canonical obstruction support: all failed safety atoms at a state. -/
def canonicalReopenSupport {State : Type*}
    (P : CSafePredicates State) (x : State) (r : ReopenTaxonomy) : Prop :=
  taxonomyWitness P x r

/-- THEOREM 1: unsafe states are exactly those with nonempty canonical support. -/
theorem canonicalSupport_nonempty_iff_not_csafe {State : Type*}
    (P : CSafePredicates State) (x : State)
    [Decidable (P.sourceBacked x)] [Decidable (P.authoritySafe x)]
    [Decidable (P.graphConfluent x)] [Decidable (P.gaugeNonleaking x)]
    [Decidable (P.contractionSafe x)] [Decidable (P.omegaConsistent x)]
    [Decidable (P.freshnessSafe x)] :
    (∃ r, canonicalReopenSupport P x r) ↔ ¬ CSafe P x := by
  exact (not_csafe_iff_exists_taxonomy P x).symm

/-! ## Presentations of the support object -/

/-- A presentation of obstructions by an arbitrary representation `O`.

It is canonical only if its decoded support is sound and complete with respect
to the algebraic support object.
-/
structure ObstructionPresentation {State : Type*}
    (P : CSafePredicates State) (O : Type*) where
  classify : State → O
  decodes : O → ReopenTaxonomy → Prop
  sound : ∀ x r, decodes (classify x) r → canonicalReopenSupport P x r
  complete : ∀ x r, canonicalReopenSupport P x r → decodes (classify x) r

/-- THEOREM 2: any sound-and-complete presentation decodes to exactly the
    canonical support. -/
theorem obstructionPresentation_unique_support {State O : Type*}
    (P : CSafePredicates State) (pres : ObstructionPresentation P O)
    (x : State) (r : ReopenTaxonomy) :
    pres.decodes (pres.classify x) r ↔ canonicalReopenSupport P x r := by
  constructor
  · exact pres.sound x r
  · exact pres.complete x r

/-- THEOREM 3: any two sound-and-complete presentations are equivalent after
    decoding; their representation choices carry no extra canonical content. -/
theorem obstructionPresentations_equivalent {State O₁ O₂ : Type*}
    (P : CSafePredicates State)
    (pres₁ : ObstructionPresentation P O₁)
    (pres₂ : ObstructionPresentation P O₂)
    (x : State) (r : ReopenTaxonomy) :
    pres₁.decodes (pres₁.classify x) r ↔ pres₂.decodes (pres₂.classify x) r := by
  calc
    pres₁.decodes (pres₁.classify x) r ↔ canonicalReopenSupport P x r :=
      obstructionPresentation_unique_support P pres₁ x r
    _ ↔ pres₂.decodes (pres₂.classify x) r :=
      (obstructionPresentation_unique_support P pres₂ x r).symm

/-- The canonical presentation: represent an obstruction by its support
    predicate itself. -/
def canonicalObstructionPresentation {State : Type*}
    (P : CSafePredicates State) :
    ObstructionPresentation P (ReopenTaxonomy → Prop) where
  classify := fun x => canonicalReopenSupport P x
  decodes := fun support r => support r
  sound := by
    intro _x _r h
    exact h
  complete := by
    intro _x _r h
    exact h

/-! ## First-failure classifiers are not canonical in general -/

/-- Decoding for a first-failure classifier: it exposes exactly one tag. -/
def firstFailureDecode (o : Option ReopenTaxonomy) (r : ReopenTaxonomy) : Prop :=
  o = some r

/-- THEOREM 4: the existing first-failure classifier is sound. -/
theorem firstFailureClassifier_sound {State : Type*}
    (P : CSafePredicates State) (x : State) (r : ReopenTaxonomy)
    [Decidable (P.sourceBacked x)] [Decidable (P.authoritySafe x)]
    [Decidable (P.graphConfluent x)] [Decidable (P.gaugeNonleaking x)]
    [Decidable (P.contractionSafe x)] [Decidable (P.omegaConsistent x)]
    [Decidable (P.freshnessSafe x)]
    (h : firstFailureDecode (classifyUnsafe P x) r) :
    canonicalReopenSupport P x r := by
  exact taxonomyWitness_of_classifyUnsafe_some P x h

/-- THEOREM 5: if the first-failure classifier were complete at a state, the
    canonical support at that state would have at most one atom. -/
theorem firstFailure_complete_implies_subsingleton_support {State : Type*}
    (P : CSafePredicates State) (x : State)
    [Decidable (P.sourceBacked x)] [Decidable (P.authoritySafe x)]
    [Decidable (P.graphConfluent x)] [Decidable (P.gaugeNonleaking x)]
    [Decidable (P.contractionSafe x)] [Decidable (P.omegaConsistent x)]
    [Decidable (P.freshnessSafe x)]
    (hcomplete :
      ∀ r, canonicalReopenSupport P x r →
        firstFailureDecode (classifyUnsafe P x) r) :
    ∀ r₁ r₂,
      canonicalReopenSupport P x r₁ →
      canonicalReopenSupport P x r₂ →
      r₁ = r₂ := by
  intro r₁ r₂ h₁ h₂
  have hc₁ := hcomplete r₁ h₁
  have hc₂ := hcomplete r₂ h₂
  have hs : (some r₁ : Option ReopenTaxonomy) = some r₂ := hc₁.symm.trans hc₂
  exact Option.some.inj hs

/-- THEOREM 6: if two distinct obstruction atoms are present, the first-failure
    classifier cannot be complete. -/
theorem firstFailure_not_complete_of_two_failures {State : Type*}
    (P : CSafePredicates State) (x : State)
    [Decidable (P.sourceBacked x)] [Decidable (P.authoritySafe x)]
    [Decidable (P.graphConfluent x)] [Decidable (P.gaugeNonleaking x)]
    [Decidable (P.contractionSafe x)] [Decidable (P.omegaConsistent x)]
    [Decidable (P.freshnessSafe x)]
    {r₁ r₂ : ReopenTaxonomy} (hne : r₁ ≠ r₂)
    (h₁ : canonicalReopenSupport P x r₁)
    (h₂ : canonicalReopenSupport P x r₂) :
    ¬ (∀ r, canonicalReopenSupport P x r →
        firstFailureDecode (classifyUnsafe P x) r) := by
  intro hcomplete
  exact hne (firstFailure_complete_implies_subsingleton_support P x hcomplete r₁ r₂ h₁ h₂)

/-!
  Summary:
  - The canonical obstruction is the full support of failed algebraic atoms.
  - Any sound-and-complete presentation is unique up to decoded support.
  - A first-failure taxonomy is sound but loses information whenever multiple
    atoms fail, so it is a runtime convenience, not the canonical object.

  What remains outside this file: proving that the primitive safety atoms
  themselves are the right algebraic atoms of the concrete runtime.
-/
