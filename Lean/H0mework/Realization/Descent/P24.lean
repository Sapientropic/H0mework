/-
  Proposition 24: gluing-failure presentations and no-free completeness.

  Proposition 17 identified `GluingFailureSupport` as the local-safe/global-
  unsafe support object.  This file gives it the same presentation theorem that
  Proposition 12 gave local reopen support: any sound-and-complete gluing
  presentation decodes to exactly the same support, independent of the chosen
  representation.

  It also formalizes two negative boundaries:
    * sound-only presentations do not imply gluing completeness;
    * the seven-facet taxonomy being complete for `C_safe` does not imply
      completeness for a strictly stronger runtime safety predicate.
-/

import H0mework.Realization.Observation.AtomEquivalence

/-! ## Presentations of gluing-failure support -/

/-- A presentation of pairwise gluing failures by an arbitrary representation
    `O`.  It is canonical only through its decoded support. -/
structure GluingFailurePresentation
    {Left Right Global : Type*}
    (PL : CSafePredicates Left) (PR : CSafePredicates Right)
    (PG : CSafePredicates Global) (glue : Left → Right → Global)
    (O : Type*) where
  classify : Left → Right → O
  decodes : O → SemanticAtom → Prop
  sound :
    ∀ l r a,
      decodes (classify l r) a →
        GluingFailureSupport PL PR PG glue l r a
  complete :
    ∀ l r a,
      GluingFailureSupport PL PR PG glue l r a →
        decodes (classify l r) a

/-- THEOREM 1: any sound-and-complete gluing presentation decodes to exactly
    `GluingFailureSupport`. -/
theorem gluingFailurePresentation_unique_support
    {Left Right Global O : Type*}
    (PL : CSafePredicates Left) (PR : CSafePredicates Right)
    (PG : CSafePredicates Global) (glue : Left → Right → Global)
    (pres : GluingFailurePresentation PL PR PG glue O)
    (l : Left) (r : Right) (a : SemanticAtom) :
    pres.decodes (pres.classify l r) a ↔
      GluingFailureSupport PL PR PG glue l r a := by
  constructor
  · exact pres.sound l r a
  · exact pres.complete l r a

/-- THEOREM 2: any two sound-and-complete gluing presentations are equivalent
    after decoding. -/
theorem gluingFailurePresentations_equivalent
    {Left Right Global O₁ O₂ : Type*}
    (PL : CSafePredicates Left) (PR : CSafePredicates Right)
    (PG : CSafePredicates Global) (glue : Left → Right → Global)
    (pres₁ : GluingFailurePresentation PL PR PG glue O₁)
    (pres₂ : GluingFailurePresentation PL PR PG glue O₂)
    (l : Left) (r : Right) (a : SemanticAtom) :
    pres₁.decodes (pres₁.classify l r) a ↔
      pres₂.decodes (pres₂.classify l r) a := by
  calc
    pres₁.decodes (pres₁.classify l r) a
        ↔ GluingFailureSupport PL PR PG glue l r a :=
      gluingFailurePresentation_unique_support PL PR PG glue pres₁ l r a
    _ ↔ pres₂.decodes (pres₂.classify l r) a :=
      (gluingFailurePresentation_unique_support PL PR PG glue pres₂ l r a).symm

/-- The canonical presentation: the representation is the support predicate
    itself. -/
def canonicalGluingFailurePresentation
    {Left Right Global : Type*}
    (PL : CSafePredicates Left) (PR : CSafePredicates Right)
    (PG : CSafePredicates Global) (glue : Left → Right → Global) :
    GluingFailurePresentation PL PR PG glue (SemanticAtom → Prop) where
  classify := fun l r => GluingFailureSupport PL PR PG glue l r
  decodes := fun support a => support a
  sound := by
    intro _l _r _a h
    exact h
  complete := by
    intro _l _r _a h
    exact h

/-! ## Sound-only is not enough -/

/-- A gluing-failure presentation with only soundness, no completeness. -/
structure SoundGluingFailurePresentation
    {Left Right Global : Type*}
    (PL : CSafePredicates Left) (PR : CSafePredicates Right)
    (PG : CSafePredicates Global) (glue : Left → Right → Global)
    (O : Type*) where
  classify : Left → Right → O
  decodes : O → SemanticAtom → Prop
  sound :
    ∀ l r a,
      decodes (classify l r) a →
        GluingFailureSupport PL PR PG glue l r a

/-- The empty presentation is always sound: it reports no gluing failures. -/
def emptySoundGluingFailurePresentation
    {Left Right Global : Type*}
    (PL : CSafePredicates Left) (PR : CSafePredicates Right)
    (PG : CSafePredicates Global) (glue : Left → Right → Global) :
    SoundGluingFailurePresentation PL PR PG glue PUnit where
  classify := fun _ _ => PUnit.unit
  decodes := fun _ _ => False
  sound := by
    intro _l _r _a h
    exact False.elim h

/-- THEOREM 3: if a real gluing failure exists, soundness alone cannot force
    completeness; the empty sound presentation is a counterexample. -/
theorem sound_only_does_not_imply_gluing_complete
    {Left Right Global : Type*}
    (PL : CSafePredicates Left) (PR : CSafePredicates Right)
    (PG : CSafePredicates Global) (glue : Left → Right → Global)
    {l : Left} {r : Right} {a : SemanticAtom}
    (ha : GluingFailureSupport PL PR PG glue l r a) :
    ∃ O,
      ∃ pres : SoundGluingFailurePresentation PL PR PG glue O,
        ¬ (∀ l r a,
          GluingFailureSupport PL PR PG glue l r a →
            pres.decodes (pres.classify l r) a) := by
  refine ⟨PUnit, emptySoundGluingFailurePresentation PL PR PG glue, ?_⟩
  intro hcomplete
  exact hcomplete l r a ha

/-! ## Seven-facet completeness does not automatically lift to stronger safety -/

/-- A runtime safety predicate that adds one extra obligation beyond `C_safe`. -/
def strongerRuntimeSafe {State : Type*}
    (P : CSafePredicates State) (extra : State → Prop) (x : State) : Prop :=
  CSafe P x ∧ extra x

/-- THEOREM 4: if a state satisfies all seven facets but fails an extra
    obligation, the reopen taxonomy is empty while stronger runtime safety
    fails.  Thus seven-facet completeness for `C_safe` does not freely become
    completeness for a stricter runtime contract. -/
theorem no_free_seven_facet_completeness_for_stronger_runtime
    {State : Type*} (P : CSafePredicates State)
    (extra : State → Prop) (x : State)
    (hx : CSafe P x) (hextra : ¬ extra x) :
    ¬ strongerRuntimeSafe P extra x ∧
      ¬ (∃ r, taxonomyWitness P x r) := by
  constructor
  · intro hstrong
    exact hextra hstrong.2
  · intro htax
    have hunsafe : ¬ CSafe P x :=
      (taxonomySupport_nonempty_iff_not_csafe P x).mp htax
    exact hunsafe hx

/-!
  Summary:
  - `GluingFailureSupport` now has a representation-independent presentation
    theorem mirroring local reopen support.
  - Completeness is not free: a sound-only gluing classifier can be empty, and
    seven-facet completeness for `C_safe` does not rule out a stricter runtime
    safety predicate with an eighth obligation.

  Boundary:
  - This is still Prop-valued support, not group-valued sheaf cohomology.  No
    `δ² = 0`, quotient by coboundaries, or universal abelian-group construction
    is claimed here.
-/
