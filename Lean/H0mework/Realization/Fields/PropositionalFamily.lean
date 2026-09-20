/-
  Proposition 57: memory as field convergence.

  The previous files derived seven primitive safety atoms as a product of
  obligations.  That is the algebraic reading.  This file gives the same
  object a deliberately geometric interface: a memory state is safe when a
  family of local fields converges at that state.

  This is still Prop-valued and does not claim a full sheaf/descent or
  cohomology construction.  What it proves is the next honest bridge:

    * a `FieldFamily` has a canonical convergence predicate;
    * that predicate satisfies the universal "greatest cone/fiber" property;
    * failed convergence is exactly nonempty field-failure support;
    * the seven AIppocampus facets instantiate this geometry, with `C_safe`
      as their convergence object.

  The next sheaf-theoretic step would replace these Prop-valued fields with
  sections over opens and prove descent/gluing conditions.
-/

import H0mework.Realization.Fields.TimeHolonomy

/-! ## Prop-valued field families -/

/-- A Prop-valued family of fields over a common state space.

`holds field x` means that the `field` is locally satisfied at state `x`.
This is intentionally thinner than a sheaf: it records the convergence
interface without yet modelling opens, restriction maps, or descent data. -/
structure FieldFamily (State Field : Type*) where
  holds : Field -> State -> Prop

/-- A state is a convergence point when every field in the family holds there. -/
def FieldConvergence {State Field : Type*}
    (F : FieldFamily State Field) (x : State) : Prop :=
  forall field, F.holds field x

/-- The failed field support at a state. -/
def FieldFailure {State Field : Type*}
    (F : FieldFamily State Field) (x : State) (field : Field) : Prop :=
  Not (F.holds field x)

/-- Read a field family as the already-proved product-of-obligations semantics.
This is the algebraic shadow of the geometric interface. -/
def FieldFamily.toObligationSemantics {State Field : Type*}
    (F : FieldFamily State Field) : ObligationSemantics State Field where
  holds := F.holds

/-- THEOREM 1: field convergence is definitionally the same support condition
as product safety for the associated obligation semantics. -/
theorem fieldConvergence_iff_safeByAtoms {State Field : Type*}
    (F : FieldFamily State Field) (x : State) :
    FieldConvergence F x <-> SafeByAtoms F.toObligationSemantics x := by
  rfl

/-- THEOREM 2: field failure support is the same as atom failure support for
the associated obligation semantics. -/
theorem fieldFailure_iff_atomFailure {State Field : Type*}
    (F : FieldFamily State Field) (x : State) (field : Field) :
    FieldFailure F x field <->
      AtomFailure F.toObligationSemantics x field := by
  rfl

/-- THEOREM 3: failed convergence is exactly nonempty field-failure support. -/
theorem fieldFailure_nonempty_iff_not_convergent {State Field : Type*}
    (F : FieldFamily State Field) (x : State) :
    (exists field, FieldFailure F x field) <-> Not (FieldConvergence F x) := by
  exact atomSupport_nonempty_iff_not_safe F.toObligationSemantics x

/-! ## The convergence object and its universal property -/

/-- A predicate presenting the convergence locus of a field family. -/
structure FieldConvergenceObject {State Field : Type*}
    (F : FieldFamily State Field) where
  carrier : State -> Prop
  iff_converges : forall x, carrier x <-> FieldConvergence F x

/-- The canonical convergence object. -/
def canonicalFieldConvergenceObject {State Field : Type*}
    (F : FieldFamily State Field) : FieldConvergenceObject F where
  carrier := FieldConvergence F
  iff_converges := by
    intro x
    rfl

/-- A predicate maps into the field family when every state satisfying it also
satisfies every field.  This is the Prop-level cone condition. -/
def FieldCone {State Field : Type*}
    (F : FieldFamily State Field) (D : State -> Prop) : Prop :=
  forall x, D x -> FieldConvergence F x

/-- THEOREM 4: the cone condition is exactly inclusion into the canonical
convergence locus. -/
theorem fieldCone_iff_subset_convergence {State Field : Type*}
    (F : FieldFamily State Field) (D : State -> Prop) :
    FieldCone F D <-> PredSubset D (FieldConvergence F) := by
  rfl

/-- THEOREM 5: every cone factors through the convergence object.  This is the
Prop-valued "fiber/limit" universal property used here. -/
theorem fieldConvergence_greatest_cone {State Field : Type*}
    (F : FieldFamily State Field) :
    forall D : State -> Prop, FieldCone F D -> PredSubset D (FieldConvergence F) := by
  intro D hD
  exact hD

/-- THEOREM 6: the canonical convergence object is itself a cone. -/
theorem canonicalFieldConvergence_is_cone {State Field : Type*}
    (F : FieldFamily State Field) :
    FieldCone F (FieldConvergence F) := by
  intro x hx
  exact hx

/-- THEOREM 7: any two convergence objects for the same family have the same
carrier predicate. -/
theorem fieldConvergenceObject_unique {State Field : Type*}
    {F : FieldFamily State Field}
    (A B : FieldConvergenceObject F) (x : State) :
    A.carrier x <-> B.carrier x := by
  calc
    A.carrier x <-> FieldConvergence F x := A.iff_converges x
    _ <-> B.carrier x := (B.iff_converges x).symm

/-- THEOREM 8: any presentation of convergence transports failed-field support
without changing it. -/
theorem fieldConvergenceObject_failure_support {State Field : Type*}
    {F : FieldFamily State Field}
    (C : FieldConvergenceObject F) (x : State) :
    (exists field, FieldFailure F x field) <-> Not (C.carrier x) := by
  calc
    (exists field, FieldFailure F x field) <-> Not (FieldConvergence F x) :=
      fieldFailure_nonempty_iff_not_convergent F x
    _ <-> Not (C.carrier x) := not_congr (C.iff_converges x).symm

/-! ## The seven AIppocampus fields -/

/-- The seven lower semantic atoms read geometrically as seven fields. -/
def semanticFieldFamily {State : Type*}
    (P : CSafePredicates State) : FieldFamily State SemanticAtom where
  holds := semanticHolds P

/-- THEOREM 9: the seven-field convergence locus is exactly `C_safe`. -/
theorem semanticFieldConvergence_iff_csafe {State : Type*}
    (P : CSafePredicates State) (x : State) :
    FieldConvergence (semanticFieldFamily P) x <-> CSafe P x := by
  change SafeByAtoms (semanticObligationSemantics P) x <-> CSafe P x
  exact semanticSafe_iff_csafe P x

/-- `C_safe` presented as the convergence object of the seven fields. -/
def cSafeFieldConvergenceObject {State : Type*}
    (P : CSafePredicates State) :
    FieldConvergenceObject (semanticFieldFamily P) where
  carrier := CSafe P
  iff_converges := by
    intro x
    exact (semanticFieldConvergence_iff_csafe P x).symm

/-- THEOREM 10: every domain satisfying all seven fields factors through
`C_safe`. -/
theorem sevenFieldConvergence_greatest {State : Type*}
    (P : CSafePredicates State) :
    forall D : State -> Prop,
      FieldCone (semanticFieldFamily P) D -> PredSubset D (CSafe P) := by
  intro D hD x hx
  exact (semanticFieldConvergence_iff_csafe P x).mp (hD x hx)

/-- THEOREM 11: `C_safe` is itself a cone over the seven fields. -/
theorem cSafe_is_sevenFieldCone {State : Type*}
    (P : CSafePredicates State) :
    FieldCone (semanticFieldFamily P) (CSafe P) := by
  intro x hx
  exact (semanticFieldConvergence_iff_csafe P x).mpr hx

/-- THEOREM 12: non-convergence of the seven fields is exactly nonempty lower
semantic field-failure support. -/
theorem semanticFieldFailure_nonempty_iff_not_csafe {State : Type*}
    (P : CSafePredicates State) (x : State) :
    (exists field, FieldFailure (semanticFieldFamily P) x field) <->
      Not (CSafe P x) := by
  calc
    (exists field, FieldFailure (semanticFieldFamily P) x field) <->
        Not (FieldConvergence (semanticFieldFamily P) x) :=
      fieldFailure_nonempty_iff_not_convergent (semanticFieldFamily P) x
    _ <-> Not (CSafe P x) :=
      not_congr (semanticFieldConvergence_iff_csafe P x)

/-- THEOREM 13: the field-failure support and the previously derived semantic
atom-failure support are the same lower object. -/
theorem semanticFieldFailure_iff_semanticAtomFailure {State : Type*}
    (P : CSafePredicates State) (x : State) (field : SemanticAtom) :
    FieldFailure (semanticFieldFamily P) x field <->
      AtomFailure (semanticObligationSemantics P) x field := by
  simp [FieldFailure, semanticFieldFamily, AtomFailure,
    semanticObligationSemantics]

/-- THEOREM 14: the reopen taxonomy is a presentation of seven-field failure,
not the source of the field geometry. -/
theorem semanticFieldFailure_iff_taxonomyWitness {State : Type*}
    (P : CSafePredicates State) (x : State) (field : SemanticAtom) :
    FieldFailure (semanticFieldFamily P) x field <->
      taxonomyWitness P x (semanticAtomToReopen field) := by
  calc
    FieldFailure (semanticFieldFamily P) x field <->
        AtomFailure (semanticObligationSemantics P) x field :=
      semanticFieldFailure_iff_semanticAtomFailure P x field
    _ <-> taxonomyWitness P x (semanticAtomToReopen field) :=
      semanticFailure_iff_taxonomyWitness P x field

/-!
  Summary:
  - The same seven primitive safety coordinates can be read algebraically as a
    product of obligations or geometrically as a Prop-valued field family.
  - `C_safe` is the canonical convergence/fiber object of that family: any
    domain that satisfies all seven fields factors through it, and it is unique
    up to predicate equivalence.
  - Failure of convergence is the canonical support that later presentations
    relabel as reopen taxonomy.

  Remaining debt: this is not yet sheaf descent.  To get the full geometry,
  the fields must become sections over opens, restrictions must be explicit,
  and cross-boundary holonomy should be recovered as a descent/gluing
  obstruction rather than only as Prop-valued failed support.
-/
