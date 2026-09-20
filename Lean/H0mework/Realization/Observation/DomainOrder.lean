/-
  Proposition 11: C_safe is the maximal safe domain.

  Proposition 10 proved that C_safe is closed and that its complement is
  classified by the reopen taxonomy.  This file proves the maximality slice:

    * any domain whose members satisfy all safety facets is a subdomain of
      C_safe;
    * any obstruction-free domain is a subdomain of C_safe;
    * any obstruction-free extension of C_safe is equal to C_safe;
    * adding even one unsafe point to C_safe necessarily creates a reopen
      taxonomy obstruction.

  This is still an abstract theorem about the declared predicates.  Runtime
  maximality still requires mechanism-faithfulness: the concrete predicates
  must be the real safety facets of the reducer/router/source system.
-/

import H0mework.Realization.Observation.Safety

/-! ## Predicate order on domains -/

/-- Domain inclusion / predicate subset. -/
def PredSubset {State : Type*} (A B : State → Prop) : Prop :=
  ∀ x, A x → B x

/-- Predicate equality by extensional equivalence. -/
def PredEq {State : Type*} (A B : State → Prop) : Prop :=
  ∀ x, A x ↔ B x

/-! ## Maximality among facet-safe domains -/

/-- A domain is facet-safe when every member satisfies each safety facet. -/
structure DomainSafetyWitness {State : Type*}
    (P : CSafePredicates State) (D : State → Prop) where
  sourceBacked : ∀ x, D x → P.sourceBacked x
  authoritySafe : ∀ x, D x → P.authoritySafe x
  graphConfluent : ∀ x, D x → P.graphConfluent x
  gaugeNonleaking : ∀ x, D x → P.gaugeNonleaking x
  contractionSafe : ∀ x, D x → P.contractionSafe x
  omegaConsistent : ∀ x, D x → P.omegaConsistent x
  freshnessSafe : ∀ x, D x → P.freshnessSafe x

/-- THEOREM 1: C_safe itself is facet-safe. -/
theorem cSafe_domainSafetyWitness {State : Type*}
    (P : CSafePredicates State) : DomainSafetyWitness P (CSafe P) where
  sourceBacked := by intro x hx; exact hx.1
  authoritySafe := by intro x hx; exact hx.2.1
  graphConfluent := by intro x hx; exact hx.2.2.1
  gaugeNonleaking := by intro x hx; exact hx.2.2.2.1
  contractionSafe := by intro x hx; exact hx.2.2.2.2.1
  omegaConsistent := by intro x hx; exact hx.2.2.2.2.2.1
  freshnessSafe := by intro x hx; exact hx.2.2.2.2.2.2

/-- THEOREM 2: any facet-safe domain is included in C_safe. -/
theorem domainSafety_subset_csafe {State : Type*}
    (P : CSafePredicates State) (D : State → Prop)
    (hD : DomainSafetyWitness P D) : PredSubset D (CSafe P) := by
  intro x hx
  exact ⟨
    hD.sourceBacked x hx,
    hD.authoritySafe x hx,
    hD.graphConfluent x hx,
    hD.gaugeNonleaking x hx,
    hD.contractionSafe x hx,
    hD.omegaConsistent x hx,
    hD.freshnessSafe x hx
  ⟩

/-- C_safe is the greatest domain among all domains that satisfy every facet. -/
def IsGreatestFacetSafeDomain {State : Type*}
    (P : CSafePredicates State) (C : State → Prop) : Prop :=
  DomainSafetyWitness P C ∧
    ∀ D : State → Prop, DomainSafetyWitness P D → PredSubset D C

/-- THEOREM 3: C_safe is the greatest facet-safe domain. -/
theorem cSafe_greatest_facet_safe_domain {State : Type*}
    (P : CSafePredicates State) :
    IsGreatestFacetSafeDomain P (CSafe P) := by
  constructor
  · exact cSafe_domainSafetyWitness P
  · intro D hD
    exact domainSafety_subset_csafe P D hD

/-! ## Maximality among obstruction-free domains -/

/-- A domain is obstruction-free when the reopen classifier returns no
    obstruction for every member. -/
def ObstructionFreeDomain {State : Type*}
    (P : CSafePredicates State) (D : State → Prop)
    [∀ x : State, Decidable (P.sourceBacked x)]
    [∀ x : State, Decidable (P.authoritySafe x)]
    [∀ x : State, Decidable (P.graphConfluent x)]
    [∀ x : State, Decidable (P.gaugeNonleaking x)]
    [∀ x : State, Decidable (P.contractionSafe x)]
    [∀ x : State, Decidable (P.omegaConsistent x)]
    [∀ x : State, Decidable (P.freshnessSafe x)] : Prop :=
  ∀ x, D x → classifyUnsafe P x = none

/-- THEOREM 4: C_safe is obstruction-free. -/
theorem cSafe_obstruction_free {State : Type*}
    (P : CSafePredicates State)
    [∀ x : State, Decidable (P.sourceBacked x)]
    [∀ x : State, Decidable (P.authoritySafe x)]
    [∀ x : State, Decidable (P.graphConfluent x)]
    [∀ x : State, Decidable (P.gaugeNonleaking x)]
    [∀ x : State, Decidable (P.contractionSafe x)]
    [∀ x : State, Decidable (P.omegaConsistent x)]
    [∀ x : State, Decidable (P.freshnessSafe x)] :
    ObstructionFreeDomain P (CSafe P) := by
  intro x hx
  exact (classifyUnsafe_none_iff_csafe P x).mpr hx

/-- THEOREM 5: any obstruction-free domain is included in C_safe. -/
theorem obstructionFree_subset_csafe {State : Type*}
    (P : CSafePredicates State) (D : State → Prop)
    [∀ x : State, Decidable (P.sourceBacked x)]
    [∀ x : State, Decidable (P.authoritySafe x)]
    [∀ x : State, Decidable (P.graphConfluent x)]
    [∀ x : State, Decidable (P.gaugeNonleaking x)]
    [∀ x : State, Decidable (P.contractionSafe x)]
    [∀ x : State, Decidable (P.omegaConsistent x)]
    [∀ x : State, Decidable (P.freshnessSafe x)]
    (hD : ObstructionFreeDomain P D) : PredSubset D (CSafe P) := by
  intro x hx
  exact (classifyUnsafe_none_iff_csafe P x).mp (hD x hx)

/-- C_safe is the greatest obstruction-free domain. -/
def IsGreatestObstructionFreeDomain {State : Type*}
    (P : CSafePredicates State) (C : State → Prop)
    [∀ x : State, Decidable (P.sourceBacked x)]
    [∀ x : State, Decidable (P.authoritySafe x)]
    [∀ x : State, Decidable (P.graphConfluent x)]
    [∀ x : State, Decidable (P.gaugeNonleaking x)]
    [∀ x : State, Decidable (P.contractionSafe x)]
    [∀ x : State, Decidable (P.omegaConsistent x)]
    [∀ x : State, Decidable (P.freshnessSafe x)] : Prop :=
  ObstructionFreeDomain P C ∧
    ∀ D : State → Prop, ObstructionFreeDomain P D → PredSubset D C

/-- THEOREM 6: C_safe is the greatest obstruction-free domain. -/
theorem cSafe_greatest_obstruction_free_domain {State : Type*}
    (P : CSafePredicates State)
    [∀ x : State, Decidable (P.sourceBacked x)]
    [∀ x : State, Decidable (P.authoritySafe x)]
    [∀ x : State, Decidable (P.graphConfluent x)]
    [∀ x : State, Decidable (P.gaugeNonleaking x)]
    [∀ x : State, Decidable (P.contractionSafe x)]
    [∀ x : State, Decidable (P.omegaConsistent x)]
    [∀ x : State, Decidable (P.freshnessSafe x)] :
    IsGreatestObstructionFreeDomain P (CSafe P) := by
  constructor
  · exact cSafe_obstruction_free P
  · intro D hD
    exact obstructionFree_subset_csafe P D hD

/-- THEOREM 7: any obstruction-free extension of C_safe is extensionally equal
    to C_safe. -/
theorem obstructionFree_extension_eq_csafe {State : Type*}
    (P : CSafePredicates State) (D : State → Prop)
    [∀ x : State, Decidable (P.sourceBacked x)]
    [∀ x : State, Decidable (P.authoritySafe x)]
    [∀ x : State, Decidable (P.graphConfluent x)]
    [∀ x : State, Decidable (P.gaugeNonleaking x)]
    [∀ x : State, Decidable (P.contractionSafe x)]
    [∀ x : State, Decidable (P.omegaConsistent x)]
    [∀ x : State, Decidable (P.freshnessSafe x)]
    (hcontains : PredSubset (CSafe P) D)
    (hfree : ObstructionFreeDomain P D) :
    PredEq D (CSafe P) := by
  intro x
  constructor
  · exact obstructionFree_subset_csafe P D hfree x
  · exact hcontains x

/-! ## No unsafe point can be added without reopening -/

/-- Add a single point to a domain. -/
def AddPoint {State : Type*} (D : State → Prop) (x : State) : State → Prop :=
  fun y => D y ∨ y = x

/-- THEOREM 8: adding an unsafe point to C_safe necessarily destroys
    obstruction-freedom. -/
theorem add_unsafe_point_not_obstruction_free {State : Type*}
    (P : CSafePredicates State) (x : State)
    [∀ x : State, Decidable (P.sourceBacked x)]
    [∀ x : State, Decidable (P.authoritySafe x)]
    [∀ x : State, Decidable (P.graphConfluent x)]
    [∀ x : State, Decidable (P.gaugeNonleaking x)]
    [∀ x : State, Decidable (P.contractionSafe x)]
    [∀ x : State, Decidable (P.omegaConsistent x)]
    [∀ x : State, Decidable (P.freshnessSafe x)]
    (hunsafe : ¬ CSafe P x) :
    ¬ ObstructionFreeDomain P (AddPoint (CSafe P) x) := by
  intro hfree
  have hx_in : AddPoint (CSafe P) x x := Or.inr rfl
  have hnone : classifyUnsafe P x = none := hfree x hx_in
  exact hunsafe ((classifyUnsafe_none_iff_csafe P x).mp hnone)

/-- THEOREM 9: adding an unsafe point yields a concrete reopen taxonomy
    witness at that point. -/
theorem add_unsafe_point_has_taxonomy {State : Type*}
    (P : CSafePredicates State) (x : State)
    [∀ x : State, Decidable (P.sourceBacked x)]
    [∀ x : State, Decidable (P.authoritySafe x)]
    [∀ x : State, Decidable (P.graphConfluent x)]
    [∀ x : State, Decidable (P.gaugeNonleaking x)]
    [∀ x : State, Decidable (P.contractionSafe x)]
    [∀ x : State, Decidable (P.omegaConsistent x)]
    [∀ x : State, Decidable (P.freshnessSafe x)]
    (hunsafe : ¬ CSafe P x) :
    ∃ r, taxonomyWitness P x r := by
  exact (not_csafe_iff_exists_taxonomy P x).mp hunsafe

/-!
  Summary:
  - C_safe is the greatest domain whose points satisfy all safety facets.
  - C_safe is also the greatest domain on which the reopen classifier is
    obstruction-free.
  - Any obstruction-free extension of C_safe is equal to C_safe.
  - Adding any point outside C_safe forces a reopen-taxonomy witness.

  What remains outside this file is mechanism-faithfulness: proving that the
  concrete runtime predicates are exactly the intended safety facets.
-/
