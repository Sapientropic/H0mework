import H0mework.Arithmetic.PrimeSearch.P335

/-!
# Proposition 336: generic finite-pair coefficient/search frontend

P332 introduced a Goldbach-specific coefficient

`Σ_{p≤n} 1_Prime(p) * 1_Prime(n-p)`.

The reusable part is more general: for any decidable binary witness predicate
`P p q`, the finite coefficient

`Σ_{p≤n} 1_{P p (n-p)}`

is positive exactly when a finite witness exists, and exactly when the finite
search over `p ≤ n` succeeds.  Goldbach is the specialization
`P p q := Prime p ∧ Prime q`.

Boundary: this is a finite frontend theorem.  It proves no global witness
existence theorem for any particular predicate.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Generic finite-pair coefficient and search -/

/-- Generic finite-pair coefficient over witnesses of the form `P p (n-p)`. -/
def finitePairCoefficient
    (n : ℕ) (P : ℕ → ℕ → Prop) [DecidableRel P] : ℕ :=
  ((List.range (n + 1)).map
    (fun p : ℕ => if P p (n - p) then 1 else 0)).sum

/-- Generic finite search returning the first index `p ≤ n` satisfying
`P p (n-p)`, if one exists. -/
def finitePairSearchIndex
    (n : ℕ) (P : ℕ → ℕ → Prop) [DecidableRel P] : Option ℕ :=
  (List.range (n + 1)).find? (fun p : ℕ => decide (P p (n - p)))

/-- THEOREM 1: the generic finite-pair coefficient is positive exactly when
there exists a bounded witness index. -/
theorem finitePairCoefficient_pos_iff_exists
    (n : ℕ) (P : ℕ → ℕ → Prop) [DecidableRel P] :
    0 < finitePairCoefficient n P ↔
      ∃ p : ℕ, p ≤ n ∧ P p (n - p) := by
  rw [finitePairCoefficient, list_sum_map_pos_iff_exists]
  constructor
  · rintro ⟨p, hmem, hpos⟩
    have hp_le : p ≤ n := Nat.lt_succ_iff.mp (List.mem_range.mp hmem)
    have hP : P p (n - p) := by
      by_cases hp : P p (n - p)
      · exact hp
      · simp [hp] at hpos
    exact ⟨p, hp_le, hP⟩
  · rintro ⟨p, hp_le, hP⟩
    refine ⟨p, ?_, ?_⟩
    · rw [List.mem_range]
      exact Nat.lt_succ_of_le hp_le
    · simp [hP]

/-- THEOREM 2: the generic finite search succeeds exactly when there exists a
bounded witness index. -/
theorem finitePairSearchIndex_isSome_iff_exists
    (n : ℕ) (P : ℕ → ℕ → Prop) [DecidableRel P] :
    (finitePairSearchIndex n P).isSome = true ↔
      ∃ p : ℕ, p ≤ n ∧ P p (n - p) := by
  rw [finitePairSearchIndex, List.find?_isSome]
  constructor
  · rintro ⟨p, hmem, hbool⟩
    have hp_le : p ≤ n := Nat.lt_succ_iff.mp (List.mem_range.mp hmem)
    have hP : P p (n - p) := of_decide_eq_true hbool
    exact ⟨p, hp_le, hP⟩
  · rintro ⟨p, hp_le, hP⟩
    refine ⟨p, ?_, ?_⟩
    · rw [List.mem_range]
      exact Nat.lt_succ_of_le hp_le
    · exact decide_eq_true hP

/-- THEOREM 3: coefficient positivity and finite-search success are the same
generic frontend. -/
theorem finitePairCoefficient_pos_iff_search
    (n : ℕ) (P : ℕ → ℕ → Prop) [DecidableRel P] :
    0 < finitePairCoefficient n P ↔
      (finitePairSearchIndex n P).isSome = true := by
  exact (finitePairCoefficient_pos_iff_exists n P).trans
    (finitePairSearchIndex_isSome_iff_exists n P).symm

/-! ## Goldbach as the prime-pair instance -/

/-- THEOREM 4: P332's Goldbach coefficient is the prime-pair instance of the
generic finite-pair coefficient. -/
theorem finitePairCoefficient_primePair_eq_goldbachConvolutionCoefficient
    (n : ℕ) :
    finitePairCoefficient n (fun p q : ℕ => Nat.Prime p ∧ Nat.Prime q) =
      goldbachConvolutionCoefficient n := by
  unfold finitePairCoefficient goldbachConvolutionCoefficient primeIndicator
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _hmem
  by_cases hp : Nat.Prime p <;>
    by_cases hq : Nat.Prime (n - p) <;>
      simp [hp, hq]

/-- THEOREM 5: the generic finite search, specialized to prime pairs, is
exactly the pointwise Goldbach predicate. -/
theorem finitePairSearchIndex_primePair_isSome_iff_goldbach
    (n : ℕ) :
    (finitePairSearchIndex n
        (fun p q : ℕ => Nat.Prime p ∧ Nat.Prime q)).isSome = true ↔
      HasPrimeAdditiveDecomposition n := by
  rw [finitePairSearchIndex_isSome_iff_exists]
  constructor
  · rintro ⟨p, hp_le, hpq⟩
    refine ⟨⟨p, hpq.1⟩, ⟨n - p, hpq.2⟩, ?_⟩
    exact (Nat.add_sub_of_le hp_le).symm
  · rintro ⟨p, q, hsum⟩
    refine ⟨p.1, ?_, ?_⟩
    · rw [hsum]
      exact Nat.le_add_right p.1 q.1
    · have hsub : (p.1 + q.1) - p.1 = q.1 :=
        Nat.add_sub_cancel_left p.1 q.1
      constructor
      · exact p.2
      · simpa [hsum, hsub] using q.2

/-- THEOREM 6: P332's Goldbach coefficient theorem factors through the generic
finite-pair frontend. -/
theorem goldbachConvolutionCoefficient_pos_iff_via_finitePairCoefficient
    (n : ℕ) :
    0 < goldbachConvolutionCoefficient n ↔
      0 < finitePairCoefficient n
        (fun p q : ℕ => Nat.Prime p ∧ Nat.Prime q) := by
  rw [finitePairCoefficient_primePair_eq_goldbachConvolutionCoefficient]

/-! ## Certificate -/

/-- A compact certificate for the reusable finite-pair frontend. -/
structure P336GenericFinitePairFrontendCertificate : Prop where
  coefficient_pos_iff_exists :
    ∀ (n : ℕ) (P : ℕ → ℕ → Prop) [DecidableRel P],
      0 < finitePairCoefficient n P ↔
        ∃ p : ℕ, p ≤ n ∧ P p (n - p)
  search_isSome_iff_exists :
    ∀ (n : ℕ) (P : ℕ → ℕ → Prop) [DecidableRel P],
      (finitePairSearchIndex n P).isSome = true ↔
        ∃ p : ℕ, p ≤ n ∧ P p (n - p)
  coefficient_pos_iff_search :
    ∀ (n : ℕ) (P : ℕ → ℕ → Prop) [DecidableRel P],
      0 < finitePairCoefficient n P ↔
        (finitePairSearchIndex n P).isSome = true
  goldbach_coefficient_instance :
    ∀ n : ℕ,
      finitePairCoefficient n
          (fun p q : ℕ => Nat.Prime p ∧ Nat.Prime q) =
        goldbachConvolutionCoefficient n
  goldbach_search_instance :
    ∀ n : ℕ,
      (finitePairSearchIndex n
          (fun p q : ℕ => Nat.Prime p ∧ Nat.Prime q)).isSome = true ↔
        HasPrimeAdditiveDecomposition n

/-- THEOREM 7: the canonical generic finite-pair frontend certificate. -/
theorem p336GenericFinitePairFrontendCertificate :
    P336GenericFinitePairFrontendCertificate where
  coefficient_pos_iff_exists := by
    intro n P hdec
    exact finitePairCoefficient_pos_iff_exists n P
  search_isSome_iff_exists := by
    intro n P hdec
    exact finitePairSearchIndex_isSome_iff_exists n P
  coefficient_pos_iff_search := by
    intro n P hdec
    exact finitePairCoefficient_pos_iff_search n P
  goldbach_coefficient_instance :=
    finitePairCoefficient_primePair_eq_goldbachConvolutionCoefficient
  goldbach_search_instance :=
    finitePairSearchIndex_primePair_isSome_iff_goldbach

end AffineRelaxation
end SaturationMonoid
