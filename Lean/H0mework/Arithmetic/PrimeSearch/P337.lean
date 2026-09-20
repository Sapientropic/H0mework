import H0mework.Arithmetic.PrimeSearch.P336

/-!
# Proposition 337: generic finite-pair search returns sound witnesses

P336 proves that the generic finite-pair coefficient/search frontend is
complete as a boolean decision surface for each fixed finite input.  This file
adds the operational side: when the finite search returns an index or a pair,
the returned value itself is a sound witness.

Boundary: this is still pointwise finite search.  It does not prove that any
predicate has witnesses for all inputs.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Returned-index soundness -/

/-- THEOREM 1: if the generic finite search returns an index, then that index
is bounded by `n` and satisfies the witness predicate. -/
theorem finitePairSearchIndex_sound
    {n : ℕ} {P : ℕ → ℕ → Prop} [DecidableRel P] {p : ℕ}
    (h : finitePairSearchIndex n P = some p) :
    p ≤ n ∧ P p (n - p) := by
  unfold finitePairSearchIndex at h
  have hmem : p ∈ List.range (n + 1) := List.mem_of_find?_eq_some h
  have hp_le : p ≤ n := Nat.lt_succ_iff.mp (List.mem_range.mp hmem)
  have hbool :
      (fun x : ℕ => decide (P x (n - x))) p = true := by
    exact
      @List.find?_some ℕ
        (fun x : ℕ => decide (P x (n - x)))
        p
        (List.range (n + 1))
        h
  exact ⟨hp_le, of_decide_eq_true (by simpa using hbool)⟩

/-- THEOREM 2: any bounded witness makes the generic finite search succeed.
The returned index may be an earlier witness, because `find?` returns the first
one. -/
theorem finitePairSearchIndex_complete
    {n : ℕ} {P : ℕ → ℕ → Prop} [DecidableRel P] {p : ℕ}
    (hp_le : p ≤ n) (hP : P p (n - p)) :
    (finitePairSearchIndex n P).isSome = true := by
  exact (finitePairSearchIndex_isSome_iff_exists n P).mpr
    ⟨p, hp_le, hP⟩

/-- THEOREM 3: a returned search index forces the generic coefficient to be
positive. -/
theorem finitePairSearchIndex_some_implies_coefficient_pos
    {n : ℕ} {P : ℕ → ℕ → Prop} [DecidableRel P] {p : ℕ}
    (h : finitePairSearchIndex n P = some p) :
    0 < finitePairCoefficient n P := by
  have hs := finitePairSearchIndex_sound (P := P) h
  exact (finitePairCoefficient_pos_iff_exists n P).mpr
    ⟨p, hs.1, hs.2⟩

/-! ## Returned-pair soundness -/

/-- Generic finite search returning the actual pair `(p, n-p)` rather than
only the witness index. -/
def finitePairSearchPair
    (n : ℕ) (P : ℕ → ℕ → Prop) [DecidableRel P] :
    Option (ℕ × ℕ) :=
  (finitePairSearchIndex n P).map (fun p : ℕ => (p, n - p))

/-- THEOREM 4: if the generic pair search returns `(p,q)`, then `q = n-p`,
`p ≤ n`, and `P p q`. -/
theorem finitePairSearchPair_sound
    {n : ℕ} {P : ℕ → ℕ → Prop} [DecidableRel P] {pair : ℕ × ℕ}
    (h : finitePairSearchPair n P = some pair) :
    pair.1 ≤ n ∧ pair.2 = n - pair.1 ∧ P pair.1 pair.2 := by
  unfold finitePairSearchPair at h
  cases hidx : finitePairSearchIndex n P with
  | none =>
      simp [hidx] at h
  | some p =>
      have hs := finitePairSearchIndex_sound (P := P) hidx
      simp [hidx] at h
      cases h
      exact ⟨hs.1, rfl, hs.2⟩

/-- THEOREM 5: pair-search success is the same finite witness condition as
index-search success. -/
theorem finitePairSearchPair_isSome_iff_exists
    (n : ℕ) (P : ℕ → ℕ → Prop) [DecidableRel P] :
    (finitePairSearchPair n P).isSome = true ↔
      ∃ p : ℕ, p ≤ n ∧ P p (n - p) := by
  unfold finitePairSearchPair
  cases hidx : finitePairSearchIndex n P with
  | none =>
      have hnone :
          (finitePairSearchIndex n P).isSome = false := by
        simp [hidx]
      have hno :
          ¬ ∃ p : ℕ, p ≤ n ∧ P p (n - p) := by
        intro hex
        have hs :
            (finitePairSearchIndex n P).isSome = true :=
          (finitePairSearchIndex_isSome_iff_exists n P).mpr hex
        simp [hidx] at hs
      simp [hno]
  | some p =>
      have hs :
          ∃ p : ℕ, p ≤ n ∧ P p (n - p) := by
        exact (finitePairSearchIndex_isSome_iff_exists n P).mp (by
          simp [hidx])
      simp [hs]

/-! ## Prime-pair specialization -/

/-- THEOREM 6: the generic pair search specialized to prime pairs returns a
genuine Goldbach pair. -/
theorem finitePairSearchPair_primePair_sound
    {n : ℕ} {pair : ℕ × ℕ}
    (h :
      finitePairSearchPair n
          (fun p q : ℕ => Nat.Prime p ∧ Nat.Prime q) =
        some pair) :
    GoldbachPairPredicate n pair := by
  have hs := finitePairSearchPair_sound
    (P := fun p q : ℕ => Nat.Prime p ∧ Nat.Prime q) h
  refine ⟨hs.2.2.1, hs.2.2.2, ?_⟩
  rw [hs.2.1]
  exact (Nat.add_sub_of_le hs.1).symm

/-- THEOREM 7: the generic pair search specialized to prime pairs succeeds
exactly at the ordinary pointwise Goldbach predicate. -/
theorem finitePairSearchPair_primePair_isSome_iff_goldbach
    (n : ℕ) :
    (finitePairSearchPair n
        (fun p q : ℕ => Nat.Prime p ∧ Nat.Prime q)).isSome = true ↔
      HasPrimeAdditiveDecomposition n := by
  rw [finitePairSearchPair_isSome_iff_exists]
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

/-! ## Certificate -/

/-- A compact certificate for sound returned witnesses from the generic finite
pair frontend. -/
structure P337GenericFinitePairSearchSoundnessCertificate : Prop where
  index_sound :
    ∀ {n : ℕ} {P : ℕ → ℕ → Prop} [DecidableRel P] {p : ℕ},
      finitePairSearchIndex n P = some p ->
        p ≤ n ∧ P p (n - p)
  index_complete :
    ∀ {n : ℕ} {P : ℕ → ℕ → Prop} [DecidableRel P] {p : ℕ},
      p ≤ n -> P p (n - p) ->
        (finitePairSearchIndex n P).isSome = true
  pair_sound :
    ∀ {n : ℕ} {P : ℕ → ℕ → Prop} [DecidableRel P] {pair : ℕ × ℕ},
      finitePairSearchPair n P = some pair ->
        pair.1 ≤ n ∧ pair.2 = n - pair.1 ∧ P pair.1 pair.2
  pair_isSome_iff_exists :
    ∀ (n : ℕ) (P : ℕ → ℕ → Prop) [DecidableRel P],
      (finitePairSearchPair n P).isSome = true ↔
        ∃ p : ℕ, p ≤ n ∧ P p (n - p)
  goldbach_pair_sound :
    ∀ {n : ℕ} {pair : ℕ × ℕ},
      finitePairSearchPair n
          (fun p q : ℕ => Nat.Prime p ∧ Nat.Prime q) =
        some pair ->
          GoldbachPairPredicate n pair
  goldbach_pair_search_iff :
    ∀ n : ℕ,
      (finitePairSearchPair n
          (fun p q : ℕ => Nat.Prime p ∧ Nat.Prime q)).isSome = true ↔
        HasPrimeAdditiveDecomposition n

/-- THEOREM 8: the canonical returned-witness soundness certificate. -/
theorem p337GenericFinitePairSearchSoundnessCertificate :
    P337GenericFinitePairSearchSoundnessCertificate where
  index_sound := by
    intro n P hdec p h
    exact finitePairSearchIndex_sound (P := P) h
  index_complete := by
    intro n P hdec p hp_le hP
    exact finitePairSearchIndex_complete (P := P) hp_le hP
  pair_sound := by
    intro n P hdec pair h
    exact finitePairSearchPair_sound (P := P) h
  pair_isSome_iff_exists := by
    intro n P hdec
    exact finitePairSearchPair_isSome_iff_exists n P
  goldbach_pair_sound := by
    intro n pair h
    exact finitePairSearchPair_primePair_sound h
  goldbach_pair_search_iff :=
    finitePairSearchPair_primePair_isSome_iff_goldbach

end AffineRelaxation
end SaturationMonoid
