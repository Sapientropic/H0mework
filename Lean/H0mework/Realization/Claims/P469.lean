/-
  Proposition 469: complement dissolves the independent-null alternative.

  P314 proves the common complement spine `x ↦ 1 - x`.  P467/P468 then show
  that apparent growth-to-one is the complementary reading of zero-target
  relaxation.

  This file records the sharp algebraic boundary behind the slogan

      loss is gain; null is not an independent alternative.

  In a complement-closed carrier, `{0}` alone is not closed unless the carrier
  is degenerate (`0 = 1`).  The smallest endpoint story is the pair `{0, 1}`:
  complement swaps them.  Thus `Null` and `Everything` are not independent
  singletons in this algebra; they are a complement pair.

  Boundary: this is the algebraic content.  It does not prove metaphysical
  claims; it proves the endpoint/complement closure facts that the prose must
  respect.
-/

import H0mework.Physics.SourceContracts.P468
import H0mework.Realization.Fibres.P314

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Loss/gain endpoint algebra -/

/-- A subset is closed under the complement involution. -/
def ComplementClosed {K : Type*} [One K] [Sub K] (S : Set K) : Prop :=
  ∀ ⦃x : K⦄, x ∈ S -> complement x ∈ S

/-- The two endpoint states: null and everything. -/
def nullEverythingPair (K : Type*) [Zero K] [One K] : Set K :=
  ({0, 1} : Set K)

/-- THEOREM 1: keep/loss plus rate/gain is one. -/
theorem complement_add_self
    {K : Type*} [Ring K] (x : K) :
    complement x + x = 1 := by
  simp [complement]

/-- THEOREM 2: the same partition in the other order. -/
theorem self_add_complement
    {K : Type*} [Ring K] (x : K) :
    x + complement x = 1 := by
  simpa [add_comm] using complement_add_self (K := K) x

/-- THEOREM 3: null complements to everything. -/
theorem complement_zero
    {K : Type*} [Ring K] :
    complement (0 : K) = 1 := by
  simp [complement]

/-- THEOREM 4: everything complements to null. -/
theorem complement_one
    {K : Type*} [Ring K] :
    complement (1 : K) = 0 := by
  simp [complement]

/-- THEOREM 5: a bump from null produces exactly the rate. -/
theorem bumpSatField_zero_eq_rate
    {K : Type*} [Field K] (sigma : K) :
    bumpSatField (0 : K) sigma = sigma := by
  unfold bumpSatField
  ring

/-- THEOREM 6: a fully saturated endpoint is absorbing. -/
theorem bumpSatField_one_absorbing
    {K : Type*} [Field K] (sigma : K) :
    bumpSatField (1 : K) sigma = 1 := by
  unfold bumpSatField
  ring

/-- THEOREM 7: a singleton null carrier is complement-closed only in the
degenerate case `0 = 1`. -/
theorem singleton_zero_complementClosed_iff_zero_eq_one
    {K : Type*} [Ring K] :
    ComplementClosed ({0} : Set K) ↔ (0 : K) = 1 := by
  constructor
  · intro hclosed
    have hmem : complement (0 : K) ∈ ({0} : Set K) := hclosed (by simp)
    have hone_zero : (1 : K) = 0 := by
      simpa [complement] using hmem
    exact hone_zero.symm
  · intro hzero_one x hx
    have hx0 : x = (0 : K) := by simpa using hx
    subst x
    have hone_zero : (1 : K) = 0 := hzero_one.symm
    simp [complement, hone_zero]

/-- THEOREM 8: in a nontrivial carrier, null alone is not complement-closed. -/
theorem not_complementClosed_singleton_zero_of_nontrivial
    {K : Type*} [Ring K] [Nontrivial K] :
    ¬ ComplementClosed ({0} : Set K) := by
  intro hclosed
  have hzero_one : (0 : K) = 1 :=
    (singleton_zero_complementClosed_iff_zero_eq_one).mp hclosed
  exact zero_ne_one hzero_one

/-- THEOREM 9: a singleton everything carrier is complement-closed only in the
degenerate case `0 = 1`. -/
theorem singleton_one_complementClosed_iff_zero_eq_one
    {K : Type*} [Ring K] :
    ComplementClosed ({1} : Set K) ↔ (0 : K) = 1 := by
  constructor
  · intro hclosed
    have hmem : complement (1 : K) ∈ ({1} : Set K) := hclosed (by simp)
    simpa [complement] using hmem
  · intro hzero_one x hx
    have hx1 : x = (1 : K) := by simpa using hx
    subst x
    simp [complement, hzero_one]

/-- THEOREM 10: in a nontrivial carrier, everything alone is not
complement-closed. -/
theorem not_complementClosed_singleton_one_of_nontrivial
    {K : Type*} [Ring K] [Nontrivial K] :
    ¬ ComplementClosed ({1} : Set K) := by
  intro hclosed
  have hzero_one : (0 : K) = 1 :=
    (singleton_one_complementClosed_iff_zero_eq_one).mp hclosed
  exact zero_ne_one hzero_one

/-- THEOREM 11: the null/everything pair is complement-closed. -/
theorem nullEverythingPair_complementClosed
    {K : Type*} [Ring K] :
    ComplementClosed (nullEverythingPair K) := by
  intro x hx
  rcases hx with hx | hx
  · subst x
    simp [nullEverythingPair, complement]
  · subst x
    simp [nullEverythingPair, complement]

/-- THEOREM 12: a self-complementary scalar is exactly the midpoint `1/2`.
The endpoint pair is therefore not self-dual pointwise; it is dual as a pair. -/
theorem complement_eq_self_iff_eq_half
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (x : K) :
    complement x = x ↔ x = (1 : K) / 2 := by
  constructor
  · intro h
    unfold complement at h
    nlinarith
  · intro h
    rw [h]
    unfold complement
    ring

/-! ## Bundled receipt -/

/-- A compact certificate for the complement/null boundary. -/
structure ComplementNullBoundaryReceipt (K : Type*) [Ring K] : Prop where
  complement_partition :
    ∀ x : K, complement x + x = 1
  null_to_everything :
    complement (0 : K) = 1
  everything_to_null :
    complement (1 : K) = 0
  singleton_null_closed_iff_degenerate :
    ComplementClosed ({0} : Set K) ↔ (0 : K) = 1
  singleton_everything_closed_iff_degenerate :
    ComplementClosed ({1} : Set K) ↔ (0 : K) = 1
  pair_closed :
    ComplementClosed (nullEverythingPair K)

/-- THEOREM 13: every ring carrier has the complement/null boundary receipt. -/
theorem complementNullBoundaryReceipt
    (K : Type*) [Ring K] :
    ComplementNullBoundaryReceipt K where
  complement_partition := complement_add_self
  null_to_everything := complement_zero
  everything_to_null := complement_one
  singleton_null_closed_iff_degenerate :=
    singleton_zero_complementClosed_iff_zero_eq_one
  singleton_everything_closed_iff_degenerate :=
    singleton_one_complementClosed_iff_zero_eq_one
  pair_closed := nullEverythingPair_complementClosed

end AffineRelaxation
end SaturationMonoid
