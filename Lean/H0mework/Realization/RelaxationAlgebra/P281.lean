import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Init
import Mathlib.Tactic
import H0mework.Physics.Generation.P280

/-!
# Proposition 281: general Poincare pairing slot count

P280 proves the 4D Poincare-duality generation-slot arithmetic.  This file
removes a remaining special-case wrinkle: for any top dimension `D`, the
degree-pairing involution `k ↔ D-k` has `D / 2 + 1` canonical slots.

The result is still certificate-relative.  It does not construct de Rham
cohomology, prove Poincare duality for manifolds, or identify the resulting
slots with physical fermion generations.  It proves the finite arithmetic that
any such producer must respect:

* the canonical representative of a degree is `min k (D-k)`;
* the number of representatives is `D / 2 + 1`;
* the representative is invariant under Poincare duality;
* every representative is realized by some degree;
* there is no injection from `D / 2 + 2` independent slots into the pairing
  slots.
-/

namespace SaturationMonoid
namespace AffineRelaxation
namespace GeometryConnection

/-! ## General finite pairing slots -/

/-- The number of degree-pairing orbits for `k ↔ D-k`.

For natural numbers this is `⌊D/2⌋ + 1`, written as `D / 2 + 1`. -/
def poincarePairingSlotCount (D : ℕ) : ℕ :=
  D / 2 + 1

/-- Canonical finite carrier for Poincare degree-pairing slots in dimension
`D`.  The slot `r` represents the orbit `{r, D-r}` when `r ≤ D/2`. -/
abbrev PoincarePairingSlot (D : ℕ) : Type :=
  Fin (poincarePairingSlotCount D)

/-- The slot carrier has exactly `D / 2 + 1` elements. -/
theorem poincarePairingSlot_card (D : ℕ) :
    Fintype.card (PoincarePairingSlot D) = D / 2 + 1 := by
  change Fintype.card (Fin (D / 2 + 1)) = D / 2 + 1
  rw [Fintype.card_fin]

/-- A degree-pairing representative `min k (D-k)` always lies below `D/2`. -/
theorem min_degree_dual_le_half (D k : ℕ) (hk : k ≤ D) :
    min k (D - k) ≤ D / 2 := by
  rw [Nat.le_div_two_iff_mul_two_le]
  have hleft : min k (D - k) ≤ k := Nat.min_le_left _ _
  have hright : min k (D - k) ≤ D - k := Nat.min_le_right _ _
  omega

/-- The degree paired with a finite degree `k : Fin (D+1)`. -/
def poincareDualDegreeFin (D : ℕ) : Fin (D + 1) -> Fin (D + 1) :=
  fun k =>
    ⟨D - k.1, by
      have hk : k.1 ≤ D := Nat.lt_succ_iff.mp k.2
      omega⟩

/-- The finite-degree version agrees with `poincareDualDegree` on values. -/
theorem poincareDualDegreeFin_val (D : ℕ) (k : Fin (D + 1)) :
    (poincareDualDegreeFin D k).1 = poincareDualDegree D k.1 := by
  rfl

/-- Finite Poincare degree-pairing is involutive. -/
theorem poincareDualDegreeFin_involutive (D : ℕ) (k : Fin (D + 1)) :
    poincareDualDegreeFin D (poincareDualDegreeFin D k) = k := by
  ext
  have hk : k.1 ≤ D := Nat.lt_succ_iff.mp k.2
  simp [poincareDualDegreeFin]
  omega

/-- The canonical Poincare pairing slot associated to a degree `0..D`. -/
def poincarePairingSlotOfDegree (D : ℕ) :
    Fin (D + 1) -> PoincarePairingSlot D :=
  fun k =>
    ⟨min k.1 (D - k.1), by
      have hk : k.1 ≤ D := Nat.lt_succ_iff.mp k.2
      exact Nat.lt_succ_of_le (min_degree_dual_le_half D k.1 hk)⟩

/-- The slot representative is literally `min k (D-k)`. -/
theorem poincarePairingSlotOfDegree_val (D : ℕ) (k : Fin (D + 1)) :
    (poincarePairingSlotOfDegree D k).1 = min k.1 (D - k.1) := by
  rfl

/-- Poincare-paired degrees have the same canonical slot. -/
theorem poincarePairingSlotOfDegree_dual_eq
    (D : ℕ) (k : Fin (D + 1)) :
    poincarePairingSlotOfDegree D (poincareDualDegreeFin D k) =
      poincarePairingSlotOfDegree D k := by
  ext
  have hk : k.1 ≤ D := Nat.lt_succ_iff.mp k.2
  simp [poincarePairingSlotOfDegree, poincareDualDegreeFin]
  have hsub : D - (D - k.1) = k.1 := by
    omega
  rw [hsub, Nat.min_comm]

/-- Every canonical Poincare pairing slot is represented by a degree. -/
theorem poincarePairingSlotOfDegree_surjective (D : ℕ) :
    Function.Surjective (poincarePairingSlotOfDegree D) := by
  intro s
  have hs_half : s.1 ≤ D / 2 := Nat.lt_succ_iff.mp s.2
  have hsD : s.1 ≤ D := by
    have hdiv : D / 2 ≤ D := Nat.div_le_self _ _
    omega
  refine ⟨⟨s.1, Nat.lt_succ_of_le hsD⟩, ?_⟩
  ext
  simp [poincarePairingSlotOfDegree]
  have htwo : (s.1 : ℤ) * 2 ≤ D :=
    (Nat.le_div_two_iff_mul_two_le.mp hs_half)
  have hledual : s.1 ≤ D - s.1 := by
    omega
  exact hledual

/-- One more independent slot than the Poincare pairing count cannot inject
into the canonical slot carrier. -/
theorem no_extra_independent_poincare_slots (D : ℕ) :
    IsEmpty (Fin (poincarePairingSlotCount D + 1) ↪
      PoincarePairingSlot D) := by
  refine ⟨?_⟩
  intro e
  have hle :
      Fintype.card (Fin (poincarePairingSlotCount D + 1)) ≤
        Fintype.card (PoincarePairingSlot D) :=
    Fintype.card_le_of_embedding e
  rw [Fintype.card_fin, poincarePairingSlot_card] at hle
  simp [poincarePairingSlotCount] at hle

/-! ## 4D specialization -/

/-- The general count specializes to three slots in dimension four. -/
theorem four_poincarePairingSlotCount_eq_three :
    poincarePairingSlotCount 4 = 3 := by
  norm_num [poincarePairingSlotCount]

/-- P281 specializes to the P280 no-fourth-independent-slot statement. -/
theorem no_four_independent_poincare_slots_from_general_count :
    IsEmpty (Fin 4 ↪ PoincarePairingSlot 4) := by
  change IsEmpty (Fin (poincarePairingSlotCount 4 + 1) ↪
    PoincarePairingSlot 4)
  exact no_extra_independent_poincare_slots 4

/-- The concrete three-slot type used in P280 is equivalent to the general
slot carrier specialized at dimension four. -/
def fourDimensionalPoincareSlotEquivGeneral :
    FourDimensionalPoincareSlot ≃ PoincarePairingSlot 4 where
  toFun
    | .scalarVolume => ⟨0, by norm_num [poincarePairingSlotCount]⟩
    | .connectionCurrent => ⟨1, by norm_num [poincarePairingSlotCount]⟩
    | .curvature => ⟨2, by norm_num [poincarePairingSlotCount]⟩
  invFun s :=
    match s with
    | ⟨0, _⟩ => .scalarVolume
    | ⟨1, _⟩ => .connectionCurrent
    | ⟨2, _⟩ => .curvature
    | ⟨n + 3, h⟩ => by
        norm_num [poincarePairingSlotCount] at h
  left_inv := by
    intro s
    cases s <;> rfl
  right_inv := by
    intro s
    rcases s with ⟨n, hn⟩
    have hn' : n < 3 := by
      simpa [poincarePairingSlotCount] using hn
    interval_cases n <;> rfl

/-!
  Boundary:
  - This file proves the finite orbit count of the degree involution
    `k ↔ D-k`.
  - It does not prove the de Rham theorem or Poincare duality for manifolds.
  - It does not prove that Standard Model fermion generations are these slots.
-/


end GeometryConnection
end AffineRelaxation
end SaturationMonoid
