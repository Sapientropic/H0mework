import Mathlib.Tactic
import H0mework.Realization.RelaxationAlgebra.P281

/-!
# Proposition 282: Poincare pairing slot kernel

P281 proves the finite count of canonical Poincare degree-pairing slots.  This
file closes the next algebraic seam: the canonical map

`degree k ↦ min k (D-k)`

identifies exactly Poincare-dual degrees and nothing else.

The result is still finite arithmetic.  It does not produce manifold
cohomology, de Rham comparison, Poincare duality, or a physical
fermion-generation interpretation.
-/

namespace SaturationMonoid
namespace AffineRelaxation
namespace GeometryConnection

/-! ## Kernel of the canonical pairing-slot map -/

/-- A degree is either its canonical representative `min k (D-k)` or the
Poincare dual of that representative. -/
theorem degree_eq_rep_or_dual_rep
    (D a : ℕ) (ha : a ≤ D) :
    a = min a (D - a) ∨ a = D - min a (D - a) := by
  by_cases hle : a ≤ D - a
  · left
    rw [Nat.min_eq_left hle]
  · right
    have hdual_le : D - a ≤ a := Nat.le_of_not_ge hle
    rw [Nat.min_eq_right hdual_le]
    omega

/-- Equality of canonical Poincare slots is exactly equality up to Poincare
duality.  This is the kernel-pair statement for the finite slot map. -/
theorem poincarePairingSlotOfDegree_eq_iff_same_or_dual
    (D : ℕ) (k l : Fin (D + 1)) :
    poincarePairingSlotOfDegree D k = poincarePairingSlotOfDegree D l ↔
      k = l ∨ k = poincareDualDegreeFin D l := by
  constructor
  · intro hslot
    have hkD : k.1 ≤ D := Nat.lt_succ_iff.mp k.2
    have hlD : l.1 ≤ D := Nat.lt_succ_iff.mp l.2
    have hrep :
        min k.1 (D - k.1) = min l.1 (D - l.1) := by
      simpa [poincarePairingSlotOfDegree] using congrArg Fin.val hslot
    rcases degree_eq_rep_or_dual_rep D k.1 hkD with hkrep | hkdual
    · rcases degree_eq_rep_or_dual_rep D l.1 hlD with hlrep | hldual
      · left
        ext
        omega
      · right
        ext
        simp [poincareDualDegreeFin]
        omega
    · rcases degree_eq_rep_or_dual_rep D l.1 hlD with hlrep | hldual
      · right
        ext
        simp [poincareDualDegreeFin]
        omega
      · left
        ext
        omega
  · intro h
    rcases h with hsame | hdual
    · rw [hsame]
    · rw [hdual, poincarePairingSlotOfDegree_dual_eq]

/-- Value-level form of the same kernel-pair theorem. -/
theorem poincarePairingSlotOfDegree_eq_iff_val_eq_or_dual
    (D : ℕ) (k l : Fin (D + 1)) :
    poincarePairingSlotOfDegree D k = poincarePairingSlotOfDegree D l ↔
      k.1 = l.1 ∨ k.1 = D - l.1 := by
  rw [poincarePairingSlotOfDegree_eq_iff_same_or_dual]
  constructor
  · intro h
    rcases h with hsame | hdual
    · left
      exact congrArg Fin.val hsame
    · right
      simpa [poincareDualDegreeFin] using congrArg Fin.val hdual
  · intro h
    rcases h with hsame | hdual
    · left
      ext
      exact hsame
    · right
      ext
      simpa [poincareDualDegreeFin] using hdual

/-!
  Boundary:
  - This proves the exact finite kernel pair of the canonical degree-slot map.
  - It does not prove any smooth/manifold de Rham theorem.
  - It does not identify the quotient slots with physical fermion generations.
-/


end GeometryConnection
end AffineRelaxation
end SaturationMonoid
