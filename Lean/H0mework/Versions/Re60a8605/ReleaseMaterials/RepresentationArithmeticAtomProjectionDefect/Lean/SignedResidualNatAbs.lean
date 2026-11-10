import Mathlib.Algebra.Group.Nat.Even

/-!
# Signed residual `natAbs` helper lemmas

Small shared arithmetic facts for endpoint-code energy proofs of the form
`|(a : Int) - (a + k : Int)| = k`.
-/

namespace RepresentationArithmeticAtomProjectionDefect

/-- Absolute residual of `(a, a+k)` in integer form. -/
theorem natAbs_subNatNat_add_right (a k : Nat) :
    Int.natAbs (Int.subNatNat a (a + k)) = k := by
  unfold Int.subNatNat
  cases k with
  | zero =>
      rw [Nat.add_zero]
      rw [Nat.sub_self]
      rfl
  | succ k =>
      have hsub : (a + Nat.succ k) - a = Nat.succ k :=
        Nat.add_sub_cancel_left a (Nat.succ k)
      rw [hsub]
      rfl

/-- Absolute residual after coercing the centered natural expression to `Int`.
-/
theorem natAbs_center_minus_center_add (a k : Nat) :
    Int.natAbs (((a : Nat) : Int) - ((a + k : Nat) : Int)) = k := by
  have hsub := Int.subNatNat_eq_coe (m := a) (n := a + k)
  rw [← hsub]
  exact natAbs_subNatNat_add_right a k


end RepresentationArithmeticAtomProjectionDefect
