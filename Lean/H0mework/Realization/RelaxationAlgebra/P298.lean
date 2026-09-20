import H0mework.Realization.Relaxation.P225

/-!
# Proposition 298: `satOrField` is not ring multiplication, but it has the
right group coordinate off the absorbing rate

The sigma-relaxation blueprint suggested constructing a ring on the usual
additive carrier by using `satOrField` as multiplication.  This file proves the
obstruction: with the standard zero, `satOrField` cannot satisfy the ring
zero law, because `satOrField σ 0 = σ`.

The repair is the same coordinate change used throughout the saturation track:
the residual keep-rate `keep σ = 1 - σ`.  In that coordinate, noisy-OR becomes
ordinary multiplication.  Consequently the non-absorbing rates `σ ≠ 1` have a
canonical group-like structure with identity `0` and inverse `σ / (σ - 1)`.
-/

noncomputable section

namespace SaturationMonoid
namespace SatOrFieldAlgebra

variable {α : Type*} [Field α]

/-! ## The residual coordinate -/

/-- The residual keep-rate coordinate. -/
def keep (σ : α) : α :=
  1 - σ

/-- THEOREM 1: noisy-OR is ordinary multiplication in the keep-rate coordinate.
-/
theorem keep_satOrField (σ τ : α) :
    keep (satOrField σ τ) = keep σ * keep τ := by
  unfold keep satOrField
  ring

/-- THEOREM 2: rate `0` is identity for noisy-OR, not a multiplicative zero. -/
theorem satOrField_zero_right (σ : α) :
    satOrField σ 0 = σ := by
  unfold satOrField
  ring

/-- THEOREM 3: rate `0` is also a left identity for noisy-OR. -/
theorem satOrField_zero_left (σ : α) :
    satOrField 0 σ = σ := by
  unfold satOrField
  ring

/-- Noisy-OR is associative over any field carrier. -/
theorem satOrField_assoc (σ τ υ : α) :
    satOrField (satOrField σ τ) υ =
      satOrField σ (satOrField τ υ) := by
  unfold satOrField
  ring

/-- Noisy-OR is commutative over any field carrier. -/
theorem satOrField_comm (σ τ : α) :
    satOrField σ τ = satOrField τ σ := by
  unfold satOrField
  ring

/-- A minimal package for any attempted multiplication that is both
extensionally `satOrField` and has the standard right-zero law required of ring
multiplication. -/
structure SatOrCandidateRightZeroMul where
  mul : α → α → α
  mul_eq_satOrField : ∀ σ τ, mul σ τ = satOrField σ τ
  right_zero : ∀ σ, mul σ 0 = 0

/-- THEOREM 4: `satOrField` cannot be ring multiplication with the standard
zero law on any field. -/
theorem no_satOrField_candidate_rightZeroMul :
    ¬ Nonempty (SatOrCandidateRightZeroMul (α := α)) := by
  rintro ⟨h⟩
  have hzero : h.mul 1 0 = 0 := h.right_zero 1
  have hsat : h.mul 1 0 = satOrField (1 : α) 0 :=
    h.mul_eq_satOrField 1 0
  have hone : satOrField (1 : α) 0 = 1 := satOrField_zero_right 1
  have h10 : (1 : α) = 0 := by
    rw [← hone, ← hsat]
    exact hzero
  exact one_ne_zero h10

/-! ## The non-absorbing rate group coordinate -/

/-- The formal noisy-OR inverse of a non-absorbing rate. -/
def satOrFieldInv (σ : α) : α :=
  σ / (σ - 1)

/-- THEOREM 5: the formal inverse cancels on the right whenever `σ ≠ 1`. -/
theorem satOrField_right_inv {σ : α} (hσ : σ ≠ 1) :
    satOrField σ (satOrFieldInv σ) = 0 := by
  unfold satOrFieldInv satOrField
  have hden : σ - 1 ≠ 0 := sub_ne_zero.mpr hσ
  field_simp [hden]
  ring

/-- THEOREM 6: the formal inverse cancels on the left whenever `σ ≠ 1`. -/
theorem satOrField_left_inv {σ : α} (hσ : σ ≠ 1) :
    satOrField (satOrFieldInv σ) σ = 0 := by
  rw [satOrField_comm]
  exact satOrField_right_inv hσ

/-- THEOREM 7: non-absorbing rates are closed under noisy-OR. -/
theorem satOrField_ne_one_of_ne_one {σ τ : α}
    (hσ : σ ≠ 1) (hτ : τ ≠ 1) :
    satOrField σ τ ≠ 1 := by
  intro h
  have hkσ : keep σ ≠ 0 := by
    intro hzero
    apply hσ
    exact (sub_eq_zero.mp hzero).symm
  have hkτ : keep τ ≠ 0 := by
    intro hzero
    apply hτ
    exact (sub_eq_zero.mp hzero).symm
  have hprod : keep σ * keep τ ≠ 0 := mul_ne_zero hkσ hkτ
  have hkeep : keep (satOrField σ τ) = 0 := by
    rw [h]
    unfold keep
    ring
  rw [keep_satOrField] at hkeep
  exact hprod hkeep

/-- THEOREM 8: the formal inverse of a non-absorbing rate is non-absorbing. -/
theorem satOrFieldInv_ne_one {σ : α} (hσ : σ ≠ 1) :
    satOrFieldInv σ ≠ 1 := by
  intro hinv
  have hright : satOrField σ (satOrFieldInv σ) = 0 :=
    satOrField_right_inv hσ
  rw [hinv] at hright
  have hone : satOrField σ 1 = 1 := by
    unfold satOrField
    ring
  rw [hone] at hright
  exact one_ne_zero hright

/-- Rates other than the absorbing rate `1`. -/
abbrev NonAbsorbingRate :=
  {σ : α // σ ≠ 1}

/-- The noisy-OR group identity is the no-op rate `0`. -/
def NonAbsorbingRate.one : NonAbsorbingRate (α := α) :=
  ⟨0, zero_ne_one⟩

/-- Noisy-OR multiplication on non-absorbing rates. -/
def NonAbsorbingRate.mul
    (σ τ : NonAbsorbingRate (α := α)) :
    NonAbsorbingRate (α := α) :=
  ⟨satOrField σ.1 τ.1, satOrField_ne_one_of_ne_one σ.2 τ.2⟩

/-- Noisy-OR inverse on non-absorbing rates. -/
def NonAbsorbingRate.inv
    (σ : NonAbsorbingRate (α := α)) :
    NonAbsorbingRate (α := α) :=
  ⟨satOrFieldInv σ.1, satOrFieldInv_ne_one σ.2⟩

/-- THEOREM 9: non-absorbing noisy-OR multiplication associates. -/
theorem NonAbsorbingRate.mul_assoc
    (σ τ υ : NonAbsorbingRate (α := α)) :
    NonAbsorbingRate.mul (NonAbsorbingRate.mul σ τ) υ =
      NonAbsorbingRate.mul σ (NonAbsorbingRate.mul τ υ) := by
  ext
  exact satOrField_assoc σ.1 τ.1 υ.1

/-- THEOREM 10: `0` is the left identity for non-absorbing noisy-OR
multiplication. -/
theorem NonAbsorbingRate.one_mul
    (σ : NonAbsorbingRate (α := α)) :
    NonAbsorbingRate.mul NonAbsorbingRate.one σ = σ := by
  ext
  exact satOrField_zero_left σ.1

/-- THEOREM 11: `0` is the right identity for non-absorbing noisy-OR
multiplication. -/
theorem NonAbsorbingRate.mul_one
    (σ : NonAbsorbingRate (α := α)) :
    NonAbsorbingRate.mul σ NonAbsorbingRate.one = σ := by
  ext
  exact satOrField_zero_right σ.1

/-- THEOREM 12: the formal inverse is a left inverse for non-absorbing noisy-OR
multiplication. -/
theorem NonAbsorbingRate.inv_mul
    (σ : NonAbsorbingRate (α := α)) :
    NonAbsorbingRate.mul (NonAbsorbingRate.inv σ) σ =
      NonAbsorbingRate.one := by
  ext
  exact satOrField_left_inv σ.2

/-- THEOREM 13: the formal inverse is a right inverse for non-absorbing noisy-OR
multiplication. -/
theorem NonAbsorbingRate.mul_inv
    (σ : NonAbsorbingRate (α := α)) :
    NonAbsorbingRate.mul σ (NonAbsorbingRate.inv σ) =
      NonAbsorbingRate.one := by
  ext
  exact satOrField_right_inv σ.2

/-- THEOREM 14: in the keep-rate coordinate, non-absorbing multiplication is
ordinary multiplication. -/
theorem NonAbsorbingRate.keep_mul
    (σ τ : NonAbsorbingRate (α := α)) :
    keep (NonAbsorbingRate.mul σ τ).1 = keep σ.1 * keep τ.1 :=
  keep_satOrField σ.1 τ.1

/-- A bundled certificate: noisy-OR is not a standard ring multiplication, but
the non-absorbing rates carry the expected group laws. -/
structure NonAbsorbingRateGroupCertificate where
  one : NonAbsorbingRate (α := α) := NonAbsorbingRate.one
  mul :
    NonAbsorbingRate (α := α) →
      NonAbsorbingRate (α := α) →
        NonAbsorbingRate (α := α) := NonAbsorbingRate.mul
  inv :
    NonAbsorbingRate (α := α) →
      NonAbsorbingRate (α := α) := NonAbsorbingRate.inv
  mul_assoc : ∀ σ τ υ, mul (mul σ τ) υ = mul σ (mul τ υ)
  one_mul : ∀ σ, mul one σ = σ
  mul_one : ∀ σ, mul σ one = σ
  inv_mul : ∀ σ, mul (inv σ) σ = one
  mul_inv : ∀ σ, mul σ (inv σ) = one
  keep_mul : ∀ σ τ, keep (mul σ τ).1 = keep σ.1 * keep τ.1

/-- THEOREM 15: the canonical non-absorbing-rate group certificate. -/
def nonAbsorbingRateGroupCertificate :
    NonAbsorbingRateGroupCertificate (α := α) where
  mul_assoc := NonAbsorbingRate.mul_assoc
  one_mul := NonAbsorbingRate.one_mul
  mul_one := NonAbsorbingRate.mul_one
  inv_mul := NonAbsorbingRate.inv_mul
  mul_inv := NonAbsorbingRate.mul_inv
  keep_mul := NonAbsorbingRate.keep_mul

end SatOrFieldAlgebra
end SaturationMonoid
