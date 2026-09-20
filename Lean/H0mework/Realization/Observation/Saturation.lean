/-
  Saturation / noisy-OR monoid for salience composition.

  Formalizes the algebraic core of the saturation model from
  reviews/verify_saturation_model.py (500/500 property-based tests passed).
  The additive model failed 483/500; the saturation reframing fixes it because
  anti-nag becomes the structural absorbing element h=1, not a separate A-set.

  Carrier: ℤ (integers). The algebraic laws hold over any commutative ring;
  ℤ is the concrete carrier. All proofs generic: for ALL h σ₁ σ₂ ∈ ℤ.

  Laws proven:
    - bumpSat saturation operator: h' = 1 - (1-σ)*(1-h)
    - satOr explicit rate composition: σ₁ ⋆ σ₂ = 1 - (1-σ₁)*(1-σ₂)
    - residual form composes by multiplication (noisy-OR)
    - identity (σ=0 is no-op)
    - associativity
    - commutativity
    - absorbing element (h=1)
    - [0,1] closure for headroom/rates over any linear ordered field
-/

import Mathlib

/-! ## Single-section saturation operator -/

/-- Noisy-OR / saturation-rate composition. -/
def satOr (σ₁ σ₂ : ℤ) : ℤ := 1 - (1 - σ₁) * (1 - σ₂)

/-- The saturation bump: consume fraction `σ` of remaining headroom `1-h`. -/
def bumpSat (h σ : ℤ) : ℤ := 1 - (1 - σ) * (1 - h)

lemma satOr_eq (σ₁ σ₂ : ℤ) : satOr σ₁ σ₂ = σ₁ + (1 - σ₁) * σ₂ := by
  show (1 : ℤ) - (1 - σ₁) * (1 - σ₂) = σ₁ + (1 - σ₁) * σ₂
  ring

lemma bumpSat_eq (h σ : ℤ) : bumpSat h σ = h + (1 - h) * σ := by
  show (1 : ℤ) - (1 - σ) * (1 - h) = h + (1 - h) * σ
  ring

/-! ## Explicit noisy-OR monoid laws on rates -/

theorem satOr_assoc (σ₁ σ₂ σ₃ : ℤ) :
    satOr (satOr σ₁ σ₂) σ₃ = satOr σ₁ (satOr σ₂ σ₃) := by
  simp only [satOr]
  ring

theorem satOr_comm (σ₁ σ₂ : ℤ) : satOr σ₁ σ₂ = satOr σ₂ σ₁ := by
  simp only [satOr]
  ring

theorem satOr_zero_left (σ : ℤ) : satOr 0 σ = σ := by
  simp only [satOr]
  ring

theorem satOr_zero_right (σ : ℤ) : satOr σ 0 = σ := by
  simp only [satOr]
  ring

theorem satOr_one_left (σ : ℤ) : satOr 1 σ = 1 := by
  simp only [satOr]
  ring

theorem satOr_one_right (σ : ℤ) : satOr σ 1 = 1 := by
  simp only [satOr]
  ring

/-! ## Noisy-OR composition law -/

/-- Composing two bumps is one bump of rate `1 - (1-σ₁)*(1-σ₂)` (noisy-OR). -/
lemma bumpSat_compose (h σ₁ σ₂ : ℤ) :
    bumpSat (bumpSat h σ₁) σ₂ = bumpSat h (satOr σ₁ σ₂) := by
  simp only [bumpSat, satOr]
  ring

/-- Composition is ORDER-INDEPENDENT. -/
theorem bumpSat_compose_comm (h σ₁ σ₂ : ℤ) :
    bumpSat (bumpSat h σ₁) σ₂ = bumpSat (bumpSat h σ₂) σ₁ := by
  show (1 : ℤ) - (1 - σ₂) * (1 - (1 - (1 - σ₁) * (1 - h))) =
       (1 : ℤ) - (1 - σ₁) * (1 - (1 - (1 - σ₂) * (1 - h)))
  ring

/-- Composition is ASSOCIATIVE. -/
theorem bumpSat_compose_assoc (h σ₁ σ₂ σ₃ : ℤ) :
    bumpSat (bumpSat (bumpSat h σ₁) σ₂) σ₃ =
    bumpSat (bumpSat h (satOr σ₁ σ₂)) σ₃ := by
  simp only [bumpSat, satOr]
  ring

/-! ## Identity: σ=0 is a no-op -/

theorem bumpSat_zero (h : ℤ) : bumpSat h 0 = h := by
  show (1 : ℤ) - (1 - 0) * (1 - h) = h
  ring

/-! ## Absorbing element: h=1 - bumping a saturated section does nothing -/

/-- Anti-nag, structurally: h=1 absorbing. No separate A-set needed. -/
theorem bumpSat_one_absorbing (σ : ℤ) : bumpSat 1 σ = 1 := by
  show (1 : ℤ) - (1 - σ) * (1 - 1) = 1
  ring

/-! ## Residual-rate form -/

/-- Headroom residual shrinks by multiplying residual rates. -/
lemma residual_mul (h σ : ℤ) : (1 : ℤ) - bumpSat h σ = (1 - σ) * (1 - h) := by
  show (1 : ℤ) - (1 - (1 - σ) * (1 - h)) = (1 - σ) * (1 - h)
  ring

/-- `bumpSat` is conjugate to multiplication via the residual map. -/
theorem bumpSat_is_mul_conjugate (h σ₁ σ₂ : ℤ) :
    (1 : ℤ) - bumpSat (bumpSat h σ₁) σ₂ = (1 - σ₁) * (1 - σ₂) * (1 - h) := by
  rw [residual_mul, residual_mul]
  ring

/-! ## [0,1] closure on any linear ordered field -/

section OrderedField

variable {α : Type*} [Field α]

/-- Noisy-OR / saturation-rate composition on an ordered field carrier. -/
def satOrField (σ₁ σ₂ : α) : α := 1 - (1 - σ₁) * (1 - σ₂)

/-- Saturation bump on an ordered field carrier. -/
def bumpSatField (h σ : α) : α := 1 - (1 - σ) * (1 - h)

lemma satOrField_eq (σ₁ σ₂ : α) : satOrField σ₁ σ₂ = σ₁ + (1 - σ₁) * σ₂ := by
  show (1 : α) - (1 - σ₁) * (1 - σ₂) = σ₁ + (1 - σ₁) * σ₂
  ring

lemma bumpSatField_eq (h σ : α) : bumpSatField h σ = h + (1 - h) * σ := by
  show (1 : α) - (1 - σ) * (1 - h) = h + (1 - h) * σ
  ring

variable [LinearOrder α] [IsStrictOrderedRing α]

/-- Noisy-OR rate composition preserves the runtime interval [0,1]. -/
theorem satOrField_mem_Icc
    (σ₁ σ₂ : α)
    (hσ₁0 : 0 ≤ σ₁) (hσ₁1 : σ₁ ≤ 1)
    (hσ₂0 : 0 ≤ σ₂) (hσ₂1 : σ₂ ≤ 1) :
    0 ≤ satOrField σ₁ σ₂ ∧ satOrField σ₁ σ₂ ≤ 1 := by
  rw [satOrField_eq]
  constructor
  · have hterm_nonneg : 0 ≤ (1 - σ₁) * σ₂ := by
      exact mul_nonneg (by nlinarith) hσ₂0
    nlinarith
  · have hterm_le : (1 - σ₁) * σ₂ ≤ (1 - σ₁) * 1 := by
      exact mul_le_mul_of_nonneg_left hσ₂1 (by nlinarith)
    nlinarith

/-- A saturation bump preserves the runtime interval [0,1]. -/
theorem bumpSatField_mem_Icc
    (h σ : α)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    0 ≤ bumpSatField h σ ∧ bumpSatField h σ ≤ 1 := by
  rw [bumpSatField_eq]
  constructor
  · have hterm_nonneg : 0 ≤ (1 - h) * σ := by
      exact mul_nonneg (by nlinarith) hσ0
    nlinarith
  · have hterm_le : (1 - h) * σ ≤ (1 - h) * 1 := by
      exact mul_le_mul_of_nonneg_left hσ1 (by nlinarith)
    nlinarith

end OrderedField
