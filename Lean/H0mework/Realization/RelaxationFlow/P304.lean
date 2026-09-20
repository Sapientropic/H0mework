import H0mework.Realization.RelaxationAlgebra.P299
import H0mework.Arithmetic.PrimeShadow.P303

/-!
# Proposition 304: iteration counts form a monoid hom into noisy-OR rates

Proposition 303 proved the corrected hierarchy as equations:
iteration counts come first, and noisy-OR is the effective-rate operation
induced by serializing iterates.

This file upgrades the central equation to a standard Lean algebraic object.
For any non-absorbing base rate `σ ≠ 1`, the map

`n ↦ 1 - (1 - σ)^n`

is a monoid homomorphism from `Multiplicative ℕ` into the non-absorbing
noisy-OR rate group of Proposition 299.  Since multiplication in
`Multiplicative ℕ` is addition of ordinary natural numbers, this is exactly the
formal statement that serial iteration (`n + m`) is noisy-OR composition of
effective rates.
-/

namespace SaturationMonoid

namespace AffineRelaxation

open SatOrFieldAlgebra

variable {K : Type*} [Field K]

/-- A non-absorbing base rate stays non-absorbing after any finite number of
iterations. -/
theorem iteratedRate_ne_one_of_ne_one
    {σ : K} (hσ : σ ≠ 1) (n : ℕ) :
    iteratedRate σ n ≠ 1 := by
  have hkeep : 1 - σ ≠ 0 := by
    intro h
    exact hσ (sub_eq_zero.mp h).symm
  intro h
  have hres : (1 - σ) ^ n = 0 := by
    have hk := keep_iteratedRate σ n
    rw [h] at hk
    simpa using hk.symm
  exact (pow_ne_zero n hkeep) hres

/-- The `n`-step effective rate as a bundled non-absorbing noisy-OR rate. -/
def iteratedNonAbsorbingRate
    (σ : K) (hσ : σ ≠ 1) (n : ℕ) :
    NonAbsorbingRate (α := K) :=
  ⟨iteratedRate σ n, iteratedRate_ne_one_of_ne_one hσ n⟩

@[simp] theorem iteratedNonAbsorbingRate_val
    (σ : K) (hσ : σ ≠ 1) (n : ℕ) :
    (iteratedNonAbsorbingRate σ hσ n).1 = iteratedRate σ n := rfl

/-- THEOREM 1: zero iterations map to the noisy-OR identity rate. -/
@[simp] theorem iteratedNonAbsorbingRate_zero
    (σ : K) (hσ : σ ≠ 1) :
    iteratedNonAbsorbingRate σ hσ 0 = 1 := by
  ext
  simp [iteratedNonAbsorbingRate]

/-- THEOREM 2: one iteration maps to the original base rate. -/
@[simp] theorem iteratedNonAbsorbingRate_one
    (σ : K) (hσ : σ ≠ 1) :
    (iteratedNonAbsorbingRate σ hσ 1).1 = σ := by
  simp [iteratedNonAbsorbingRate]

/-- THEOREM 3: addition of iteration counts is multiplication in the
non-absorbing noisy-OR rate group. -/
theorem iteratedNonAbsorbingRate_add
    (σ : K) (hσ : σ ≠ 1) (n m : ℕ) :
    iteratedNonAbsorbingRate σ hσ (n + m) =
      iteratedNonAbsorbingRate σ hσ n *
        iteratedNonAbsorbingRate σ hσ m := by
  ext
  simp [iteratedNonAbsorbingRate, iteratedRate_add]

/-- THEOREM 4: the effective-rate map is a monoid homomorphism from
`Multiplicative ℕ` to the non-absorbing noisy-OR rate group. -/
def iteratedRateMonoidHom
    (σ : K) (hσ : σ ≠ 1) :
    Multiplicative ℕ →* NonAbsorbingRate (α := K) where
  toFun n := iteratedNonAbsorbingRate σ hσ n.toAdd
  map_one' := by
    ext
    simp [iteratedNonAbsorbingRate]
  map_mul' := by
    intro n m
    ext
    simp [iteratedNonAbsorbingRate, iteratedRate_add]

@[simp] theorem iteratedRateMonoidHom_apply
    (σ : K) (hσ : σ ≠ 1) (n : Multiplicative ℕ) :
    (iteratedRateMonoidHom σ hσ n).1 = iteratedRate σ n.toAdd := rfl

/-- THEOREM 5: the generator `1 : ℕ` maps to the original base rate. -/
theorem iteratedRateMonoidHom_generator
    (σ : K) (hσ : σ ≠ 1) :
    (iteratedRateMonoidHom σ hσ (Multiplicative.ofAdd 1)).1 = σ := by
  simp [iteratedRateMonoidHom, iteratedNonAbsorbingRate]

/-- THEOREM 6: the homomorphism's multiplication law is exactly P303's
serial-addition law in bundled form. -/
theorem iteratedRateMonoidHom_map_mul_val
    (σ : K) (hσ : σ ≠ 1) (n m : Multiplicative ℕ) :
    ((iteratedRateMonoidHom σ hσ (n * m)).1 : K) =
      satOrField
        (iteratedRateMonoidHom σ hσ n).1
        (iteratedRateMonoidHom σ hσ m).1 := by
  change iteratedRate σ (n * m).toAdd =
    satOrField (iteratedRate σ n.toAdd) (iteratedRate σ m.toAdd)
  simpa using iteratedRate_add σ n.toAdd m.toAdd

/-- A compact certificate for the iteration-count homomorphism. -/
structure IteratedRateMonoidHomCertificate
    (σ : K) (hσ : σ ≠ 1) where
  hom : Multiplicative ℕ →* NonAbsorbingRate (α := K) :=
    iteratedRateMonoidHom σ hσ
  apply_val :
    ∀ n : Multiplicative ℕ, (hom n).1 = iteratedRate σ n.toAdd
  generator :
    (hom (Multiplicative.ofAdd 1)).1 = σ
  map_mul_val :
    ∀ n m : Multiplicative ℕ,
      (hom (n * m)).1 = satOrField (hom n).1 (hom m).1

/-- THEOREM 7: the canonical iteration-count homomorphism certificate. -/
def iteratedRateMonoidHomCertificate
    (σ : K) (hσ : σ ≠ 1) :
    IteratedRateMonoidHomCertificate σ hσ where
  hom := iteratedRateMonoidHom σ hσ
  apply_val := iteratedRateMonoidHom_apply σ hσ
  generator := iteratedRateMonoidHom_generator σ hσ
  map_mul_val := iteratedRateMonoidHom_map_mul_val σ hσ

end AffineRelaxation
end SaturationMonoid
