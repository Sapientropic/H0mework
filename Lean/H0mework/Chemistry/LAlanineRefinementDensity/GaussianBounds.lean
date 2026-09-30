import H0mework.Chemistry.LAlanineRefinementDensity.GaussianModel
import Mathlib.Algebra.Order.Floor.Ring

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceGaussianModel

open Polynomial Finset GaussianPrimitive

abbrev RationalPoint := Fin 3 → ℚ

def relativeUpper (term : Term) (centre : RationalPoint) (radius : ℚ) (axis : Fin 3) : ℚ :=
  |centre axis - term.centre axis| + radius

def relativeLower (term : Term) (centre : RationalPoint) (radius : ℚ) (axis : Fin 3) : ℚ :=
  max 0 (|centre axis - term.centre axis| - radius)

def decayLevel (term : Term) (centre : RationalPoint) (radius : ℚ) (axis : Fin 3) : Nat :=
  min 128 ⌊term.exponent * (relativeLower term centre radius axis) ^ 2⌋₊

noncomputable section

def factorEnvelope (term : Term) (d : MultiIndex) (centre : RationalPoint) (radius : ℚ)
    (axis : Fin 3) : ℚ :=
  coefficientEnvelope (jetPoly term.exponent (term.powers axis) (d axis))
    (relativeUpper term centre radius axis) / (2 : ℚ) ^ decayLevel term centre radius axis

def termEnvelope (term : Term) (d : MultiIndex) (centre : RationalPoint) (radius : ℚ) : ℚ :=
  |term.weight| * factorEnvelope term d centre radius 0 * factorEnvelope term d centre radius 1 *
    factorEnvelope term d centre radius 2

def orbitalEnvelope (terms : List Term) (d : MultiIndex) (centre : RationalPoint) (radius : ℚ) : ℚ :=
  (terms.map fun term => termEnvelope term d centre radius).sum

def InsideCube (centre : RationalPoint) (radius : ℚ) (x : Point) : Prop :=
  ∀ axis : Fin 3, |x axis - (centre axis : ℝ)| ≤ (radius : ℝ)

theorem relativeBounds (term : Term) (centre : RationalPoint) (radius : ℚ) (x : Point)
    (inside : InsideCube centre radius x) (axis : Fin 3) :
    (relativeLower term centre radius axis : ℝ) ≤ |x axis - (term.centre axis : ℝ)| ∧
    |x axis - (term.centre axis : ℝ)| ≤ (relativeUpper term centre radius axis : ℝ) := by
  have near := inside axis
  have upper := abs_add_le (x axis - (centre axis : ℝ))
    ((centre axis : ℝ) - (term.centre axis : ℝ))
  have lower := abs_sub (x axis - (term.centre axis : ℝ))
    (x axis - (centre axis : ℝ))
  have upperEq : x axis - (centre axis : ℝ) + ((centre axis : ℝ) - (term.centre axis : ℝ)) =
      x axis - (term.centre axis : ℝ) := by ring
  have lowerEq : (x axis - (term.centre axis : ℝ)) - (x axis - (centre axis : ℝ)) =
      (centre axis : ℝ) - (term.centre axis : ℝ) := by ring
  rw [upperEq] at upper
  rw [lowerEq] at lower
  simp only [relativeLower, relativeUpper, Rat.cast_max, Rat.cast_zero, Rat.cast_sub, Rat.cast_abs, Rat.cast_add]
  exact ⟨max_le (abs_nonneg _) (by linarith), by linarith⟩

theorem decayLevel_below (term : Term) (centre : RationalPoint) (radius : ℚ) (x : Point)
    (exponentNonnegative : 0 ≤ term.exponent) (inside : InsideCube centre radius x) (axis : Fin 3) :
    (decayLevel term centre radius axis : ℝ) ≤
      (term.exponent : ℝ) * (x axis - (term.centre axis : ℝ)) ^ 2 := by
  have sourceFloor : (decayLevel term centre radius axis : ℚ) ≤
      term.exponent * (relativeLower term centre radius axis) ^ 2 := by
    exact (Nat.cast_le.mpr (min_le_right _ _)).trans
      (Nat.floor_le (mul_nonneg exponentNonnegative (sq_nonneg _)))
  have sourceReal : (decayLevel term centre radius axis : ℝ) ≤
      (term.exponent : ℝ) * (relativeLower term centre radius axis : ℝ) ^ 2 := by
    exact_mod_cast sourceFloor
  have lowerNonnegative : (0 : ℝ) ≤ (relativeLower term centre radius axis : ℝ) := by
    exact_mod_cast (le_max_left (0 : ℚ) _)
  have square := pow_le_pow_left₀ lowerNonnegative (relativeBounds term centre radius x inside axis).1 2
  simp only [sq_abs] at square
  exact sourceReal.trans (mul_le_mul_of_nonneg_left square (by exact_mod_cast exponentNonnegative))

theorem factorEnvelope_nonnegative (term : Term) (d : MultiIndex) (centre : RationalPoint)
    (radius : ℚ) (radiusNonnegative : 0 ≤ radius) (axis : Fin 3) :
    0 ≤ factorEnvelope term d centre radius axis := by
  unfold factorEnvelope coefficientEnvelope
  apply div_nonneg _ (by positivity)
  apply Finset.sum_nonneg
  intro k _
  exact mul_nonneg (abs_nonneg _) (pow_nonneg (add_nonneg (abs_nonneg _) radiusNonnegative) k)

theorem factor_abs_bound (term : Term) (d : MultiIndex) (centre : RationalPoint) (radius : ℚ)
    (x : Point) (exponentNonnegative : 0 ≤ term.exponent) (inside : InsideCube centre radius x)
    (axis : Fin 3) :
    |factor term.exponent (term.powers axis) (d axis) (x axis - (term.centre axis : ℝ))| ≤
      (factorEnvelope term d centre radius axis : ℝ) :=
  rationalGaussian_abs_bound (jetPoly term.exponent (term.powers axis) (d axis)) term.exponent
    (relativeUpper term centre radius axis) _ (decayLevel term centre radius axis)
      (relativeBounds term centre radius x inside axis).2
      (decayLevel_below term centre radius x exponentNonnegative inside axis)

theorem term_abs_bound (term : Term) (d : MultiIndex) (centre : RationalPoint) (radius : ℚ)
    (x : Point) (exponentNonnegative : 0 ≤ term.exponent) (inside : InsideCube centre radius x) :
    |value term d x| ≤ (termEnvelope term d centre radius : ℝ) := by
  have h0 := factor_abs_bound term d centre radius x exponentNonnegative inside 0
  have h1 := factor_abs_bound term d centre radius x exponentNonnegative inside 1
  have h2 := factor_abs_bound term d centre radius x exponentNonnegative inside 2
  have h0nonnegative := (abs_nonneg _).trans h0
  have h1nonnegative := (abs_nonneg _).trans h1
  simp only [value, termEnvelope, Rat.cast_mul, Rat.cast_abs, abs_mul]
  gcongr

theorem orbital_abs_bound (terms : List Term) (d : MultiIndex) (centre : RationalPoint) (radius : ℚ)
    (x : Point) (exponentsNonnegative : ∀ term ∈ terms, 0 ≤ term.exponent)
    (inside : InsideCube centre radius x) :
    |orbital terms d x| ≤ (orbitalEnvelope terms d centre radius : ℝ) := by
  induction terms with
  | nil => simp [orbital, orbitalEnvelope]
  | cons term rest ih =>
    simp only [orbital, orbitalEnvelope, List.map_cons, List.sum_cons, Rat.cast_add]
    exact (abs_add_le _ _).trans (add_le_add
      (term_abs_bound term d centre radius x (exponentsNonnegative term (by simp)) inside)
      (ih (fun item member => exponentsNonnegative item (by simp [member]))))

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceGaussianModel
