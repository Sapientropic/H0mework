import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.Proposition183
import H0mework.Realization.Relations.P230
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Proposition 291: shifted-power Bernstein/complete-monotonicity bridge

P147/P229/P230 prove the Laplace-transform side:

`(1 + t/r)^(-c)` is the gamma-density / gamma-measure Laplace expectation.

This file adds the derivative-sign side at the positive base coordinate.  The
canonical shifted-power curve is the positive-base power

`x ↦ x^(-c)`

read along the positive affine time coordinate `x = 1 + b*t`.  For `x > 0`,
Mathlib's `Real.iter_deriv_rpow_const` gives all iterated derivatives, and the
falling/rising Pochhammer identity gives the alternating-sign positivity.

Boundary: this is the concrete Bernstein witness used by the forgetting track.
It does not formalize the full abstract Bernstein theorem, uniqueness of the
representing measure, or the affine-pullback actual-derivative theorem for
`t ↦ (1 + b*t)^(-c)`; the latter is a natural next lemma.
-/

open scoped Real

noncomputable section

namespace ShiftedPowerCompleteMonotonicity

open Real
open Polynomial
open ShiftedPowerEffectiveRate
open GammaMixtureForgetting

/-! ## Positive-base complete monotonicity -/

/-- Rising shape coefficient `(c)(c+1)...(c+n-1)`, represented by Mathlib's
ascending Pochhammer polynomial. -/
def risingShape (shape : ℝ) (n : ℕ) : ℝ :=
  (ascPochhammer ℝ n).eval shape

/-- THEOREM 1: the rising coefficient recurrence. -/
theorem risingShape_succ (shape : ℝ) (n : ℕ) :
    risingShape shape (n + 1) = risingShape shape n * (shape + n) := by
  simpa [risingShape] using ascPochhammer_succ_eval (S := ℝ) n shape

/-- THEOREM 2: positive shape gives positive rising coefficients. -/
theorem risingShape_pos {shape : ℝ} (hshape : 0 < shape) (n : ℕ) :
    0 < risingShape shape n := by
  simpa [risingShape] using ascPochhammer_pos (S := ℝ) n shape hshape

/-- THEOREM 3: falling Pochhammer at `-shape` is sign times the positive
rising coefficient. -/
theorem descPochhammer_eval_neg_eq_sign_mul_risingShape
    (shape : ℝ) (n : ℕ) :
    (descPochhammer ℝ n).eval (-shape) =
      (-1 : ℝ) ^ n * risingShape shape n := by
  -- `h` says `risingShape shape n = (-1)^n * desc(-shape)`.
  have h :
      risingShape shape n =
        (-1 : ℝ) ^ n * (descPochhammer ℝ n).eval (-shape) := by
    simpa [risingShape] using
      ascPochhammer_eval_neg_eq_descPochhammer (R := ℝ) (-shape) n
  have hsign : (-1 : ℝ) ^ n * ((-1 : ℝ) ^ n) = 1 := by
    rw [← pow_add]
    rw [show n + n = 2 * n by omega]
    rw [pow_mul]
    norm_num
  calc
    (descPochhammer ℝ n).eval (-shape)
        = 1 * (descPochhammer ℝ n).eval (-shape) := by ring
    _ = ((-1 : ℝ) ^ n * ((-1 : ℝ) ^ n)) *
          (descPochhammer ℝ n).eval (-shape) := by
          rw [hsign]
    _ = (-1 : ℝ) ^ n * risingShape shape n := by
          rw [h]
          ring

/-- Positive-base power retention `x ↦ x^(-shape)`. -/
def positiveBasePowerRetention (shape : ℝ) (x : ℝ) : ℝ :=
  x ^ (-shape)

/-- THEOREM 4: all iterated derivatives of the positive-base power have the
closed Pochhammer form. -/
theorem iter_deriv_positiveBasePowerRetention_eq
    (shape x : ℝ) (n : ℕ) :
    deriv^[n] (fun y : ℝ => positiveBasePowerRetention shape y) x =
      (-1 : ℝ) ^ n * risingShape shape n * x ^ (-shape - (n : ℝ)) := by
  change deriv^[n] (fun y : ℝ => y ^ (-shape)) x =
    (-1 : ℝ) ^ n * risingShape shape n * x ^ (-shape - (n : ℝ))
  rw [Real.iter_deriv_rpow_const]
  rw [descPochhammer_eval_neg_eq_sign_mul_risingShape]

/-- Project-local complete monotonicity predicate on the positive base. -/
def CompletelyMonotoneOnPositiveBase (f : ℝ → ℝ) : Prop :=
  ∀ n : ℕ, ∀ x : ℝ, 0 < x → 0 ≤ (-1 : ℝ) ^ n * deriv^[n] f x

/-- THEOREM 5: `x ↦ x^(-shape)` is completely monotone on `x > 0`. -/
theorem positiveBasePowerRetention_completelyMonotone
    {shape : ℝ} (hshape : 0 < shape) :
    CompletelyMonotoneOnPositiveBase
      (fun x : ℝ => positiveBasePowerRetention shape x) := by
  intro n x hx
  rw [iter_deriv_positiveBasePowerRetention_eq]
  have hsign : 0 ≤ (-1 : ℝ) ^ n * ((-1 : ℝ) ^ n) := by
    simpa [pow_two] using sq_nonneg ((-1 : ℝ) ^ n)
  have hrising : 0 ≤ risingShape shape n :=
    le_of_lt (risingShape_pos hshape n)
  have hrpow : 0 ≤ x ^ (-shape - (n : ℝ)) :=
    le_of_lt (Real.rpow_pos_of_pos hx _)
  have hprod :
      0 ≤ (((-1 : ℝ) ^ n * ((-1 : ℝ) ^ n)) *
          risingShape shape n * x ^ (-shape - (n : ℝ))) :=
    mul_nonneg (mul_nonneg hsign hrising) hrpow
  convert hprod using 1
  ring

/-! ## Laplace/Bernstein witness bridge -/

/-- A concrete Bernstein/Laplace witness for a function on nonnegative time:
it is equal to the gamma-density Laplace transform supplied by P229. -/
def HasGammaLaplaceBernsteinWitness
    (f : ℝ → ℝ) (shape rate : ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    f t = normalizedGammaDensityLaplace shape rate t

/-- THEOREM 6: shifted-power retention has the gamma-density Laplace witness. -/
theorem shiftedPowerRetention_hasGammaLaplaceBernsteinWitness
    {shape rate : ℝ}
    (hshape : 0 < shape) (hrate : 0 < rate) :
    HasGammaLaplaceBernsteinWitness
      (fun t : ℝ => (1 + t / rate) ^ (-shape)) shape rate := by
  intro t ht
  rw [normalizedGammaDensityLaplace_eq_shiftedPower hshape hrate ht]

/-- THEOREM 7: the canonical positive-base power has complete monotonicity,
and the shifted-power time curve has the gamma-density Laplace witness. -/
theorem positiveBaseCompleteMonotone_and_shiftedPowerLaplaceWitness
    {shape rate : ℝ}
    (hshape : 0 < shape) (hrate : 0 < rate) :
    CompletelyMonotoneOnPositiveBase
        (fun x : ℝ => positiveBasePowerRetention shape x) ∧
      HasGammaLaplaceBernsteinWitness
        (fun t : ℝ => (1 + t / rate) ^ (-shape)) shape rate := by
  exact ⟨positiveBasePowerRetention_completelyMonotone hshape,
    shiftedPowerRetention_hasGammaLaplaceBernsteinWitness hshape hrate⟩

end ShiftedPowerCompleteMonotonicity
