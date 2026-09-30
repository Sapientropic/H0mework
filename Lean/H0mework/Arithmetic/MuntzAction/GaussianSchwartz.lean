import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian

/-!
# The canonical Gaussian as a bundled Schwartz test

This file bundles `x ↦ exp (-π x²)` in the real Schwartz space.  The only substantial
step is uniform decay of every derivative; Mathlib's Hermite derivative formula and Gaussian
super-polynomial decay supply that bound.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual

open Filter Polynomial Set
open scoped ContDiff Nat SchwartzMap Topology

noncomputable section

private def standardGaussianRealFunction (x : ℝ) : ℝ :=
  Real.exp (-(x ^ 2 / 2))

private theorem standardGaussianRealFunction_contDiff :
    ContDiff ℝ ∞ standardGaussianRealFunction := by
  unfold standardGaussianRealFunction
  fun_prop

private theorem iteratedDeriv_standardGaussianRealFunction
    (order : ℕ) (x : ℝ) :
    iteratedDeriv order standardGaussianRealFunction x =
      (-1 : ℝ) ^ order * aeval x (Polynomial.hermite order) *
        Real.exp (-(x ^ 2 / 2)) := by
  rw [iteratedDeriv_eq_iterate]
  exact Polynomial.deriv_gaussian_eq_hermite_mul_gaussian order x

private theorem monomial_mul_standardGaussian_tendsto
    (power : ℕ) :
    Tendsto
        (fun x : ℝ => x ^ power * Real.exp (-(x ^ 2 / 2)))
        (cocompact ℝ) (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have decay := tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact
    (a := (1 / 2 : ℝ)) (by norm_num) (power : ℝ)
  convert decay using 1
  funext x
  simp only [Real.norm_eq_abs, abs_mul, abs_pow,
    abs_of_pos (Real.exp_pos _), Real.rpow_natCast]
  congr 2
  ring

private theorem standardGaussianRealFunction_decay (weight order : ℕ) :
    ∃ C : ℝ, ∀ x : ℝ,
      ‖x‖ ^ weight *
          ‖iteratedFDeriv ℝ order standardGaussianRealFunction x‖ ≤ C := by
  let p : ℝ[X] := (Polynomial.hermite order).map (Int.castRingHom ℝ)
  let weightedDerivative : ℝ → ℝ := fun x =>
    x ^ weight * iteratedDeriv order standardGaussianRealFunction x
  have polynomialRead (x : ℝ) :
      aeval x (Polynomial.hermite order) = p.eval x := by
    change Polynomial.eval₂ (Int.castRingHom ℝ) x
      (Polynomial.hermite order) = p.eval x
    exact (Polynomial.eval_map (p := Polynomial.hermite order)
      (Int.castRingHom ℝ) x).symm
  have weightedDerivative_eq :
      weightedDerivative = fun x : ℝ =>
        ∑ index ∈ p.support,
          ((-1 : ℝ) ^ order * p.coeff index) *
            (x ^ (weight + index) * Real.exp (-(x ^ 2 / 2))) := by
    funext x
    unfold weightedDerivative
    rw [iteratedDeriv_standardGaussianRealFunction, polynomialRead,
      Polynomial.eval_eq_sum, Polynomial.sum_def]
    calc
      x ^ weight *
          ((-1 : ℝ) ^ order *
            (∑ index ∈ p.support, p.coeff index * x ^ index) *
              Real.exp (-(x ^ 2 / 2))) =
          (x ^ weight * (-1 : ℝ) ^ order *
              Real.exp (-(x ^ 2 / 2))) *
            (∑ index ∈ p.support, p.coeff index * x ^ index) := by
            ring
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro index _
        rw [pow_add]
        ring
  have weightedDerivative_tendsto :
      Tendsto weightedDerivative (cocompact ℝ) (nhds 0) := by
    rw [weightedDerivative_eq]
    simpa only [mul_zero, Finset.sum_const_zero] using
      (tendsto_finsetSum p.support fun index _ =>
        (monomial_mul_standardGaussian_tendsto
          (weight + index)).const_mul
            ((-1 : ℝ) ^ order * p.coeff index))
  have weightedDerivative_continuous : Continuous weightedDerivative := by
    unfold weightedDerivative
    apply (continuous_pow weight).mul
    rw [show iteratedDeriv order standardGaussianRealFunction = fun x =>
        (-1 : ℝ) ^ order * aeval x (Polynomial.hermite order) *
          Real.exp (-(x ^ 2 / 2)) by
      funext x
      exact iteratedDeriv_standardGaussianRealFunction order x]
    fun_prop
  have weightedDerivative_bounded :
      Bornology.IsBounded (range weightedDerivative) :=
    weightedDerivative_continuous.isBounded_range_iff_isBigO.mpr
      (weightedDerivative_tendsto.isBigO_one ℝ)
  obtain ⟨C, bound⟩ := isBounded_iff_forall_norm_le.mp weightedDerivative_bounded
  refine ⟨C, fun x => ?_⟩
  have atX := bound (weightedDerivative x) ⟨x, rfl⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  simpa [weightedDerivative, norm_mul, norm_pow] using atX

/-- The standard real Gaussian `exp (-(x²/2))` as a Schwartz test. -/
def standardGaussianRealSchwartz : SchwartzMap ℝ ℝ where
  toFun := standardGaussianRealFunction
  smooth' := standardGaussianRealFunction_contDiff
  decay' := standardGaussianRealFunction_decay

@[simp]
theorem standardGaussianRealSchwartz_apply (x : ℝ) :
    standardGaussianRealSchwartz x = Real.exp (-(x ^ 2 / 2)) :=
  rfl

/-- The positive scaling which turns the standard Gaussian into `exp (-πx²)`. -/
def clozelGaussianScale : ℝ :=
  Real.sqrt (2 * Real.pi)

theorem clozelGaussianScale_pos : 0 < clozelGaussianScale := by
  exact Real.sqrt_pos.2 (mul_pos (by norm_num) Real.pi_pos)

private def clozelGaussianScaleEquiv : ℝ ≃L[ℝ] ℝ :=
  ContinuousLinearEquiv.smulLeft
    (Units.mk0 clozelGaussianScale clozelGaussianScale_pos.ne')

/-- The canonical complex Gaussian `g(x) = exp (-πx²)` as an actual Schwartz test. -/
def clozelGaussianSchwartz : SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    clozelGaussianScaleEquiv
    (SchwartzMap.postcompCLM Complex.ofRealCLM standardGaussianRealSchwartz)

@[simp]
theorem clozelGaussianSchwartz_apply (x : ℝ) :
    clozelGaussianSchwartz x =
      (Real.exp (-Real.pi * x ^ 2) : ℂ) := by
  change (Real.exp (-((clozelGaussianScale * x) ^ 2 / 2)) : ℂ) = _
  congr 1
  have scaleSquare : clozelGaussianScale ^ 2 = 2 * Real.pi := by
    exact Real.sq_sqrt (mul_nonneg (by norm_num) Real.pi_pos.le)
  rw [mul_pow, scaleSquare]
  ring_nf

end

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
