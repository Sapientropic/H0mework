import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.TruncatedFourier.Radius.Scaling.Variation.KernelDerivative
import Mathlib.Analysis.Complex.Exponential

/-! Uniform scalar-kernel remainder for the recharted truncated Fourier family. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex Filter FourierTransform MeasureTheory Set Asymptotics
open scoped ENNReal InnerProductSpace Pointwise Topology

noncomputable section

def burnolUnitRechartedKernel (radius x y : ℝ) : ℂ :=
  (radius : ℂ) * Complex.exp
    (-2 * (Real.pi : ℂ) * Complex.I * (radius : ℂ) ^ 2 * (x : ℂ) * (y : ℂ))

def burnolUnitRechartedKernelDerivative (radius x y : ℝ) : ℂ :=
  Complex.exp
      (-2 * (Real.pi : ℂ) * Complex.I * (radius : ℂ) ^ 2 * (x : ℂ) * (y : ℂ)) *
    (1 - 4 * (Real.pi : ℂ) * Complex.I * (radius : ℂ) ^ 2 * (x : ℂ) * (y : ℂ))

private def burnolKernelDelta (radius h x y : ℝ) : ℂ :=
  -2 * (Real.pi : ℂ) * Complex.I *
    (((radius + h : ℝ) : ℂ) ^ 2 - (radius : ℂ) ^ 2) * (x : ℂ) * (y : ℂ)

private def burnolKernelLinearPhase (radius x y : ℝ) : ℂ :=
  -4 * (Real.pi : ℂ) * Complex.I * (radius : ℂ) * (x : ℂ) * (y : ℂ)

private def burnolKernelQuadraticPhase (x y : ℝ) : ℂ :=
  -2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) * (y : ℂ)

private theorem burnolKernelDelta_eq
    (radius h x y : ℝ) :
    burnolKernelDelta radius h x y =
      (h : ℂ) * burnolKernelLinearPhase radius x y +
        (h : ℂ) ^ 2 * burnolKernelQuadraticPhase x y := by
  unfold burnolKernelDelta burnolKernelLinearPhase burnolKernelQuadraticPhase
  push_cast
  ring

private theorem burnolKernel_exp_shift
    (radius h x y : ℝ) :
    Complex.exp
        (-2 * (Real.pi : ℂ) * Complex.I * ((radius + h : ℝ) : ℂ) ^ 2 *
          (x : ℂ) * (y : ℂ)) =
      Complex.exp
          (-2 * (Real.pi : ℂ) * Complex.I * (radius : ℂ) ^ 2 *
            (x : ℂ) * (y : ℂ)) *
        Complex.exp (burnolKernelDelta radius h x y) := by
  rw [← Complex.exp_add]
  congr 1
  unfold burnolKernelDelta
  push_cast
  ring

private theorem burnolKernel_remainder_eq
    (radius h x y : ℝ) :
    burnolUnitRechartedKernel (radius + h) x y -
        burnolUnitRechartedKernel radius x y -
        (h : ℂ) * burnolUnitRechartedKernelDerivative radius x y =
      Complex.exp
          (-2 * (Real.pi : ℂ) * Complex.I * (radius : ℂ) ^ 2 *
            (x : ℂ) * (y : ℂ)) *
        ((radius : ℂ) *
            (Complex.exp (burnolKernelDelta radius h x y) - 1 -
              burnolKernelDelta radius h x y) +
          (radius : ℂ) *
            (burnolKernelDelta radius h x y -
              (h : ℂ) * burnolKernelLinearPhase radius x y) +
          (h : ℂ) * (Complex.exp (burnolKernelDelta radius h x y) - 1)) := by
  unfold burnolUnitRechartedKernel burnolUnitRechartedKernelDerivative
  rw [burnolKernel_exp_shift]
  unfold burnolKernelLinearPhase
  push_cast
  ring

private theorem burnolKernelLinearPhase_norm_le
    {radius x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    ‖burnolKernelLinearPhase radius x y‖ ≤ 4 * Real.pi * |radius| := by
  unfold burnolKernelLinearPhase
  simp only [norm_mul, norm_neg, norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, norm_I, mul_one, abs_of_pos Real.pi_pos]
  calc
    4 * Real.pi * |radius| * |x| * |y| ≤
        4 * Real.pi * |radius| * 1 * 1 := by gcongr
    _ = 4 * Real.pi * |radius| := by ring

private theorem burnolKernelQuadraticPhase_norm_le
    {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    ‖burnolKernelQuadraticPhase x y‖ ≤ 2 * Real.pi := by
  unfold burnolKernelQuadraticPhase
  simp only [norm_mul, norm_neg, norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, norm_I, mul_one, abs_of_pos Real.pi_pos]
  calc
    2 * Real.pi * |x| * |y| ≤ 2 * Real.pi * 1 * 1 := by gcongr
    _ = 2 * Real.pi := by ring

private def burnolKernelDeltaBound (radius : ℝ) : ℝ :=
  4 * Real.pi * |radius| + 2 * Real.pi

private theorem burnolKernelDeltaBound_pos (radius : ℝ) :
    0 < burnolKernelDeltaBound radius := by
  unfold burnolKernelDeltaBound
  positivity

private theorem burnolKernelDelta_norm_le
    {radius h x y : ℝ} (hh : |h| ≤ 1) (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    ‖burnolKernelDelta radius h x y‖ ≤
      burnolKernelDeltaBound radius * |h| := by
  rw [burnolKernelDelta_eq]
  calc
    ‖(h : ℂ) * burnolKernelLinearPhase radius x y +
        (h : ℂ) ^ 2 * burnolKernelQuadraticPhase x y‖ ≤
        ‖(h : ℂ) * burnolKernelLinearPhase radius x y‖ +
          ‖(h : ℂ) ^ 2 * burnolKernelQuadraticPhase x y‖ := norm_add_le _ _
    _ = |h| * ‖burnolKernelLinearPhase radius x y‖ +
        |h| ^ 2 * ‖burnolKernelQuadraticPhase x y‖ := by
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ |h| * (4 * Real.pi * |radius|) + |h| ^ 2 * (2 * Real.pi) := by
      gcongr
      · exact burnolKernelLinearPhase_norm_le hx hy
      · exact burnolKernelQuadraticPhase_norm_le hx hy
    _ ≤ |h| * (4 * Real.pi * |radius|) + |h| * (2 * Real.pi) := by
      gcongr
      nlinarith [abs_nonneg h]
    _ = burnolKernelDeltaBound radius * |h| := by
      unfold burnolKernelDeltaBound
      ring

private theorem burnolKernelDelta_sub_linear
    (radius h x y : ℝ) :
    burnolKernelDelta radius h x y -
        (h : ℂ) * burnolKernelLinearPhase radius x y =
      (h : ℂ) ^ 2 * burnolKernelQuadraticPhase x y := by
  rw [burnolKernelDelta_eq]
  ring

theorem burnolKernel_base_exp_norm
    (radius x y : ℝ) :
    ‖Complex.exp
      (-2 * (Real.pi : ℂ) * Complex.I * (radius : ℂ) ^ 2 *
        (x : ℂ) * (y : ℂ))‖ = 1 := by
  rw [show -2 * (Real.pi : ℂ) * Complex.I * (radius : ℂ) ^ 2 *
      (x : ℂ) * (y : ℂ) =
      (((-2 * Real.pi * radius ^ 2 * x * y : ℝ) : ℂ) * Complex.I) by
    push_cast
    ring]
  rw [Complex.norm_exp]
  rw [show (((( -2 * Real.pi * radius ^ 2 * x * y : ℝ) : ℂ) *
      Complex.I).re) = 0 by
    change (-2 * Real.pi * radius ^ 2 * x * y) * 0 - 0 * 1 = 0
    ring]
  simp

def burnolKernelVariationRadius (radius : ℝ) : ℝ :=
  min 1 (burnolKernelDeltaBound radius)⁻¹

theorem burnolKernelVariationRadius_pos (radius : ℝ) :
    0 < burnolKernelVariationRadius radius := by
  unfold burnolKernelVariationRadius
  exact lt_min zero_lt_one (inv_pos.mpr (burnolKernelDeltaBound_pos radius))

private theorem burnolKernelDelta_norm_le_one
    {radius h x y : ℝ}
    (hh : |h| < burnolKernelVariationRadius radius)
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    ‖burnolKernelDelta radius h x y‖ ≤ 1 := by
  have hOne : |h| ≤ 1 :=
    (le_of_lt hh).trans (min_le_left _ _)
  have hInv : |h| < (burnolKernelDeltaBound radius)⁻¹ :=
    hh.trans_le (min_le_right _ _)
  have scaled : burnolKernelDeltaBound radius * |h| ≤ 1 := by
    apply le_of_lt
    calc
      burnolKernelDeltaBound radius * |h| <
          burnolKernelDeltaBound radius *
            (burnolKernelDeltaBound radius)⁻¹ := by
        gcongr
        exact burnolKernelDeltaBound_pos radius
      _ = 1 := mul_inv_cancel₀ (ne_of_gt (burnolKernelDeltaBound_pos radius))
  exact (burnolKernelDelta_norm_le hOne hx hy).trans scaled

def burnolKernelRemainderBound (radius : ℝ) : ℝ :=
  |radius| * (burnolKernelDeltaBound radius) ^ 2 +
    |radius| * (2 * Real.pi) + 2 * burnolKernelDeltaBound radius

theorem burnolKernelRemainderBound_nonnegative (radius : ℝ) :
    0 ≤ burnolKernelRemainderBound radius := by
  unfold burnolKernelRemainderBound
  have hC : 0 ≤ burnolKernelDeltaBound radius :=
    (burnolKernelDeltaBound_pos radius).le
  positivity

theorem burnolUnitRechartedKernel_remainder_norm_le
    {radius h x y : ℝ}
    (hh : |h| < burnolKernelVariationRadius radius)
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    ‖burnolUnitRechartedKernel (radius + h) x y -
        burnolUnitRechartedKernel radius x y -
        (h : ℂ) * burnolUnitRechartedKernelDerivative radius x y‖ ≤
      burnolKernelRemainderBound radius * |h| ^ 2 := by
  let d := burnolKernelDelta radius h x y
  let C0 := burnolKernelDeltaBound radius
  have hOne : |h| ≤ 1 := (le_of_lt hh).trans (min_le_left _ _)
  have dBound : ‖d‖ ≤ C0 * |h| :=
    burnolKernelDelta_norm_le hOne hx hy
  have dSmall : ‖d‖ ≤ 1 :=
    burnolKernelDelta_norm_le_one hh hx hy
  have firstOrder := Complex.norm_exp_sub_one_le dSmall
  have secondOrder := Complex.norm_exp_sub_one_sub_id_le dSmall
  have termOne :
      ‖(radius : ℂ) * (Complex.exp d - 1 - d)‖ ≤
        |radius| * (C0 ^ 2 * |h| ^ 2) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg radius)
    calc
      ‖Complex.exp d - 1 - d‖ ≤ ‖d‖ ^ 2 := secondOrder
      _ ≤ (C0 * |h|) ^ 2 := by
        nlinarith [norm_nonneg d, dBound,
          (burnolKernelDeltaBound_pos radius).le, abs_nonneg h]
      _ = C0 ^ 2 * |h| ^ 2 := by ring
  have termTwo :
      ‖(radius : ℂ) *
          (d - (h : ℂ) * burnolKernelLinearPhase radius x y)‖ ≤
        |radius| * ((2 * Real.pi) * |h| ^ 2) := by
    rw [show d - (h : ℂ) * burnolKernelLinearPhase radius x y =
        (h : ℂ) ^ 2 * burnolKernelQuadraticPhase x y by
      exact burnolKernelDelta_sub_linear radius h x y]
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg radius)
    calc
      |h| ^ 2 * ‖burnolKernelQuadraticPhase x y‖ ≤
          |h| ^ 2 * (2 * Real.pi) :=
        mul_le_mul_of_nonneg_left
          (burnolKernelQuadraticPhase_norm_le hx hy) (sq_nonneg |h|)
      _ = (2 * Real.pi) * |h| ^ 2 := by ring
  have termThree :
      ‖(h : ℂ) * (Complex.exp d - 1)‖ ≤
        2 * C0 * |h| ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      |h| * ‖Complex.exp d - 1‖ ≤ |h| * (2 * ‖d‖) :=
        mul_le_mul_of_nonneg_left firstOrder (abs_nonneg h)
      _ ≤ |h| * (2 * (C0 * |h|)) := by
        gcongr
      _ = 2 * C0 * |h| ^ 2 := by ring
  rw [burnolKernel_remainder_eq, norm_mul,
    burnolKernel_base_exp_norm, one_mul]
  calc
    ‖(radius : ℂ) * (Complex.exp d - 1 - d) +
        (radius : ℂ) *
          (d - (h : ℂ) * burnolKernelLinearPhase radius x y) +
        (h : ℂ) * (Complex.exp d - 1)‖ ≤
      ‖(radius : ℂ) * (Complex.exp d - 1 - d)‖ +
        ‖(radius : ℂ) *
          (d - (h : ℂ) * burnolKernelLinearPhase radius x y)‖ +
        ‖(h : ℂ) * (Complex.exp d - 1)‖ := by
      exact (norm_add_le _ _).trans
        (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ |radius| * (C0 ^ 2 * |h| ^ 2) +
        |radius| * ((2 * Real.pi) * |h| ^ 2) +
        2 * C0 * |h| ^ 2 := by gcongr
    _ = burnolKernelRemainderBound radius * |h| ^ 2 := by
      unfold burnolKernelRemainderBound C0
      ring

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
