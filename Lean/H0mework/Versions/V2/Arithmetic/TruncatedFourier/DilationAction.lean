import H0mework.Arithmetic.TruncatedFourier.RectangularKernel
import H0mework.Versions.V2.Arithmetic.BurnolPhysical.L2DirectDilation

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex FourierTransform MeasureTheory Set
open scoped ENNReal InnerProductSpace Pointwise
noncomputable section

def burnolUnitWindowEmbedding {radius : ℝ} (hr : 0 < radius) :
    BurnolUnitIntervalL2 →L[ℂ] BurnolL2 :=
  (burnolRadiusZeroExtension radius).comp
    (burnolRadiusRechartEquiv hr).symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem burnolUnitWindowEmbedding_coe {radius : ℝ} (hr : 0 < radius)
    (state : BurnolUnitIntervalL2) :
    (burnolUnitWindowEmbedding hr state : ℝ → ℂ) =ᵐ[volume]
      (symmetricInterval radius).indicator
        (fun x : ℝ => (Real.sqrt radius : ℂ)⁻¹ * state (radius⁻¹ * x)) := by
  have inverse := (ae_restrict_iff' (measurableSet_symmetricInterval radius)).mp
    (burnolRadiusRechartEquiv_symm_coe hr state)
  filter_upwards [burnolRadiusZeroExtension_coe
    ((burnolRadiusRechartEquiv hr).symm state), inverse] with x he hi
  change burnolRadiusZeroExtension radius ((burnolRadiusRechartEquiv hr).symm state) x = _
  rw [he]
  by_cases hx : x ∈ symmetricInterval radius
  · simp only [Set.indicator_of_mem hx]
    exact hi hx
  · simp only [Set.indicator_of_notMem hx]

private theorem dilation_window_membership (radius h x : ℝ) :
    Real.exp h * x ∈ symmetricInterval radius ↔
      x ∈ symmetricInterval (radius * Real.exp (-h)) := by
  simp only [symmetricInterval, Set.mem_Icc, ← abs_le, abs_mul,
    abs_of_pos (Real.exp_pos h)]
  simpa only [Real.exp_neg, div_eq_mul_inv, mul_comm] using
    (le_div_iff₀ (Real.exp_pos h) :
      |x| ≤ radius / Real.exp h ↔ |x| * Real.exp h ≤ radius).symm

private theorem dilation_window_halfDensity {radius : ℝ}
    (hr : 0 < radius) (h : ℝ) :
    (Real.exp (h / 2) : ℂ) * (Real.sqrt radius : ℂ)⁻¹ =
      (Real.sqrt (radius * Real.exp (-h)) : ℂ)⁻¹ := by
  rw [Real.sqrt_mul hr.le, ← Real.exp_half,
    show (-h) / 2 = -(h / 2) by ring, Real.exp_neg]
  simp only [ofReal_mul, ofReal_inv, mul_inv_rev, inv_inv]

theorem burnolUnitWindowEmbedding_dilation
    {radius : ℝ} (hr : 0 < radius) (h : ℝ)
    (state : BurnolUnitIntervalL2) :
    burnolMultiplicativeDilation h (burnolUnitWindowEmbedding hr state) =
      burnolUnitWindowEmbedding (mul_pos hr (Real.exp_pos (-h))) state := by
  have scale : Measure.QuasiMeasurePreserving (fun x : ℝ => Real.exp h * x)
      volume volume := by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
        (r := Real.exp h) (Real.exp_ne_zero h))
  apply Lp.ext
  filter_upwards [burnolMultiplicativeDilation_coeFn h (burnolUnitWindowEmbedding hr state),
    scale.ae (burnolUnitWindowEmbedding_coe hr state),
    burnolUnitWindowEmbedding_coe (mul_pos hr (Real.exp_pos (-h))) state]
    with x hd hs ht
  rw [hd]
  change (Real.exp (h / 2) : ℂ) * burnolUnitWindowEmbedding hr state (Real.exp h * x) = _
  rw [hs, ht]
  by_cases hx : x ∈ symmetricInterval (radius * Real.exp (-h))
  · have old := (dilation_window_membership radius h x).mpr hx
    simp only [Set.indicator_of_mem hx, Set.indicator_of_mem old]
    rw [← mul_assoc, dilation_window_halfDensity hr h]
    congr 1
    congr 1
    simp only [Real.exp_neg, mul_inv_rev, inv_inv]
    ring
  · have old : Real.exp h * x ∉ symmetricInterval radius :=
      fun inside => hx ((dilation_window_membership radius h x).mp inside)
    simp only [Set.indicator_of_notMem hx, Set.indicator_of_notMem old, mul_zero]

theorem burnolUnitWindowEmbedding_fourier_dilation
    {radius : ℝ} (hr : 0 < radius) (h : ℝ)
    (state : BurnolUnitIntervalL2) :
    fourierL2 (burnolUnitWindowEmbedding (mul_pos hr (Real.exp_pos (-h))) state) =
      burnolMultiplicativeDilation (-h)
        (fourierL2 (burnolUnitWindowEmbedding hr state)) := by
  rw [← burnolUnitWindowEmbedding_dilation hr h]
  exact fourierL2_burnolMultiplicativeDilation h (burnolUnitWindowEmbedding hr state)

theorem burnolRectangularRechartedFourier_balanced_action
    {position frequency : ℝ} (hp : 0 < position) (hf : 0 < frequency)
    (h : ℝ) :
    burnolRectangularRechartedFourier
        (mul_pos hp (Real.exp_pos (-h))) (mul_pos hf (Real.exp_pos h)) =
      burnolRectangularRechartedFourier hp hf := by
  have product : (position * Real.exp (-h)) * (frequency * Real.exp h) =
      position * frequency := by
    rw [Real.exp_neg]
    field_simp
  rw [burnolRectangularRechartedFourier_eq_geometric_mean,
    burnolRectangularRechartedFourier_eq_geometric_mean]
  simp only [product]

theorem burnolRectangularRechartedFourier_inner
    {position frequency : ℝ} (hp : 0 < position) (hf : 0 < frequency)
    (left right : BurnolUnitIntervalL2) :
    ⟪left, burnolRectangularRechartedFourier hp hf right⟫_ℂ =
      ⟪burnolUnitWindowEmbedding hf left,
        fourierL2 (burnolUnitWindowEmbedding hp right)⟫_ℂ := by
  calc
    _ = ⟪(burnolRadiusRechartEquiv hf).symm left,
        burnolRadiusRestriction frequency
          (fourierL2 (burnolUnitWindowEmbedding hp right))⟫_ℂ := by
      simpa only [burnolRectangularRechartedFourier, burnolRectangularFourier,
        burnolUnitWindowEmbedding, ContinuousLinearMap.comp_apply,
        LinearIsometryEquiv.coe_toContinuousLinearEquiv,
        ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.apply_symm_apply] using
        (burnolRadiusRechartEquiv hf).inner_map_map
          ((burnolRadiusRechartEquiv hf).symm left)
          (burnolRadiusRestriction frequency
            (fourierL2 (burnolUnitWindowEmbedding hp right)))
    _ = _ := (ContinuousLinearMap.adjoint_inner_left
      (burnolRadiusRestriction frequency)
      (fourierL2 (burnolUnitWindowEmbedding hp right))
      ((burnolRadiusRechartEquiv hf).symm left)).symm

def burnolFixedWindowFourierDilation
    {position frequency : ℝ} (hp : 0 < position) (hf : 0 < frequency)
    (shift : ℝ) : BurnolUnitIntervalL2 →L[ℂ] BurnolUnitIntervalL2 :=
  (burnolRadiusRechartEquiv hf).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((burnolRadiusRestriction frequency).comp
      (fourierL2.toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((burnolMultiplicativeDilation shift).toContinuousLinearEquiv.toContinuousLinearMap.comp
          (burnolUnitWindowEmbedding hp))))

theorem burnolFixedWindowFourierDilation_eq_rectangular
    {position frequency : ℝ} (hp : 0 < position) (hf : 0 < frequency)
    (shift : ℝ) :
    burnolFixedWindowFourierDilation hp hf shift =
      burnolRectangularRechartedFourier
        (mul_pos hp (Real.exp_pos (-shift))) hf := by
  apply ContinuousLinearMap.ext
  intro state
  change (burnolRadiusRechartEquiv hf)
      (burnolRadiusRestriction frequency
        (fourierL2 (burnolMultiplicativeDilation shift
          (burnolUnitWindowEmbedding hp state)))) =
    (burnolRadiusRechartEquiv hf)
      (burnolRadiusRestriction frequency
        (fourierL2 (burnolUnitWindowEmbedding
          (mul_pos hp (Real.exp_pos (-shift))) state)))
  rw [burnolUnitWindowEmbedding_dilation]

theorem burnolFixedWindowFourierDilation_eq_radius
    {position frequency : ℝ} (hp : 0 < position) (hf : 0 < frequency)
    (shift : ℝ) :
    burnolFixedWindowFourierDilation hp hf shift =
      burnolRadiusRechartedTruncatedFourier
        (mul_pos (Real.sqrt_pos.mpr (mul_pos hp hf))
          (Real.exp_pos (-shift / 2))) := by
  rw [burnolFixedWindowFourierDilation_eq_rectangular,
    burnolRectangularRechartedFourier_eq_geometric_mean]
  have radiusEq : Real.sqrt (position * Real.exp (-shift) * frequency) =
      Real.sqrt (position * frequency) * Real.exp (-shift / 2) := by
    rw [show position * Real.exp (-shift) * frequency =
      (position * frequency) * Real.exp (-shift) by ring,
      Real.sqrt_mul (mul_pos hp hf).le, ← Real.exp_half]
  simp only [radiusEq]

def burnolFixedWindowDilationFourier
    {position frequency : ℝ} (hp : 0 < position) (hf : 0 < frequency)
    (shift : ℝ) : BurnolUnitIntervalL2 →L[ℂ] BurnolUnitIntervalL2 :=
  (burnolRadiusRechartEquiv hf).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((burnolRadiusRestriction frequency).comp
      ((burnolMultiplicativeDilation shift).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (fourierL2.toContinuousLinearEquiv.toContinuousLinearMap.comp
          (burnolUnitWindowEmbedding hp))))

theorem burnolFixedWindowDilationFourier_eq_inverse
    {position frequency : ℝ} (hp : 0 < position) (hf : 0 < frequency)
    (shift : ℝ) :
    burnolFixedWindowDilationFourier hp hf shift =
      burnolFixedWindowFourierDilation hp hf (-shift) := by
  apply ContinuousLinearMap.ext
  intro state
  change (burnolRadiusRechartEquiv hf)
      (burnolRadiusRestriction frequency
        (burnolMultiplicativeDilation shift
          (fourierL2 (burnolUnitWindowEmbedding hp state)))) =
    (burnolRadiusRechartEquiv hf)
      (burnolRadiusRestriction frequency
        (fourierL2 (burnolMultiplicativeDilation (-shift)
          (burnolUnitWindowEmbedding hp state))))
  rw [fourierL2_burnolMultiplicativeDilation, neg_neg]

theorem burnolFixedWindowDilationFourier_eq_radius
    {position frequency : ℝ} (hp : 0 < position) (hf : 0 < frequency)
    (shift : ℝ) :
    burnolFixedWindowDilationFourier hp hf shift =
      burnolRadiusRechartedTruncatedFourier
        (mul_pos (Real.sqrt_pos.mpr (mul_pos hp hf))
          (Real.exp_pos (shift / 2))) := by
  rw [burnolFixedWindowDilationFourier_eq_inverse,
    burnolFixedWindowFourierDilation_eq_radius]
  simp only [neg_neg]

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
