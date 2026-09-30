import H0mework.Arithmetic.BurnolCarrier.ConstantGapFace

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex FourierTransform MeasureTheory Set
open scoped ENNReal InnerProductSpace

noncomputable section

abbrev BurnolRadiusIntervalL2 (radius : ℝ) :=
  Lp ℂ 2 ((volume : Measure ℝ).restrict (symmetricInterval radius))

def burnolRadiusRestriction (radius : ℝ) :
    BurnolL2 →L[ℂ] BurnolRadiusIntervalL2 radius :=
  restrictToInterval radius

def burnolRadiusZeroExtension (radius : ℝ) :
    BurnolRadiusIntervalL2 radius →L[ℂ] BurnolL2 :=
  ContinuousLinearMap.adjoint (burnolRadiusRestriction radius)

/-- The actual radius-indexed truncation `R_r ℱ₂ R_r*`. -/
def burnolRadiusTruncatedFourier (radius : ℝ) :
    BurnolRadiusIntervalL2 radius →L[ℂ] BurnolRadiusIntervalL2 radius :=
  (burnolRadiusRestriction radius).comp
    (fourierL2.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (burnolRadiusZeroExtension radius))

local instance burnolRadiusIntervalFiniteMeasure (radius : ℝ) :
    IsFiniteMeasure ((volume : Measure ℝ).restrict
      (symmetricInterval radius)) where
  measure_univ_lt_top := by
    exact lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top radius)

def burnolRadiusTruncatedFourierRaw (radius : ℝ)
    (state : BurnolRadiusIntervalL2 radius) (x : ℝ) : ℂ :=
  VectorFourier.fourierIntegral 𝐞
    ((volume : Measure ℝ).restrict (symmetricInterval radius))
    (innerₗ ℝ) (state : ℝ → ℂ) x

theorem burnolRadiusInterval_measureReal_univ
    {radius : ℝ} (positive : 0 < radius) :
    ((volume : Measure ℝ).restrict
      (symmetricInterval radius)).real Set.univ = 2 * radius := by
  rw [Measure.real, Measure.restrict_apply_univ, symmetricInterval,
    Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
  linarith

theorem burnolRadiusInterval_integral_norm_sq
    {radius : ℝ} (state : BurnolRadiusIntervalL2 radius) :
    (∫ x : ℝ, ‖state x‖ ^ 2
      ∂((volume : Measure ℝ).restrict (symmetricInterval radius))) =
      ‖state‖ ^ 2 := by
  have normSquare := InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) state
  rw [MeasureTheory.L2.inner_def] at normSquare
  have innerIntegrable := MeasureTheory.L2.integrable_inner
    (𝕜 := ℂ) state state
  have realIntegral := integral_re innerIntegrable
  rw [← realIntegral] at normSquare
  simp only [inner_self_eq_norm_sq_to_K] at normSquare
  norm_cast at normSquare
  exact normSquare.symm

theorem burnolRadiusInterval_integral_norm_le
    {radius : ℝ} (positive : 0 < radius)
    (state : BurnolRadiusIntervalL2 radius) :
    (∫ x : ℝ, ‖state x‖
      ∂((volume : Measure ℝ).restrict (symmetricInterval radius))) ≤
      Real.sqrt (2 * radius) * ‖state‖ := by
  have stateMem : MemLp (fun x : ℝ ↦ state x) (ENNReal.ofReal 2)
      ((volume : Measure ℝ).restrict (symmetricInterval radius)) := by
    simpa using Lp.memLp state
  have holder := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
    (μ := ((volume : Measure ℝ).restrict (symmetricInterval radius)))
    (f := fun x : ℝ ↦ state x) (g := fun _ : ℝ ↦ (1 : ℂ))
    Real.HolderConjugate.two_two stateMem (memLp_const 1)
  simp only [norm_one, mul_one] at holder
  rw [show (∫ x : ℝ, ‖state x‖ ^ (2 : ℝ)
      ∂((volume : Measure ℝ).restrict (symmetricInterval radius))) =
      ‖state‖ ^ 2 by
        simpa using burnolRadiusInterval_integral_norm_sq state] at holder
  have constantSquare :
      (∫ _ : ℝ, (1 : ℝ) ^ (2 : ℝ)
        ∂((volume : Measure ℝ).restrict (symmetricInterval radius))) =
        2 * radius := by
    simpa using burnolRadiusInterval_measureReal_univ positive
  rw [constantSquare] at holder
  have stateRoot : (‖state‖ ^ (2 : ℕ)) ^ (1 / (2 : ℝ)) = ‖state‖ := by
    convert Real.pow_rpow_inv_natCast (norm_nonneg state)
      (by norm_num : (2 : ℕ) ≠ 0) using 1
    norm_num
  have radiusRoot :
      ((2 * radius : ℝ) ^ (1 / (2 : ℝ))) =
        Real.sqrt (2 * radius) := by
    exact (Real.sqrt_eq_rpow (2 * radius)).symm
  calc
    _ ≤ (‖state‖ ^ (2 : ℕ)) ^ (1 / (2 : ℝ)) *
        ((2 * radius : ℝ) ^ (1 / (2 : ℝ))) := holder
    _ = Real.sqrt (2 * radius) * ‖state‖ := by
      rw [stateRoot, radiusRoot]
      ring

theorem burnolRadiusTruncatedFourierRaw_norm_le
    {radius : ℝ} (positive : 0 < radius)
    (state : BurnolRadiusIntervalL2 radius) (x : ℝ) :
    ‖burnolRadiusTruncatedFourierRaw radius state x‖ ≤
      Real.sqrt (2 * radius) * ‖state‖ := by
  exact (VectorFourier.norm_fourierIntegral_le_integral_norm
    𝐞 ((volume : Measure ℝ).restrict (symmetricInterval radius))
    (innerₗ ℝ) (state : ℝ → ℂ) x).trans
      (burnolRadiusInterval_integral_norm_le positive state)

theorem burnolRadiusTruncatedFourierRaw_continuous
    {radius : ℝ} (state : BurnolRadiusIntervalL2 radius) :
    Continuous (burnolRadiusTruncatedFourierRaw radius state) := by
  apply VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar continuous_inner
  exact (Lp.memLp state).integrable (by norm_num)

theorem burnolRadiusTruncatedFourierRaw_memLp
    {radius : ℝ} (positive : 0 < radius)
    (state : BurnolRadiusIntervalL2 radius) :
    MemLp (burnolRadiusTruncatedFourierRaw radius state) 2
      ((volume : Measure ℝ).restrict (symmetricInterval radius)) := by
  exact (memLp_top_of_bound
    (burnolRadiusTruncatedFourierRaw_continuous state).aestronglyMeasurable
    (Real.sqrt (2 * radius) * ‖state‖)
    (Filter.Eventually.of_forall
      (burnolRadiusTruncatedFourierRaw_norm_le positive state)))
      |>.mono_exponent (by norm_num)

def burnolRadiusTruncatedFourierIntegralValue
    {radius : ℝ} (positive : 0 < radius)
    (state : BurnolRadiusIntervalL2 radius) : BurnolRadiusIntervalL2 radius :=
  (burnolRadiusTruncatedFourierRaw_memLp positive state).toLp
    (burnolRadiusTruncatedFourierRaw radius state)

theorem burnolRadiusTruncatedFourierIntegralValue_norm_le
    {radius : ℝ} (positive : 0 < radius)
    (state : BurnolRadiusIntervalL2 radius) :
    ‖burnolRadiusTruncatedFourierIntegralValue positive state‖ ≤
      (2 * radius : ℝ) * ‖state‖ := by
  rw [burnolRadiusTruncatedFourierIntegralValue, Lp.norm_toLp]
  have rawBound := eLpNorm_le_of_ae_bound (p := (2 : ℝ≥0∞))
    (μ := ((volume : Measure ℝ).restrict (symmetricInterval radius)))
    (Filter.Eventually.of_forall
      (burnolRadiusTruncatedFourierRaw_norm_le positive state))
  have rhsFinite :
      ((volume : Measure ℝ).restrict (symmetricInterval radius)) Set.univ ^
          (2 : ℝ≥0∞).toReal⁻¹ *
        ENNReal.ofReal (Real.sqrt (2 * radius) * ‖state‖) ≠ ∞ := by
    finiteness
  apply (ENNReal.toReal_mono rhsFinite rawBound).trans_eq
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (by positivity :
      0 ≤ Real.sqrt (2 * radius) * ‖state‖)]
  simp only [ENNReal.toReal_ofNat]
  have measureRead :
      (((volume : Measure ℝ).restrict
        (symmetricInterval radius)) Set.univ).toReal = 2 * radius :=
    burnolRadiusInterval_measureReal_univ positive
  rw [measureRead]
  have radiusRpow :
      (2 * radius : ℝ) ^ (2⁻¹ : ℝ) = Real.sqrt (2 * radius) := by
    simpa only [one_div] using (Real.sqrt_eq_rpow (2 * radius)).symm
  rw [radiusRpow]
  have squareRootSquare :
      Real.sqrt (2 * radius) * Real.sqrt (2 * radius) = 2 * radius := by
    rw [Real.mul_self_sqrt]
    linarith
  rw [← mul_assoc, squareRootSquare]

theorem burnolRadiusTruncatedFourierRaw_add
    {radius : ℝ} (left right : BurnolRadiusIntervalL2 radius) :
    burnolRadiusTruncatedFourierRaw radius (left + right) =
      burnolRadiusTruncatedFourierRaw radius left +
        burnolRadiusTruncatedFourierRaw radius right := by
  have coeAdd : ((left + right : BurnolRadiusIntervalL2 radius) : ℝ → ℂ) =ᵐ[
      ((volume : Measure ℝ).restrict (symmetricInterval radius))]
      (fun x ↦ left x + right x) := Lp.coeFn_add left right
  have congruent := VectorFourier.fourierIntegral_congr_ae
    𝐞 ((volume : Measure ℝ).restrict (symmetricInterval radius))
    (innerₗ ℝ) coeAdd
  have additive := VectorFourier.fourierIntegral_add
    (e := 𝐞) (μ := ((volume : Measure ℝ).restrict
      (symmetricInterval radius))) (L := innerₗ ℝ)
    Real.continuous_fourierChar (by fun_prop)
    ((Lp.memLp left).integrable (by norm_num))
    ((Lp.memLp right).integrable (by norm_num))
  unfold burnolRadiusTruncatedFourierRaw
  exact congruent.trans additive

theorem burnolRadiusTruncatedFourierRaw_smul
    {radius : ℝ} (coefficient : ℂ)
    (state : BurnolRadiusIntervalL2 radius) :
    burnolRadiusTruncatedFourierRaw radius (coefficient • state) =
      coefficient • burnolRadiusTruncatedFourierRaw radius state := by
  have coeSmul : ((coefficient • state : BurnolRadiusIntervalL2 radius) :
      ℝ → ℂ) =ᵐ[((volume : Measure ℝ).restrict
      (symmetricInterval radius))]
      (fun x ↦ coefficient • state x) := Lp.coeFn_smul coefficient state
  have congruent := VectorFourier.fourierIntegral_congr_ae
    𝐞 ((volume : Measure ℝ).restrict (symmetricInterval radius))
    (innerₗ ℝ) coeSmul
  unfold burnolRadiusTruncatedFourierRaw
  exact congruent.trans (VectorFourier.fourierIntegral_const_smul
    𝐞 ((volume : Measure ℝ).restrict (symmetricInterval radius))
    (innerₗ ℝ) (state : ℝ → ℂ) coefficient)

theorem burnolRadiusTruncatedFourierIntegralValue_add
    {radius : ℝ} (positive : 0 < radius)
    (left right : BurnolRadiusIntervalL2 radius) :
    burnolRadiusTruncatedFourierIntegralValue positive (left + right) =
      burnolRadiusTruncatedFourierIntegralValue positive left +
        burnolRadiusTruncatedFourierIntegralValue positive right := by
  apply Lp.ext
  filter_upwards [
    MemLp.coeFn_toLp
      (burnolRadiusTruncatedFourierRaw_memLp positive (left + right)),
    MemLp.coeFn_toLp
      (burnolRadiusTruncatedFourierRaw_memLp positive left),
    MemLp.coeFn_toLp
      (burnolRadiusTruncatedFourierRaw_memLp positive right),
    Lp.coeFn_add
      (burnolRadiusTruncatedFourierIntegralValue positive left)
      (burnolRadiusTruncatedFourierIntegralValue positive right)]
      with x sumRead leftRead rightRead addRead
  have sumRead' :
      burnolRadiusTruncatedFourierIntegralValue positive (left + right) x =
        burnolRadiusTruncatedFourierRaw radius (left + right) x := sumRead
  have leftRead' :
      burnolRadiusTruncatedFourierIntegralValue positive left x =
        burnolRadiusTruncatedFourierRaw radius left x := leftRead
  have rightRead' :
      burnolRadiusTruncatedFourierIntegralValue positive right x =
        burnolRadiusTruncatedFourierRaw radius right x := rightRead
  rw [sumRead']
  calc
    _ = burnolRadiusTruncatedFourierRaw radius left x +
        burnolRadiusTruncatedFourierRaw radius right x :=
      congrFun (burnolRadiusTruncatedFourierRaw_add left right) x
    _ = burnolRadiusTruncatedFourierIntegralValue positive left x +
        burnolRadiusTruncatedFourierIntegralValue positive right x := by
      rw [leftRead', rightRead']
    _ = _ := addRead.symm

theorem burnolRadiusTruncatedFourierIntegralValue_smul
    {radius : ℝ} (positive : 0 < radius) (coefficient : ℂ)
    (state : BurnolRadiusIntervalL2 radius) :
    burnolRadiusTruncatedFourierIntegralValue positive
        (coefficient • state) =
      coefficient • burnolRadiusTruncatedFourierIntegralValue positive state := by
  apply Lp.ext
  filter_upwards [
    MemLp.coeFn_toLp
      (burnolRadiusTruncatedFourierRaw_memLp positive (coefficient • state)),
    MemLp.coeFn_toLp
      (burnolRadiusTruncatedFourierRaw_memLp positive state),
    Lp.coeFn_smul coefficient
      (burnolRadiusTruncatedFourierIntegralValue positive state)]
      with x scaledRead stateRead smulRead
  have scaledRead' :
      burnolRadiusTruncatedFourierIntegralValue positive
          (coefficient • state) x =
        burnolRadiusTruncatedFourierRaw radius (coefficient • state) x :=
    scaledRead
  have stateRead' :
      burnolRadiusTruncatedFourierIntegralValue positive state x =
        burnolRadiusTruncatedFourierRaw radius state x := stateRead
  rw [scaledRead']
  calc
    _ = coefficient • burnolRadiusTruncatedFourierRaw radius state x :=
      congrFun (burnolRadiusTruncatedFourierRaw_smul coefficient state) x
    _ = coefficient •
        burnolRadiusTruncatedFourierIntegralValue positive state x := by
      rw [stateRead']
    _ = _ := smulRead.symm

def burnolRadiusTruncatedFourierIntegral
    (radius : ℝ) (positive : 0 < radius) :
    BurnolRadiusIntervalL2 radius →L[ℂ] BurnolRadiusIntervalL2 radius :=
  @LinearMap.mkContinuous ℂ ℂ (BurnolRadiusIntervalL2 radius)
    (BurnolRadiusIntervalL2 radius) _ _ _ _ _ _ (RingHom.id ℂ)
    { toFun := burnolRadiusTruncatedFourierIntegralValue positive
      map_add' := burnolRadiusTruncatedFourierIntegralValue_add positive
      map_smul' := burnolRadiusTruncatedFourierIntegralValue_smul positive }
    (2 * radius) (burnolRadiusTruncatedFourierIntegralValue_norm_le positive)

theorem burnolRadiusTruncatedFourierIntegral_opNorm_le
    {radius : ℝ} (positive : 0 < radius) :
    ‖burnolRadiusTruncatedFourierIntegral radius positive‖ ≤ 2 * radius := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by linarith)
  exact burnolRadiusTruncatedFourierIntegralValue_norm_le positive

theorem burnolRadiusTruncatedFourierIntegral_opNorm_lt_one
    {radius : ℝ} (positive : 0 < radius) (short : 2 * radius < 1) :
    ‖burnolRadiusTruncatedFourierIntegral radius positive‖ < 1 :=
  lt_of_le_of_lt (burnolRadiusTruncatedFourierIntegral_opNorm_le positive) short

end

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
