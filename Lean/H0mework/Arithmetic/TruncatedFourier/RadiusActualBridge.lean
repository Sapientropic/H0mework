import H0mework.Arithmetic.TruncatedFourier.RadiusIntegralKernel
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex FourierTransform MeasureTheory Set
open scoped ENNReal InnerProductSpace ComplexConjugate

noncomputable section

local instance burnolRadiusBridgeFiniteMeasure (radius : ℝ) :
    IsFiniteMeasure ((volume : Measure ℝ).restrict
      (symmetricInterval radius)) where
  measure_univ_lt_top := by
    exact lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top radius)

theorem burnolRadiusZeroExtensionRaw_memLp
    {radius : ℝ} (state : BurnolRadiusIntervalL2 radius) :
    MemLp ((symmetricInterval radius).indicator fun x : ℝ ↦ state x) 2
      (volume : Measure ℝ) := by
  rw [memLp_indicator_iff_restrict (measurableSet_symmetricInterval radius)]
  exact Lp.memLp state

def burnolRadiusZeroExtensionValue
    {radius : ℝ} (state : BurnolRadiusIntervalL2 radius) : BurnolL2 :=
  (burnolRadiusZeroExtensionRaw_memLp state).toLp
    ((symmetricInterval radius).indicator fun x : ℝ ↦ state x)

theorem burnolRadiusZeroExtensionValue_norm
    {radius : ℝ} (state : BurnolRadiusIntervalL2 radius) :
    ‖burnolRadiusZeroExtensionValue state‖ = ‖state‖ := by
  rw [burnolRadiusZeroExtensionValue, Lp.norm_toLp,
    eLpNorm_indicator_eq_eLpNorm_restrict
      (measurableSet_symmetricInterval radius), Lp.norm_def]

theorem burnolRadiusZeroExtensionValue_add
    {radius : ℝ} (left right : BurnolRadiusIntervalL2 radius) :
    burnolRadiusZeroExtensionValue (left + right) =
      burnolRadiusZeroExtensionValue left + burnolRadiusZeroExtensionValue right := by
  have localAdd : ∀ᵐ x ∂(volume : Measure ℝ),
      x ∈ symmetricInterval radius →
        (left + right : BurnolRadiusIntervalL2 radius) x = left x + right x :=
    (ae_restrict_iff' (measurableSet_symmetricInterval radius)).mp
      (Lp.coeFn_add left right)
  apply Lp.ext
  filter_upwards [
    MemLp.coeFn_toLp (burnolRadiusZeroExtensionRaw_memLp (left + right)),
    MemLp.coeFn_toLp (burnolRadiusZeroExtensionRaw_memLp left),
    MemLp.coeFn_toLp (burnolRadiusZeroExtensionRaw_memLp right), localAdd,
    Lp.coeFn_add (burnolRadiusZeroExtensionValue left)
      (burnolRadiusZeroExtensionValue right)]
      with x sumRead leftRead rightRead localAddAt globalAdd
  rw [globalAdd]
  change
    ((burnolRadiusZeroExtensionRaw_memLp (left + right)).toLp
      ((symmetricInterval radius).indicator fun x : ℝ ↦ (left + right) x)) x =
    ((burnolRadiusZeroExtensionRaw_memLp left).toLp
      ((symmetricInterval radius).indicator fun x : ℝ ↦ left x)) x +
    ((burnolRadiusZeroExtensionRaw_memLp right).toLp
      ((symmetricInterval radius).indicator fun x : ℝ ↦ right x)) x
  rw [sumRead, leftRead, rightRead]
  by_cases hx : x ∈ symmetricInterval radius
  · simp only [Set.indicator_of_mem hx]
    exact localAddAt hx
  · simp [hx]

theorem burnolRadiusZeroExtensionValue_smul
    {radius : ℝ} (coefficient : ℂ)
    (state : BurnolRadiusIntervalL2 radius) :
    burnolRadiusZeroExtensionValue (coefficient • state) =
      coefficient • burnolRadiusZeroExtensionValue state := by
  have localSmul : ∀ᵐ x ∂(volume : Measure ℝ),
      x ∈ symmetricInterval radius →
        (coefficient • state : BurnolRadiusIntervalL2 radius) x =
          coefficient • state x :=
    (ae_restrict_iff' (measurableSet_symmetricInterval radius)).mp
      (Lp.coeFn_smul coefficient state)
  apply Lp.ext
  filter_upwards [
    MemLp.coeFn_toLp
      (burnolRadiusZeroExtensionRaw_memLp (coefficient • state)),
    MemLp.coeFn_toLp (burnolRadiusZeroExtensionRaw_memLp state), localSmul,
    Lp.coeFn_smul coefficient (burnolRadiusZeroExtensionValue state)]
      with x scaledRead stateRead localSmulAt globalSmul
  rw [globalSmul]
  change
    ((burnolRadiusZeroExtensionRaw_memLp (coefficient • state)).toLp
      ((symmetricInterval radius).indicator fun x : ℝ ↦
        (coefficient • state) x)) x =
    coefficient •
      ((burnolRadiusZeroExtensionRaw_memLp state).toLp
        ((symmetricInterval radius).indicator fun x : ℝ ↦ state x)) x
  rw [scaledRead, stateRead]
  by_cases hx : x ∈ symmetricInterval radius
  · simp only [Set.indicator_of_mem hx]
    exact localSmulAt hx
  · simp [hx]

def burnolRadiusZeroExtensionExplicit (radius : ℝ) :
    BurnolRadiusIntervalL2 radius →L[ℂ] BurnolL2 :=
  @LinearMap.mkContinuous ℂ ℂ (BurnolRadiusIntervalL2 radius) BurnolL2
    _ _ _ _ _ _ (RingHom.id ℂ)
    { toFun := burnolRadiusZeroExtensionValue
      map_add' := burnolRadiusZeroExtensionValue_add
      map_smul' := burnolRadiusZeroExtensionValue_smul }
    1 (fun state ↦ by
      change ‖burnolRadiusZeroExtensionValue state‖ ≤ 1 * ‖state‖
      rw [one_mul, burnolRadiusZeroExtensionValue_norm])

theorem burnolRadiusZeroExtensionExplicit_coe
    {radius : ℝ} (state : BurnolRadiusIntervalL2 radius) :
    burnolRadiusZeroExtensionExplicit radius state =ᵐ[(volume : Measure ℝ)]
      (symmetricInterval radius).indicator fun x : ℝ ↦ state x :=
  MemLp.coeFn_toLp (burnolRadiusZeroExtensionRaw_memLp state)

theorem burnolRadiusZeroExtensionExplicit_is_adjoint (radius : ℝ) :
    burnolRadiusZeroExtensionExplicit radius = burnolRadiusZeroExtension radius := by
  unfold burnolRadiusZeroExtension
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro state ambient
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  have extensionRead := burnolRadiusZeroExtensionExplicit_coe state
  have restrictionRead : ∀ᵐ x ∂(volume : Measure ℝ),
      x ∈ symmetricInterval radius →
        (burnolRadiusRestriction radius ambient) x = ambient x := by
    apply (ae_restrict_iff' (measurableSet_symmetricInterval radius)).mp
    exact LpToLpRestrictCLM_coeFn ℂ (symmetricInterval radius) ambient
  rw [← integral_indicator (measurableSet_symmetricInterval radius)]
  apply integral_congr_ae
  filter_upwards [extensionRead, restrictionRead] with x hxExt hxRestrict
  by_cases hx : x ∈ symmetricInterval radius
  · simp only [Set.indicator_of_mem hx, hxExt, hxRestrict hx]
  · simp only [Set.indicator_of_notMem hx, hxExt]
    simp

theorem burnolRadiusZeroExtension_coe
    {radius : ℝ} (state : BurnolRadiusIntervalL2 radius) :
    burnolRadiusZeroExtension radius state =ᵐ[(volume : Measure ℝ)]
      (symmetricInterval radius).indicator fun x : ℝ ↦ state x := by
  rw [← burnolRadiusZeroExtensionExplicit_is_adjoint radius]
  exact burnolRadiusZeroExtensionExplicit_coe state

theorem burnolRadiusZeroExtensionRaw_integrable
    {radius : ℝ} (state : BurnolRadiusIntervalL2 radius) :
    Integrable ((symmetricInterval radius).indicator fun x : ℝ ↦ state x)
      (volume : Measure ℝ) := by
  rw [← memLp_one_iff_integrable,
    memLp_indicator_iff_restrict (measurableSet_symmetricInterval radius)]
  exact (Lp.memLp state).mono_exponent (by norm_num)

theorem burnolRadiusTruncatedFourierRaw_eq_fourier_zeroExtension
    {radius : ℝ} (state : BurnolRadiusIntervalL2 radius)
    (frequency : ℝ) :
    burnolRadiusTruncatedFourierRaw radius state frequency =
      FourierTransform.fourier
        ((symmetricInterval radius).indicator fun x : ℝ ↦ state x)
        frequency := by
  rw [Real.fourier_eq]
  unfold burnolRadiusTruncatedFourierRaw VectorFourier.fourierIntegral
  rw [← integral_indicator (measurableSet_symmetricInterval radius)]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ symmetricInterval radius <;> simp [hx]

theorem burnolRadiusRealInner_flip_fourier
    (test : SchwartzMap ℝ ℂ) (frequency : ℝ) :
    VectorFourier.fourierIntegral 𝐞 (volume : Measure ℝ)
        (innerₗ ℝ).flip (test : ℝ → ℂ) frequency =
      FourierTransform.fourier test frequency := by
  rw [SchwartzMap.fourier_coe, Real.fourier_eq]
  unfold VectorFourier.fourierIntegral
  apply integral_congr_ae
  filter_upwards with x
  simp

theorem burnolRadiusFourier_pairing
    {radius : ℝ} (state : BurnolRadiusIntervalL2 radius)
    (test : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ, FourierTransform.fourier test x •
        (symmetricInterval radius).indicator (fun y : ℝ ↦ state y) x) =
      ∫ x : ℝ, test x • burnolRadiusTruncatedFourierRaw radius state x := by
  have swap := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (e := 𝐞) (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (L := innerₗ ℝ) Real.continuous_fourierChar (by fun_prop)
    (burnolRadiusZeroExtensionRaw_integrable state) test.integrable
  calc
    _ = ∫ x : ℝ,
        (symmetricInterval radius).indicator (fun y : ℝ ↦ state y) x •
          FourierTransform.fourier test x := by
      apply integral_congr_ae
      filter_upwards with x
      simp [smul_eq_mul, mul_comm]
    _ = ∫ x : ℝ,
        (symmetricInterval radius).indicator (fun y : ℝ ↦ state y) x •
          VectorFourier.fourierIntegral 𝐞 (volume : Measure ℝ)
            (innerₗ ℝ).flip (test : ℝ → ℂ) x := by
      apply integral_congr_ae
      filter_upwards with x
      rw [burnolRadiusRealInner_flip_fourier]
    _ = ∫ x : ℝ,
        VectorFourier.fourierIntegral 𝐞 (volume : Measure ℝ)
          (innerₗ ℝ)
          ((symmetricInterval radius).indicator fun y : ℝ ↦ state y) x •
            test x := swap.symm
    _ = ∫ x : ℝ,
        burnolRadiusTruncatedFourierRaw radius state x • test x := by
      apply integral_congr_ae
      filter_upwards with x
      change FourierTransform.fourier
          ((symmetricInterval radius).indicator fun y : ℝ ↦ state y) x •
            test x = _
      rw [burnolRadiusTruncatedFourierRaw_eq_fourier_zeroExtension]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with x
      simp [smul_eq_mul, mul_comm]

theorem burnolRadiusFourierL2_zeroExtension_ae_eq_raw
    {radius : ℝ} (state : BurnolRadiusIntervalL2 radius) :
    (fourierL2 (burnolRadiusZeroExtension radius state) : ℝ → ℂ) =ᵐ[
        (volume : Measure ℝ)] burnolRadiusTruncatedFourierRaw radius state := by
  apply ae_eq_of_integral_contDiff_smul_eq
  · exact (Lp.memLp (fourierL2
      (burnolRadiusZeroExtension radius state))).locallyIntegrable (by norm_num)
  · exact (burnolRadiusTruncatedFourierRaw_continuous state).locallyIntegrable
  · intro testReal testSmooth testCompact
    have testCompactComplex :
        HasCompactSupport (Complex.ofRealCLM ∘ testReal) :=
      testCompact.comp_left rfl
    let test : SchwartzMap ℝ ℂ :=
      testCompactComplex.toSchwartzMap
        (Complex.ofRealCLM.contDiff.comp testSmooth)
    have distributionalFourier :=
      Lp.fourier_toTemperedDistribution_eq
        (burnolRadiusZeroExtension radius state)
    calc
      (∫ x : ℝ, testReal x •
          (fourierL2 (burnolRadiusZeroExtension radius state) : ℝ → ℂ) x) =
          ((fourierL2 (burnolRadiusZeroExtension radius state) : BurnolL2) :
            TemperedDistribution ℝ ℂ) test := by
        simp [test, Function.comp_apply, real_smul]
      _ = FourierTransform.fourier
          ((burnolRadiusZeroExtension radius state : BurnolL2) :
            TemperedDistribution ℝ ℂ) test := by
        change
          ((FourierTransform.fourier
              (burnolRadiusZeroExtension radius state) : BurnolL2) :
                TemperedDistribution ℝ ℂ) test = _
        exact congrArg
          (fun value : TemperedDistribution ℝ ℂ ↦ value test)
          distributionalFourier.symm
      _ = ((burnolRadiusZeroExtension radius state : BurnolL2) :
            TemperedDistribution ℝ ℂ)
          (FourierTransform.fourier test) := rfl
      _ = ∫ x : ℝ, FourierTransform.fourier test x •
          (burnolRadiusZeroExtension radius state : ℝ → ℂ) x := by simp
      _ = ∫ x : ℝ, FourierTransform.fourier test x •
          (symmetricInterval radius).indicator (fun y : ℝ ↦ state y) x := by
        apply integral_congr_ae
        filter_upwards [burnolRadiusZeroExtension_coe state] with x hx
        rw [hx]
      _ = ∫ x : ℝ, test x •
          burnolRadiusTruncatedFourierRaw radius state x :=
        burnolRadiusFourier_pairing state test
      _ = ∫ x : ℝ, testReal x •
          burnolRadiusTruncatedFourierRaw radius state x := by
        apply integral_congr_ae
        filter_upwards with x
        simp [test, Function.comp_apply, real_smul]

theorem burnolRadiusTruncatedFourier_apply_eq_integral
    {radius : ℝ} (positive : 0 < radius)
    (state : BurnolRadiusIntervalL2 radius) :
    burnolRadiusTruncatedFourier radius state =
      burnolRadiusTruncatedFourierIntegral radius positive state := by
  change burnolRadiusRestriction radius
      (fourierL2 (burnolRadiusZeroExtension radius state)) =
    burnolRadiusTruncatedFourierIntegralValue positive state
  apply Lp.ext
  have restrictionRead := LpToLpRestrictCLM_coeFn ℂ
    (symmetricInterval radius)
    (fourierL2 (burnolRadiusZeroExtension radius state))
  have fourierRead := ae_restrict_of_ae (s := symmetricInterval radius)
    (burnolRadiusFourierL2_zeroExtension_ae_eq_raw state)
  have integralRead := MemLp.coeFn_toLp
    (burnolRadiusTruncatedFourierRaw_memLp positive state)
  filter_upwards [restrictionRead, fourierRead, integralRead]
      with x hxRestriction hxFourier hxIntegral
  have hxRestriction' :
      burnolRadiusRestriction radius
          (fourierL2 (burnolRadiusZeroExtension radius state)) x =
        fourierL2 (burnolRadiusZeroExtension radius state) x := hxRestriction
  have hxIntegral' :
      burnolRadiusTruncatedFourierIntegralValue positive state x =
        burnolRadiusTruncatedFourierRaw radius state x := hxIntegral
  rw [hxRestriction', hxFourier, hxIntegral']

theorem burnolRadiusTruncatedFourier_eq_integral
    {radius : ℝ} (positive : 0 < radius) :
    burnolRadiusTruncatedFourier radius =
      burnolRadiusTruncatedFourierIntegral radius positive := by
  apply ContinuousLinearMap.ext
  exact burnolRadiusTruncatedFourier_apply_eq_integral positive

theorem burnolRadiusTruncatedFourier_opNorm_le
    {radius : ℝ} (positive : 0 < radius) :
    ‖burnolRadiusTruncatedFourier radius‖ ≤ 2 * radius := by
  rw [burnolRadiusTruncatedFourier_eq_integral positive]
  exact burnolRadiusTruncatedFourierIntegral_opNorm_le positive

theorem burnolRadiusTruncatedFourier_opNorm_lt_one
    {radius : ℝ} (positive : 0 < radius) (short : 2 * radius < 1) :
    ‖burnolRadiusTruncatedFourier radius‖ < 1 :=
  lt_of_le_of_lt (burnolRadiusTruncatedFourier_opNorm_le positive) short

end


end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
