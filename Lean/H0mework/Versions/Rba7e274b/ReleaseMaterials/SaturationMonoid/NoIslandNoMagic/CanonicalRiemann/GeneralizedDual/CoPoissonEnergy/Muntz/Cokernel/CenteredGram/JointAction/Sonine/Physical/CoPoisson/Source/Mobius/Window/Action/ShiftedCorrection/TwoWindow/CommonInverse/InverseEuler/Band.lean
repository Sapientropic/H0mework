import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.CommonInverse.InverseEuler.Ward
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalCommonInverseForcing.InverseEuler
open Complex Filter FourierTransform MeasureTheory Set OriginalRieszSource
open scoped ENNReal InnerProductSpace Topology
open OriginalTwoWindowInverseForcing OriginalCommonInverseForcing
attribute [local instance 1100] NormedSpace.complexToReal
local notation "μband" h => volume.restrict (sourceBand h)

def forceBLeg (coordinate : BurnolCompletedMellinCoordinate) (leg x : ℝ) : ℂ :=
  forceB coordinate (Real.exp leg*x)
def forcePLeg (coordinate : BurnolCompletedMellinCoordinate) (leg x : ℝ) : ℂ :=
  forceP coordinate (Real.exp leg*x)

theorem forceBLeg_continuous (coordinate : BurnolCompletedMellinCoordinate) (leg : ℝ) :
    Continuous (forceBLeg coordinate leg) := by
  have ru : Continuous (rawFourier Response.u) := burnolRadiusTruncatedFourierRaw_continuous _
  have rv : Continuous (rawFourier Response.v) := burnolRadiusTruncatedFourierRaw_continuous _
  have edge:=Edge.raw_continuous (1/4:ℝ)
  unfold forceBLeg forceB responseV responseU
  fun_prop
theorem forcePLeg_continuous (coordinate : BurnolCompletedMellinCoordinate) (leg : ℝ) :
    Continuous (forcePLeg coordinate leg) := by
  have ru : Continuous (rawFourier Response.u) := burnolRadiusTruncatedFourierRaw_continuous _
  have rv : Continuous (rawFourier Response.v) := burnolRadiusTruncatedFourierRaw_continuous _
  have edge:=Edge.raw_continuous (1/4:ℝ)
  unfold forcePLeg forceP responseV responseU
  fun_prop

theorem bLeg_source_derivative (coordinate : BurnolCompletedMellinCoordinate) (leg x : ℝ)
    (positive : 0<x) : HasDerivAt (bLeg coordinate leg)
    ((lambda coordinate*bLeg coordinate leg x+forceBLeg coordinate leg x-
      (1/2:ℂ)*bLeg coordinate leg x)/(x:ℂ)) x := by
  have source:=(b_hasDerivAt coordinate (Real.exp leg*x) (mul_pos (Real.exp_pos _) positive)).scomp x
    ((hasDerivAt_id x).const_mul (Real.exp leg))
  have normalized : HasDerivAt (bLeg coordinate leg)
      ((Real.exp leg:ℂ)*((lambda coordinate*b coordinate (Real.exp leg*x)+
        forceB coordinate (Real.exp leg*x)-(1/2:ℂ)*b coordinate (Real.exp leg*x))/
        (Real.exp leg*x:ℝ))) x := by
    simpa only [bLeg,Function.comp_def,id_eq,mul_one,real_smul,smul_eq_mul] using! source
  convert! normalized using 1
  unfold bLeg forceBLeg
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr positive.ne',
    Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero leg)]

theorem pLeg_source_derivative (coordinate : BurnolCompletedMellinCoordinate) (leg x : ℝ)
    (positive : 0<x) : HasDerivAt (pLeg coordinate leg)
    ((-lambda coordinate*pLeg coordinate leg x+forcePLeg coordinate leg x-
      (1/2:ℂ)*pLeg coordinate leg x)/(x:ℂ)) x := by
  have source:=(p_hasDerivAt coordinate (Real.exp leg*x) (mul_pos (Real.exp_pos _) positive)).scomp x
    ((hasDerivAt_id x).const_mul (Real.exp leg))
  have normalized : HasDerivAt (pLeg coordinate leg)
      ((Real.exp leg:ℂ)*((-lambda coordinate*p coordinate (Real.exp leg*x)+
        forceP coordinate (Real.exp leg*x)-(1/2:ℂ)*p coordinate (Real.exp leg*x))/
        (Real.exp leg*x:ℝ))) x := by
    simpa only [pLeg,Function.comp_def,id_eq,mul_one,real_smul,smul_eq_mul] using! source
  convert! normalized using 1
  unfold pLeg forcePLeg
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr positive.ne',
    Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero leg)]

theorem bandFourier_integral (h frequency : ℝ) (nonnegative : 0≤h) (raw : ℝ→ℂ) :
    bandFourier h raw frequency=∫ x:ℝ in (lowerRadius h)..(upperRadius h),
      Constructor.phase frequency x*raw x := by
  unfold bandFourier VectorFourier.fourierIntegral sourceBand
  rw [uIcc_of_le (source_radii_ordered h nonnegative),integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (source_radii_ordered h nonnegative)]
  apply intervalIntegral.integral_congr
  intro x _
  simp only [innerₗ_apply_apply,Real.inner_apply,Circle.smul_def,smul_eq_mul,Constructor.phase]
  rw [mul_comm x frequency]

theorem bandDerivative_integral (h frequency : ℝ) (nonnegative : 0≤h) (raw : ℝ→ℂ)
    (continuous : ContinuousOn raw (sourceBand h)) :
    bandDerivative h raw frequency=∫ x:ℝ in (lowerRadius h)..(upperRadius h),
      Constructor.phase frequency x*(-2*(Real.pi:ℂ)*Complex.I*(x:ℂ)*raw x) := by
  have moment : Integrable (VectorFourier.fourierSMulRight (innerSL ℝ) raw) (μband h) := by
    apply (show ContinuousOn (VectorFourier.fourierSMulRight (innerSL ℝ) raw) (sourceBand h)
      from ?_).integrableOn_Icc
    unfold VectorFourier.fourierSMulRight
    have paired : ContinuousOn (fun x:ℝ=>((innerSL ℝ) x,raw x)) (sourceBand h) :=
      (innerSL ℝ).continuous.continuousOn.prodMk continuous
    exact ((ContinuousLinearMap.smulRightL ℝ ℝ ℂ).continuous₂.comp_continuousOn
      paired).const_smul (-(2*(Real.pi:ℂ)*Complex.I):ℂ)
  unfold bandDerivative
  rw [Real.fourierIntegral_continuousLinearMap_apply' moment]
  unfold VectorFourier.fourierIntegral sourceBand
  rw [uIcc_of_le (source_radii_ordered h nonnegative),integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (source_radii_ordered h nonnegative)]
  apply intervalIntegral.integral_congr
  intro x _
  have innerOne : (innerSL ℝ) x 1=x := by rw [innerSL_apply_apply,Real.inner_apply,mul_one]
  have innerFrequency : (innerSL ℝ) x frequency=x*frequency := by rw [innerSL_apply_apply,Real.inner_apply]
  simp only [VectorFourier.fourierSMulRight_apply,
    ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply,innerOne,innerFrequency,
    Circle.smul_def,smul_eq_mul,Constructor.phase,real_smul]
  rw [mul_comm x frequency]
  ring

theorem band_source_euler (h frequency : ℝ) (nonnegative : 0≤h)
    (raw force : ℝ→ℂ) (weight : ℂ)
    (rawContinuous : ContinuousOn raw (sourceBand h))
    (forceContinuous : ContinuousOn force (sourceBand h))
    (source : ∀ x∈sourceBand h,HasDerivAt raw
      ((weight*raw x+force x-(1/2:ℂ)*raw x)/(x:ℂ)) x) :
    (frequency:ℂ)*bandDerivative h raw frequency+(weight+1/2)*bandFourier h raw frequency+
      bandFourier h force frequency=
      (upperRadius h:ℂ)*Constructor.phase frequency (upperRadius h)*raw (upperRadius h)-
      (lowerRadius h:ℂ)*Constructor.phase frequency (lowerRadius h)*raw (lowerRadius h) := by
  let primitive:=fun x:ℝ=>(x:ℂ)*Constructor.phase frequency x*raw x
  let density:=fun x:ℝ=>Constructor.phase frequency x*
    ((weight+1/2-2*(Real.pi:ℂ)*Complex.I*(frequency:ℂ)*(x:ℂ))*raw x+force x)
  have generated (x : ℝ) (inside : x∈sourceBand h) : HasDerivAt primitive (density x) x := by
    have actual:=((Complex.ofRealCLM.hasDerivAt (x:=x)).mul
      (Constructor.phase_derivative frequency x)).mul (source x inside)
    convert! actual using 1
    dsimp only [density,Complex.ofRealCLM_apply,Pi.mul_apply,Complex.ofReal_one]
    field_simp [Complex.ofReal_ne_zero.mpr (two_window_positive h x inside).ne']
    ring
  have densityContinuous : ContinuousOn density (sourceBand h) := by
    have phase:=Constructor.phaseContinuous frequency
    dsimp only [density]
    fun_prop
  have integral:=intervalIntegral.integral_eq_sub_of_hasDerivAt generated densityContinuous.intervalIntegrable
  rw [bandDerivative_integral h frequency nonnegative raw rawContinuous,
    bandFourier_integral h frequency nonnegative,bandFourier_integral h frequency nonnegative]
  let moment:=fun x:ℝ=>Constructor.phase frequency x*(-2*(Real.pi:ℂ)*Complex.I*(x:ℂ)*raw x)
  let returned:=fun x:ℝ=>Constructor.phase frequency x*raw x
  let forcing:=fun x:ℝ=>Constructor.phase frequency x*force x
  have momentContinuous : ContinuousOn moment (sourceBand h) := by
    have phase:=Constructor.phaseContinuous frequency
    dsimp only [moment]
    fun_prop
  have returnedContinuous : ContinuousOn returned (sourceBand h) :=
    (Constructor.phaseContinuous frequency).continuousOn.mul rawContinuous
  have forcingContinuous : ContinuousOn forcing (sourceBand h) :=
    (Constructor.phaseContinuous frequency).continuousOn.mul forceContinuous
  change (frequency:ℂ)*(∫ x:ℝ in (lowerRadius h)..(upperRadius h),moment x)+
    (weight+1/2)*(∫ x:ℝ in (lowerRadius h)..(upperRadius h),returned x)+
    (∫ x:ℝ in (lowerRadius h)..(upperRadius h),forcing x)=_
  calc
    _=∫ x:ℝ in (lowerRadius h)..(upperRadius h),
        ((frequency:ℂ)*moment x+(weight+1/2)*returned x)+forcing x := by
      rw [intervalIntegral.integral_add
        (f:=fun x=>(frequency:ℂ)*moment x+(weight+1/2)*returned x) (g:=forcing)
        (((momentContinuous.const_mul (frequency:ℂ)).add
          (returnedContinuous.const_mul (weight+1/2))).intervalIntegrable)
        forcingContinuous.intervalIntegrable,
        intervalIntegral.integral_add (f:=fun x=>(frequency:ℂ)*moment x)
          (g:=fun x=>(weight+1/2)*returned x)
          (momentContinuous.const_mul (frequency:ℂ)).intervalIntegrable
          (returnedContinuous.const_mul (weight+1/2)).intervalIntegrable,
        intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
    _=∫ x:ℝ in (lowerRadius h)..(upperRadius h),density x := by
      apply intervalIntegral.integral_congr
      intro x _
      dsimp only [moment,returned,forcing,density]
      ring
    _=_ := integral

theorem b_band_source_euler (coordinate : BurnolCompletedMellinCoordinate)
    (h leg frequency : ℝ) (nonnegative : 0≤h) :
    (frequency:ℂ)*bandDerivative h (bLeg coordinate leg) frequency+
      (lambda coordinate+1/2)*bandFourier h (bLeg coordinate leg) frequency+
      bandFourier h (forceBLeg coordinate leg) frequency=
      (upperRadius h:ℂ)*Constructor.phase frequency (upperRadius h)*bLeg coordinate leg (upperRadius h)-
      (lowerRadius h:ℂ)*Constructor.phase frequency (lowerRadius h)*bLeg coordinate leg (lowerRadius h) :=
  band_source_euler h frequency nonnegative _ _ _ (bLeg_continuousOn coordinate h leg)
    (forceBLeg_continuous coordinate leg).continuousOn
    (fun x inside=>bLeg_source_derivative coordinate leg x (two_window_positive h x inside))
theorem p_band_source_euler (coordinate : BurnolCompletedMellinCoordinate)
    (h leg frequency : ℝ) (nonnegative : 0≤h) :
    (frequency:ℂ)*bandDerivative h (pLeg coordinate leg) frequency+
      (-lambda coordinate+1/2)*bandFourier h (pLeg coordinate leg) frequency+
      bandFourier h (forcePLeg coordinate leg) frequency=
      (upperRadius h:ℂ)*Constructor.phase frequency (upperRadius h)*pLeg coordinate leg (upperRadius h)-
      (lowerRadius h:ℂ)*Constructor.phase frequency (lowerRadius h)*pLeg coordinate leg (lowerRadius h) :=
  band_source_euler h frequency nonnegative _ _ _ (pLeg_continuousOn coordinate h leg)
    (forcePLeg_continuous coordinate leg).continuousOn
    (fun x inside=>pLeg_source_derivative coordinate leg x (two_window_positive h x inside))

end OriginalCommonInverseForcing.InverseEuler
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
