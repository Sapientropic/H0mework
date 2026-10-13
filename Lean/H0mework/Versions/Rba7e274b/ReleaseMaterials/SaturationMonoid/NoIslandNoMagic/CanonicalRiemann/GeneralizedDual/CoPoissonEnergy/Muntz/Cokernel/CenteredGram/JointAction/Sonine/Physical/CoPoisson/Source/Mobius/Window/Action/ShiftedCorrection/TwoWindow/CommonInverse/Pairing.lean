import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.CommonInverse.Transport
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalCommonInverseForcing
open Complex MeasureTheory Set Filter OriginalRieszSource
open scoped Topology InnerProductSpace ENNReal
open OriginalTwoWindowInverseForcing

theorem source_radii_ordered (h : ℝ) (nonnegative : 0≤h) : lowerRadius h≤upperRadius h := by
  unfold lowerRadius upperRadius FixedWindowFourierReaction.actualRadius
  gcongr
  linarith

theorem whole_fourier_dilation_raw (state : BurnolQuarterMeanZeroCarrier) (scale : ℝ) :
    (burnolMultiplicativeDilation scale (fourierL2 (whole state)):ℝ→ℂ)=ᵐ[volume]
      fun x:ℝ=>(Real.exp (scale/2):ℂ)*rawFourier state (Real.exp scale*x) := by
  have qmp : Measure.QuasiMeasurePreserving (fun x:ℝ=>Real.exp scale*x) volume volume := by
    simpa only [smul_eq_mul] using Measure.quasiMeasurePreserving_smul
      (μ:=(volume:Measure ℝ)) (r:=Real.exp scale) (Real.exp_ne_zero scale)
  have source:=burnolRadiusFourierL2_zeroExtension_ae_eq_raw (state:BurnolQuarterIntervalL2)
  change (fourierL2 (whole state):ℝ→ℂ)=ᵐ[volume] rawFourier state at source
  filter_upwards [burnolMultiplicativeDilation_coeFn scale (fourierL2 (whole state)),qmp.ae source]
    with x dilated native
  rw [dilated]
  unfold burnolL2RawNormalizedDilation
  rw [native]

theorem band_full_fourier_inner (state : BurnolQuarterMeanZeroCarrier) (h scale : ℝ)
    (nonnegative : 0≤h) (field : BurnolL2) (raw : ℝ→ℂ)
    (fieldRead : (field:ℝ→ℂ)=ᵐ[volume] (sourceBand h).indicator raw) :
    inner ℂ (burnolMultiplicativeDilation scale (fourierL2 (whole state))) field=
      (Real.exp (scale/2):ℂ)*(∫ x:ℝ in (lowerRadius h)..(upperRadius h),
        star (rawFourier state (Real.exp scale*x))*raw x) := by
  have density : (fun x:ℝ=>inner ℂ
      (burnolMultiplicativeDilation scale (fourierL2 (whole state)) x) (field x))=ᵐ[volume]
    (sourceBand h).indicator (fun x:ℝ=>(Real.exp (scale/2):ℂ)*
      (star (rawFourier state (Real.exp scale*x))*raw x)) := by
    filter_upwards [whole_fourier_dilation_raw state scale,fieldRead] with x source field
    by_cases inside : x∈sourceBand h
    · rw [source,field,indicator_of_mem inside,indicator_of_mem inside,RCLike.inner_apply]
      rw [(starRingEnd ℂ).map_mul, Complex.conj_ofReal]
      change raw x*((Real.exp (scale/2):ℂ)*star (rawFourier state (Real.exp scale*x)))=_
      ring
    · rw [field,indicator_of_notMem inside,inner_zero_right,indicator_of_notMem inside]
  rw [L2.inner_def,integral_congr_ae density,
    integral_indicator (show MeasurableSet (sourceBand h) from measurableSet_uIcc)]
  unfold sourceBand
  rw [uIcc_of_le (source_radii_ordered h nonnegative),integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (source_radii_ordered h nonnegative),intervalIntegral.integral_const_mul]

theorem band_cotest_read (state : BurnolQuarterMeanZeroCarrier)
    (even : reflectRestricted (1/4:ℝ) (state:BurnolQuarterIntervalL2)=state)
    (coordinate : BurnolCompletedMellinCoordinate) (h scale leg : ℝ) (nonnegative : 0≤h) :
    (∫ x:ℝ in (lowerRadius h)..(upperRadius h),
      star (rawFourier state (Real.exp scale*x))*bLeg coordinate leg x)=
      (Real.exp (-scale/2):ℂ)*inner ℂ state (cotestColumn scale (bBand coordinate h leg)) := by
  have full:=band_full_fourier_inner state h scale nonnegative (bBand coordinate h leg)
    (bLeg coordinate leg) (bBand_raw coordinate h leg)
  rw [quarter_cotest_pairing state even] at full
  have cancel : (Real.exp (-scale/2):ℂ)*(Real.exp (scale/2):ℂ)=1 := by
    rw [← Complex.ofReal_mul,← Real.exp_add,show -scale/2+scale/2=0 by ring,Real.exp_zero,Complex.ofReal_one]
  rw [full,← mul_assoc,cancel,one_mul]

theorem return_band_cotest_read (state : BurnolQuarterMeanZeroCarrier)
    (even : reflectRestricted (1/4:ℝ) (state:BurnolQuarterIntervalL2)=state)
    (coordinate : BurnolCompletedMellinCoordinate) (h scale leg : ℝ) (nonnegative : 0≤h) :
    (∫ x:ℝ in (lowerRadius h)..(upperRadius h),
      star (rawFourier state (Real.exp scale*x))*pLeg coordinate leg x)=
      (Real.exp (-scale/2):ℂ)*inner ℂ state (cotestColumn scale (pBand coordinate h leg)) := by
  have full:=band_full_fourier_inner state h scale nonnegative (pBand coordinate h leg)
    (pLeg coordinate leg) (pBand_raw coordinate h leg)
  rw [quarter_cotest_pairing state even] at full
  have cancel : (Real.exp (-scale/2):ℂ)*(Real.exp (scale/2):ℂ)=1 := by
    rw [← Complex.ofReal_mul,← Real.exp_add,show -scale/2+scale/2=0 by ring,Real.exp_zero,Complex.ofReal_one]
  rw [full,← mul_assoc,cancel,one_mul]

end OriginalCommonInverseForcing
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
