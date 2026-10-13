import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.CommonInverse.InverseEuler.Fourier
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
local notation "q" => (1/4:ℝ)
local notation "μq" => volume.restrict (symmetricInterval q)

theorem band_subset_radius (h : ℝ) (nonnegative : 0≤h) :
    sourceBand h ⊆ symmetricInterval (upperRadius h) := by
  intro x inside
  change x∈uIcc (lowerRadius h) (upperRadius h) at inside
  rw [uIcc_of_le (source_radii_ordered h nonnegative)] at inside
  have positive : 0<lowerRadius h := by
    unfold lowerRadius FixedWindowFourierReaction.actualRadius
    positivity
  have nonnegativeX : 0≤x := le_trans positive.le inside.1
  have nonnegativeUpper : 0≤upperRadius h := le_trans nonnegativeX inside.2
  exact ⟨le_trans (neg_nonpos.mpr nonnegativeUpper) nonnegativeX,inside.2⟩

theorem bandField_eq_extension (h : ℝ) (nonnegative : 0≤h) (field : BurnolL2) (raw : ℝ→ℂ)
    (fieldRead : (field:ℝ→ℂ)=ᵐ[volume] (sourceBand h).indicator raw) :
    field=burnolRadiusZeroExtension (upperRadius h) (burnolRadiusRestriction (upperRadius h) field) := by
  have restricted:= (ae_restrict_iff' (measurableSet_symmetricInterval (upperRadius h))).mp
    (LpToLpRestrictCLM_coeFn ℂ (symmetricInterval (upperRadius h)) field)
  apply Lp.ext
  filter_upwards [fieldRead,burnolRadiusZeroExtension_coe
    (burnolRadiusRestriction (upperRadius h) field),restricted] with x read extension localRead
  rw [extension]
  by_cases inside : x∈symmetricInterval (upperRadius h)
  · rw [indicator_of_mem inside]
    change (x∈symmetricInterval (upperRadius h) →
      (burnolRadiusRestriction (upperRadius h) field) x=field x) at localRead
    exact (localRead inside).symm
  · have outside : x∉sourceBand h := fun hx=>inside (band_subset_radius h nonnegative hx)
    rw [read,indicator_of_notMem outside,indicator_of_notMem inside]

theorem bandField_rawFourier (h : ℝ) (nonnegative : 0≤h) (field : BurnolL2) (raw : ℝ→ℂ)
    (fieldRead : (field:ℝ→ℂ)=ᵐ[volume] (sourceBand h).indicator raw) :
    (fourierL2 field:ℝ→ℂ)=ᵐ[volume] bandFourier h raw := by
  let state:=burnolRadiusRestriction (upperRadius h) field
  have extended : field=burnolRadiusZeroExtension (upperRadius h) state :=
    bandField_eq_extension h nonnegative field raw fieldRead
  have full:=burnolRadiusFourierL2_zeroExtension_ae_eq_raw state
  rw [← extended] at full
  have extendedRead :
      (symmetricInterval (upperRadius h)).indicator (fun x:ℝ=>state x)=ᵐ[volume]
        (sourceBand h).indicator raw := by
    have native:=burnolRadiusZeroExtension_coe state
    rw [← extended] at native
    exact native.symm.trans fieldRead
  have actual (frequency : ℝ) :
      burnolRadiusTruncatedFourierRaw (upperRadius h) state frequency=bandFourier h raw frequency := by
    rw [burnolRadiusTruncatedFourierRaw_eq_fourier_zeroExtension,
      Real.fourier_congr_ae extendedRead,Real.fourier_eq]
    unfold bandFourier VectorFourier.fourierIntegral
    rw [← integral_indicator (show MeasurableSet (sourceBand h) from measurableSet_uIcc)]
    apply integral_congr_ae
    filter_upwards with x
    by_cases inside : x∈sourceBand h <;> simp [inside]
  filter_upwards [full] with x read
  exact read.trans (actual x)

theorem dilatedBand_rawFourier (h scale : ℝ) (nonnegative : 0≤h)
    (field : BurnolL2) (raw : ℝ→ℂ)
    (fieldRead : (field:ℝ→ℂ)=ᵐ[volume] (sourceBand h).indicator raw) :
    (fourierL2 (burnolMultiplicativeDilation (-scale) field):ℝ→ℂ)=ᵐ[volume]
      fun x:ℝ=>(Real.exp (scale/2):ℂ)*bandFourier h raw (Real.exp scale*x) := by
  rw [fourierL2_burnolMultiplicativeDilation,neg_neg]
  have qmp : Measure.QuasiMeasurePreserving (fun x:ℝ=>Real.exp scale*x) volume volume := by
    simpa only [smul_eq_mul] using Measure.quasiMeasurePreserving_smul
      (μ:=(volume:Measure ℝ)) (r:=Real.exp scale) (Real.exp_ne_zero scale)
  filter_upwards [burnolMultiplicativeDilation_coeFn scale (fourierL2 field),
    qmp.ae (bandField_rawFourier h nonnegative field raw fieldRead)] with x moved read
  rw [moved]
  unfold burnolL2RawNormalizedDilation
  rw [read]

theorem cotestColumn_raw (h scale : ℝ) (nonnegative : 0≤h)
    (field : BurnolL2) (raw : ℝ→ℂ)
    (fieldRead : (field:ℝ→ℂ)=ᵐ[volume] (sourceBand h).indicator raw) :
    ((cotestColumn scale field:BurnolQuarterIntervalL2):ℝ→ℂ)=ᵐ[μq]
      fun x=>evenBandFourier h scale raw x-cotestMean scale field := by
  let transformed:=fourierL2 (burnolMultiplicativeDilation (-scale) field)
  have direct:=dilatedBand_rawFourier h scale nonnegative field raw fieldRead
  have evenRead : (burnolAmbientEvenPart transformed:ℝ→ℂ)=ᵐ[volume]
      evenBandFourier h scale raw := by
    filter_upwards [Lp.coeFn_smul (1/2:ℂ) (transformed+reflectL2 transformed),
      Lp.coeFn_add transformed (reflectL2 transformed),
      Lp.coeFn_compMeasurePreserving transformed negMeasurePreserving,direct,
      negMeasurePreserving.quasiMeasurePreserving.ae direct]
      with x scalar addition reflection plus minus
    change reflectL2 transformed x=transformed (-x) at reflection
    unfold burnolAmbientEvenPart
    rw [scalar]
    change (1/2:ℂ)*(transformed+reflectL2 transformed:BurnolL2) x=_
    rw [addition]
    change (1/2:ℂ)*(transformed x+reflectL2 transformed x)=_
    rw [reflection,plus,minus]
    unfold evenBandFourier
    rw [mul_neg]
    ring
  have restricted :
      (burnolQuarterRestriction (burnolAmbientEvenPart transformed):ℝ→ℂ)=ᵐ[μq]
        evenBandFourier h scale raw :=
    (LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) _).trans (ae_restrict_of_ae evenRead)
  exact burnolMeanZeroProjection_ae_raw _ _ restricted

theorem bCotestRaw_read (coordinate : BurnolCompletedMellinCoordinate)
    (h scale leg : ℝ) (nonnegative : 0≤h) :
    ((cotestColumn scale (bBand coordinate h leg):BurnolQuarterIntervalL2):ℝ→ℂ)=ᵐ[μq]
      bCotestRaw coordinate h scale leg :=
  cotestColumn_raw h scale nonnegative _ _ (bBand_raw coordinate h leg)
theorem pCotestRaw_read (coordinate : BurnolCompletedMellinCoordinate)
    (h scale leg : ℝ) (nonnegative : 0≤h) :
    ((cotestColumn scale (pBand coordinate h leg):BurnolQuarterIntervalL2):ℝ→ℂ)=ᵐ[μq]
      pCotestRaw coordinate h scale leg :=
  cotestColumn_raw h scale nonnegative _ _ (pBand_raw coordinate h leg)

end OriginalCommonInverseForcing.InverseEuler
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
