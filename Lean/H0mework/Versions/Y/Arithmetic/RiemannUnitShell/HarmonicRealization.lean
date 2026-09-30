import H0mework.Versions.Y.Arithmetic.RiemannUnitShell.HarmonicCount
import H0mework.Versions.Y.Arithmetic.RiemannUnitShell.StepCount

/-! The original Fourier step has the harmonic representative produced by its actual Tate box, via the existing full-source recovery. -/

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

local instance : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

/-- The original Fourier image has the source-generated harmonic representative almost everywhere. -/
theorem burnolReciprocalStepFourier_coeFn (lower upper : ℝ) (lowerStrict : (1 / 4 : ℝ) < lower)
    (ordered : lower ≤ upper) (bounded : upper ≤ 4) :
    (fourierL2 (burnolReciprocalStepNativeWave lower upper) : ℝ → ℂ) =ᵐ[volume]
      burnolHarmonicStepWaveRaw lower upper := by
  have lowerPositive : 0 < lower := lt_trans (by norm_num) lowerStrict
  have upperPositive := lowerPositive.trans_le ordered
  rw [burnolReciprocalStepNativeWave_eq lower upper lowerPositive ordered]
  let original := burnolReciprocalStepSourceL2 lower upper lowerPositive ordered
  let source := burnolTateReciprocalL2 original
  let value := fourierL2 (burnolReciprocalStepWaveL2 lower upper lowerPositive ordered)
  have represents : (source : ℝ → ℂ) =ᵐ[volume] burnolTateStepBoxRaw lower upper :=
    burnolReciprocalStepSource_tate_raw lower upper lowerPositive ordered
  have even : reflectL2 source = source :=
    burnolReflectL2_eq_of_even_raw source _ represents (fun x => by simp only [burnolTateStepBoxRaw, abs_neg])
  have gap : (source : ℝ → ℂ) =ᵐ[volume.restrict (symmetricInterval (1 / 4 : ℝ))] fun _ => 0 := by
    filter_upwards [ae_restrict_of_ae represents,
      ae_restrict_mem (measurableSet_symmetricInterval (1 / 4 : ℝ))] with x read inside
    rw [read]
    unfold burnolTateStepBoxRaw
    apply if_neg
    intro active
    linarith [abs_le.mpr inside, active.1]
  have realization (test : SchwartzMap ℝ ℂ) : burnolRemainderSourceRead source test =
      ∫ x : ℝ, test x * value x := by
    simpa only [Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistribution_apply, smul_eq_mul] using
      burnolRemainderRealization_fourier original
        (burnolReciprocalStepWaveL2 lower upper lowerPositive ordered)
        (burnolReciprocalStepSource_realizes lower upper lowerPositive ordered bounded) test
  obtain ⟨raw, rawRep, _, valueRep⟩ :=
    burnolRemainderSourceRead_realization_ae source value even gap realization
  have same : raw =ᵐ[volume] burnolTateStepBoxRaw lower upper := rawRep.symm.trans represents
  have coSum := burnolInnerGapForward_ae_congr raw (burnolTateStepBoxRaw lower upper) same
  have mean : (∫ u : ℝ in Ioi 0, (u : ℂ)⁻¹ * raw u) = (Real.log (upper / lower) : ℂ) := by
    calc
      _ = ∫ u : ℝ in Ioi 0, (u : ℂ)⁻¹ * burnolTateStepBoxRaw lower upper u := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae same] with x hx
        rw [hx]
      _ = _ := burnolTateStepBox_reciprocalMean lower upper lowerPositive ordered
  change (value : ℝ → ℂ) =ᵐ[volume] burnolHarmonicStepWaveRaw lower upper
  filter_upwards [valueRep, coSum] with x valueAt sumAt
  rw [valueAt, sumAt, mean, burnolTateStepBox_finiteCoSum lower upper x lowerPositive upperPositive]
  rfl
end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
