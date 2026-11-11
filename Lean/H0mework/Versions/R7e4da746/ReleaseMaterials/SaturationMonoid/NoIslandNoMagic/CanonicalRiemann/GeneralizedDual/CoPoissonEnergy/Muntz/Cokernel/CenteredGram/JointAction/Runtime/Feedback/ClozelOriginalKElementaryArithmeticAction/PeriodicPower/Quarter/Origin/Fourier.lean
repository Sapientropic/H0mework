import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Compact
import Mathlib.MeasureTheory.Measure.OpenPos
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Fourier
open Complex Filter MeasureTheory Set BurnolPhysicalState FourierTransform
open OriginalKElementaryArithmeticAction.PeriodicPower.Resolved OriginalKElementaryArithmeticAction.PeriodicPower.Alias.Continuous
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Compact
open scoped Topology InnerProductSpace FourierTransform
local notation "F"=>fourierL2

def waveFourier (c:BurnolCompletedMellinCoordinate) (h:ℝ):ℝ→ℂ :=
  burnolRadiusTruncatedFourierRaw (waveRadius h)
    (burnolRadiusRestriction (waveRadius h) (compactWave c h))

theorem actual_compact_extension (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nonnegative:0≤h):
    burnolRadiusZeroExtension (waveRadius h)
      (burnolRadiusRestriction (waveRadius h) (compactWave c h))=compactWave c h := by
  have restriction:∀ᵐ x:ℝ ∂volume,x∈symmetricInterval (waveRadius h)→
      burnolRadiusRestriction (waveRadius h) (compactWave c h) x=compactWave c h x:=
    (ae_restrict_iff' (measurableSet_symmetricInterval _)).mp
      (LpToLpRestrictCLM_coeFn ℂ (symmetricInterval (waveRadius h)) (compactWave c h))
  apply Lp.ext
  filter_upwards [burnolRadiusZeroExtension_coe
    (burnolRadiusRestriction (waveRadius h) (compactWave c h)),restriction,actual_compact_raw c h]
    with x extended restricted raw
  rw [extended]
  by_cases inside:x∈symmetricInterval (waveRadius h)
  · rw [indicator_of_mem inside,restricted inside]
  · rw [indicator_of_notMem inside,raw]
    exact (actual_compact_outside c h nonnegative x
      (lt_of_not_ge (fun bound=>inside (abs_le.mp bound)))).symm

theorem actual_wave_fourier_read (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nonnegative:0≤h):
    (F (compactWave c h):ℝ→ℂ)=ᵐ[volume]waveFourier c h := by
  have source:=burnolRadiusFourierL2_zeroExtension_ae_eq_raw
    (burnolRadiusRestriction (waveRadius h) (compactWave c h))
  rw [actual_compact_extension c h nonnegative] at source
  exact source

theorem actual_ordinary_fourier (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nonnegative:0≤h):
    𝓕 (compactRaw c h)=waveFourier c h := by
  have localRead:∀ᵐ x:ℝ ∂volume,x∈symmetricInterval (waveRadius h)→
      burnolRadiusRestriction (waveRadius h) (compactWave c h) x=compactRaw c h x:=by
    apply (ae_restrict_iff' (measurableSet_symmetricInterval _)).mp
    exact (LpToLpRestrictCLM_coeFn ℂ (symmetricInterval (waveRadius h)) (compactWave c h)).trans
      (ae_restrict_of_ae (actual_compact_raw c h))
  funext frequency
  rw [Real.fourier_eq]
  unfold waveFourier burnolRadiusTruncatedFourierRaw VectorFourier.fourierIntegral
  rw [←integral_indicator (measurableSet_symmetricInterval (waveRadius h))]
  apply integral_congr_ae
  filter_upwards [localRead] with x raw
  by_cases inside:x∈symmetricInterval (waveRadius h)
  · rw [indicator_of_mem inside,raw inside]
    rfl
  · rw [indicator_of_notMem inside,actual_compact_outside c h nonnegative x
      (lt_of_not_ge (fun bound=>inside (abs_le.mp bound)))]
    simp only [smul_zero]

def fourierDifference (c:BurnolCompletedMellinCoordinate) (h x:ℝ):ℂ :=
  (Real.exp (h/2):ℂ)*resolvedFourierRaw c (Real.exp h*x)-waveCharacter c h*resolvedFourierRaw c x

private theorem fourier_difference_ae (c:BurnolCompletedMellinCoordinate) (h:ℝ):
    (F (compactWave c h):ℝ→ℂ)=ᵐ[volume]fourierDifference c h := by
  have scale:Measure.QuasiMeasurePreserving (fun x:ℝ=>Real.exp h*x) volume volume:=by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ:=(volume:Measure ℝ))
        (r:=Real.exp h) (Real.exp_ne_zero h))
  rw [compactWave,map_sub,map_smul,fourierL2_burnolMultiplicativeDilation,neg_neg]
  filter_upwards [Lp.coeFn_sub (burnolMultiplicativeDilation h (F (resolvedSource c)))
      (waveCharacter c h • F (resolvedSource c)),
    burnolMultiplicativeDilation_coeFn h (F (resolvedSource c)),
    Lp.coeFn_smul (waveCharacter c h) (F (resolvedSource c)),actual_resolved_fourier_raw c,
    scale.ae (actual_resolved_fourier_raw c)] with x difference dilation scalar direct moved
  rw [difference,Pi.sub_apply,dilation,scalar,Pi.smul_apply,smul_eq_mul]
  change (Real.exp (h/2):ℂ)*F (resolvedSource c) (Real.exp h*x)-waveCharacter c h*F (resolvedSource c) x=_
  rw [direct,moved]
  rfl

/-- The ordinary compact Fourier transform is the full difference of the original Fg at every nonzero point. -/
theorem actual_fourier_difference (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nonnegative:0≤h)
    (x:ℝ) (nonzero:x≠0):𝓕 (compactRaw c h) x=fourierDifference c h x := by
  have same:waveFourier c h=ᵐ[volume]fourierDifference c h:=
    (actual_wave_fourier_read c h nonnegative).symm.trans (fourier_difference_ae c h)
  have continuousLeft:ContinuousAt (waveFourier c h) x:=
    (burnolRadiusTruncatedFourierRaw_continuous _).continuousAt
  have continuousRight:ContinuousAt (fourierDifference c h) x:=by
    exact (continuousAt_const.mul ((actual_resolved_continuousAt c (Real.exp h*x)
      (mul_ne_zero (Real.exp_ne_zero h) nonzero)).comp
        (continuous_const.mul continuous_id).continuousAt)).sub
      (continuousAt_const.mul (actual_resolved_continuousAt c x nonzero))
  rw [actual_ordinary_fourier c h nonnegative]
  exact tendsto_nhds_unique_of_frequently_eq continuousLeft continuousRight
    (mem_closure_iff_frequently.mp ((Measure.dense_of_ae same) x))

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Origin.Fourier
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
