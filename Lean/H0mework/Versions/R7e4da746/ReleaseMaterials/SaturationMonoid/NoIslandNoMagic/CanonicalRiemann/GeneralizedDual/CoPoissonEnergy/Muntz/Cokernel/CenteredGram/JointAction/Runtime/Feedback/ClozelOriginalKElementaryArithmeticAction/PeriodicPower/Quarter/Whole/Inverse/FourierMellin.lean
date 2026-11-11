import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.FourierTail

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.FourierMellin
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.PositionPrice
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.FourierTail
open scoped Topology InnerProductSpace
open private logSource_zero from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Source
open private mellin_source_ae from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.ResolventSource
local notation "q"=>(1/4:ℝ)

private theorem inverse_fourier_memLp (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    MemLp (inverseFourierRaw c zero) 2 volume:=by
  change MemLp (burnolRadiusTruncatedFourierRaw q (sourceInverse c zero:BurnolQuarterIntervalL2)) 2 volume
  exact (Lp.memLp (fourierL2 (burnolQuarterZeroExtension (sourceInverse c zero:BurnolQuarterIntervalL2)))).ae_eq
    (burnolRadiusFourierL2_zeroExtension_ae_eq_raw (sourceInverse c zero:BurnolQuarterIntervalL2))

private theorem inverse_fourier_top (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    inverseFourierRaw c zero=O[atTop](fun x:ℝ=>x^(-(1:ℝ))):=by
  obtain ⟨C,_,bound⟩:=actual_inverse_fourier_tail c zero
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop (1:ℝ)] with x large
  have positive:0<x:=lt_of_lt_of_le (by norm_num) large
  simpa only [Real.rpow_neg_one,Real.norm_eq_abs,abs_inv,abs_of_pos positive,div_eq_mul_inv] using bound x large

private theorem inverse_fourier_origin (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    inverseFourierRaw c zero=O[𝓝[>] 0](fun x:ℝ=>x^(-(0:ℝ))):=by
  apply Asymptotics.IsBigO.of_bound (Real.sqrt (2*q)*‖(sourceInverse c zero:BurnolQuarterIntervalL2)‖)
  filter_upwards with x
  simpa only [inverseFourierRaw,neg_zero,Real.rpow_zero,norm_one,mul_one] using
    burnolRadiusTruncatedFourierRaw_norm_le (by norm_num : (0:ℝ)<q)
      (sourceInverse c zero:BurnolQuarterIntervalL2) x

private theorem logarithmic_top (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (j:ℕ) (a:ℝ) (below:a<1):
    logSource (inverseFourierRaw c zero) j=O[atTop](fun x:ℝ=>x^(-a)):=by
  have logarithm:(fun x:ℝ=>(Real.log x)^j)=O[atTop](fun x:ℝ=>x^(1-a)):=by
    simpa only [Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop (j:ℝ) (by linarith : 0<1-a)).isBigO
  have product:=logarithm.smul (inverse_fourier_top c zero)
  apply product.congr' (EventuallyEq.refl _ _)
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x positive
  change x^(1-a)*x^(-(1:ℝ))=x^(-a)
  rw [←Real.rpow_add positive]
  congr 1
  ring

private theorem logarithmic_origin (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (j:ℕ) (b:ℝ) (above:0<b):
    logSource (inverseFourierRaw c zero) j=O[𝓝[>] 0](fun x:ℝ=>x^(-b)):=by
  have logarithm:(fun x:ℝ=>(Real.log x)^j)=O[𝓝[>] 0](fun x:ℝ=>x^(-b)):=by
    apply Asymptotics.IsBigO.of_norm_left
    simpa only [Real.norm_eq_abs,abs_pow,Real.rpow_natCast] using
      (isLittleO_abs_log_rpow_rpow_nhdsGT_zero (j:ℝ) (by linarith : -b<0)).isBigO
  have product:=logarithm.smul (inverse_fourier_origin c zero)
  apply product.congr' (EventuallyEq.refl _ _)
  filter_upwards with x
  change x^(-b)*x^(-(0:ℝ))=x^(-b)
  simp

/-- Every original log moment of the actual inverse Fourier correction belongs to the full strip. -/
theorem actual_inverse_fourier_log_mellin (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (j:ℕ) (w:ℂ) (positive:0<w.re) (below:w.re<1):
    MellinConvergent (logSource (inverseFourierRaw c zero) j) w:=by
  have logarithm:ContinuousOn (fun x:ℝ=>(Real.log x)^j) (Ioi 0):=by
    intro x hx
    exact ((Real.continuousAt_log hx.ne').pow j).continuousWithinAt
  have localSource:LocallyIntegrableOn (logSource (inverseFourierRaw c zero) j) (Ioi 0):=
    LocallyIntegrableOn.continuousOn_smul isOpen_Ioi.isLocallyClosed
      (((inverse_fourier_memLp c zero).locallyIntegrable (by norm_num)).locallyIntegrableOn _) logarithm
  exact mellinConvergent_of_isBigO_rpow localSource
    (logarithmic_top c zero j ((w.re+1)/2) (by linarith)) (by linarith)
    (logarithmic_origin c zero j (w.re/2) (by linarith)) (by linarith)

theorem actual_inverse_fourier_mellin (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (w:ℂ) (positive:0<w.re) (below:w.re<1):MellinConvergent (inverseFourierRaw c zero) w:=by
  simpa only [logSource_zero] using actual_inverse_fourier_log_mellin c zero 0 w positive below

theorem actual_inverse_fourier_hasMellin (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (w:ℂ) (positive:0<w.re) (below:w.re<1):
    HasMellin (fourierL2 (burnolQuarterZeroExtension (sourceInverse c zero:BurnolQuarterIntervalL2)):ℝ→ℂ)
      w (mellin (inverseFourierRaw c zero) w):=
  mellin_source_ae _ _ _ _ (ae_restrict_of_ae
    (burnolRadiusFourierL2_zeroExtension_ae_eq_raw (sourceInverse c zero:BurnolQuarterIntervalL2)))
    ⟨actual_inverse_fourier_mellin c zero w positive below,rfl⟩

theorem actual_inverse_fourier_mellin_differentiable (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (w:ℂ) (positive:0<w.re) (below:w.re<1):
    DifferentiableAt ℂ (mellin (inverseFourierRaw c zero)) w:=
  mellin_differentiableAt_of_isBigO_rpow
    (((inverse_fourier_memLp c zero).locallyIntegrable (by norm_num)).locallyIntegrableOn _)
    (inverse_fourier_top c zero) below (inverse_fourier_origin c zero) positive

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.FourierMellin
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
