import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Tail
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Source

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Mellin
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Consumer OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Whole
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Counting OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Tail
open scoped Topology InnerProductSpace
open private logSource_zero from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Source
open private mellin_source_ae from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.ResolventSource

theorem actual_counted_memLp (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0) :
    MemLp (wholeCountedRaw c) 2 volume :=
  (Lp.memLp (fourierL2 (wholeValue c zero 1 (by norm_num)))).ae_eq
    (actual_whole_fourier_raw c zero 1 (by norm_num))

private theorem counted_top (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0) :
    wholeCountedRaw c=O[atTop](fun x:ℝ=>x^(-(1:ℝ))) := by
  obtain ⟨C,_,bound⟩:=actual_whole_counted_tail c zero
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop (1:ℝ)] with x large
  have positive:0<x:=lt_of_lt_of_le (by norm_num) large
  simpa only [Real.rpow_neg_one,Real.norm_eq_abs,abs_inv,abs_of_pos positive,div_eq_mul_inv] using bound x large

private theorem counted_origin (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0) :
    wholeCountedRaw c=O[𝓝[>] 0](fun x:ℝ=>x^(-(0:ℝ))) := by
  apply Asymptotics.IsBigO.of_bound ‖-quarterMean c/4‖
  filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num:(0:ℝ)<4))]
    with x positive small
  rw [actual_counted_gap c zero x (by rw [abs_of_pos positive];exact small.le)]
  simp only [neg_zero,Real.rpow_zero,norm_one,mul_one,le_refl]

private theorem counted_log_top (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (j : ℕ) (a : ℝ) (below : a<1) :
    logSource (wholeCountedRaw c) j=O[atTop](fun x:ℝ=>x^(-a)) := by
  have logarithm:(fun x:ℝ=>(Real.log x)^j)=O[atTop](fun x:ℝ=>x^(1-a)) := by
    simpa only [Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop (j:ℝ) (by linarith:0<1-a)).isBigO
  have product:=logarithm.smul (counted_top c zero)
  apply product.congr' (EventuallyEq.refl _ _)
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x positive
  change x^(1-a)*x^(-(1:ℝ))=x^(-a)
  rw [←Real.rpow_add positive]
  congr 1
  ring

private theorem counted_log_origin (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (j : ℕ) (b : ℝ) (above : 0<b) :
    logSource (wholeCountedRaw c) j=O[𝓝[>] 0](fun x:ℝ=>x^(-b)) := by
  have logarithm:(fun x:ℝ=>(Real.log x)^j)=O[𝓝[>] 0](fun x:ℝ=>x^(-b)) := by
    apply Asymptotics.IsBigO.of_norm_left
    simpa only [Real.norm_eq_abs,abs_pow,Real.rpow_natCast] using
      (isLittleO_abs_log_rpow_rpow_nhdsGT_zero (j:ℝ) (by linarith:-b<0)).isBigO
  have product:=logarithm.smul (counted_origin c zero)
  apply product.congr' (EventuallyEq.refl _ _)
  filter_upwards with x
  change x^(-b)*x^(-(0:ℝ))=x^(-b)
  simp

/-- All logarithmic reads belong to the whole counting field on the actual full strip. -/
theorem actual_counted_log_mellin (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (j : ℕ) (w : ℂ) (positive : 0<w.re) (below : w.re<1) :
    MellinConvergent (logSource (wholeCountedRaw c) j) w := by
  have logarithm:ContinuousOn (fun x:ℝ=>(Real.log x)^j) (Ioi 0) := by
    intro x hx
    exact ((Real.continuousAt_log hx.ne').pow j).continuousWithinAt
  have localSource:LocallyIntegrableOn (logSource (wholeCountedRaw c) j) (Ioi 0) :=
    LocallyIntegrableOn.continuousOn_smul isOpen_Ioi.isLocallyClosed
      (((actual_counted_memLp c zero).locallyIntegrable (by norm_num)).locallyIntegrableOn _) logarithm
  exact mellinConvergent_of_isBigO_rpow localSource
    (counted_log_top c zero j ((w.re+1)/2) (by linarith)) (by linarith)
    (counted_log_origin c zero j (w.re/2) (by linarith)) (by linarith)

theorem actual_counted_mellin (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (w : ℂ) (positive : 0<w.re) (below : w.re<1) : MellinConvergent (wholeCountedRaw c) w := by
  simpa only [logSource_zero] using actual_counted_log_mellin c zero 0 w positive below

theorem actual_fourier_whole_mellin (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (positiveH : 0<h) (w : ℂ) (positive : 0<w.re) (below : w.re<1) :
    HasMellin (fourierL2 (wholeValue c zero h positiveH):ℝ→ℂ) w (mellin (wholeCountedRaw c) w) :=
  mellin_source_ae _ _ _ _ (ae_restrict_of_ae (actual_whole_fourier_raw c zero h positiveH))
    ⟨actual_counted_mellin c zero w positive below,rfl⟩

theorem actual_counted_mellin_differentiable (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (w : ℂ) (positive : 0<w.re) (below : w.re<1) :
    DifferentiableAt ℂ (mellin (wholeCountedRaw c)) w :=
  mellin_differentiableAt_of_isBigO_rpow
    (((actual_counted_memLp c zero).locallyIntegrable (by norm_num)).locallyIntegrableOn _)
    (counted_top c zero) below (counted_origin c zero) positive

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Mellin
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
