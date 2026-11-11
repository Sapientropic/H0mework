import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Forward
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.ReciprocalMean.Source

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Source
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Consumer
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.DirectBound OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.ReciprocalMean.Source
open scoped Topology ENNReal InnerProductSpace
open private companion_whole_read companion_whole_bound from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.ReciprocalMean.Source
open private cutoff cutoffSet cutoff_norm cutoff_tendsto cutoff_measurable cutoff_measurableSet from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Forward
open private mellin_source_ae from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.ResolventSource
local notation "q" => (1/4:ℝ)

def logSource (raw : ℝ→ℂ) (j : ℕ) (x : ℝ) : ℂ := (Real.log x)^j • raw x

private theorem logSource_zero (raw : ℝ→ℂ) : logSource raw 0=raw := by
  funext x
  simp only [logSource,pow_zero,one_smul]

private theorem origin_bound (raw : ℝ→ℂ) (B : ℝ) (growth : ∀x,‖raw x‖≤B*|x|) :
    raw=O[𝓝[>] 0](fun x:ℝ=>x^(1:ℝ)) := by
  apply Asymptotics.IsBigO.of_bound B
  filter_upwards with x
  simpa only [Real.rpow_one,Real.norm_eq_abs] using growth x

private theorem log_origin_bound (raw : ℝ→ℂ) (B : ℝ) (growth : ∀x,‖raw x‖≤B*|x|)
    (j : ℕ) (b : ℝ) (above : -1<b) :
    logSource raw j=O[𝓝[>] 0](fun x:ℝ=>x^(-b)) := by
  have logarithm:(fun x:ℝ=>(Real.log x)^j)=O[𝓝[>] 0](fun x:ℝ=>x^(-b-1)) := by
    apply Asymptotics.IsBigO.of_norm_left
    simpa only [Real.norm_eq_abs,abs_pow,Real.rpow_natCast] using
      (isLittleO_abs_log_rpow_rpow_nhdsGT_zero (j:ℝ) (by linarith : -b-1<0)).isBigO
  have product:=logarithm.smul (origin_bound raw B growth)
  apply product.congr' (EventuallyEq.refl _ _)
  filter_upwards [self_mem_nhdsWithin] with x positive
  change (x:ℝ)^(-b-1)*x^(1:ℝ)=x^(-b)
  rw [←Real.rpow_add positive]
  congr 1
  ring

private theorem log_top_bound (raw : ℝ→ℂ) (radius : ℝ) (outside : ∀x,radius < |x| → raw x=0)
    (j : ℕ) (a : ℝ) : logSource raw j=O[atTop](fun x:ℝ=>x^(-a)) := by
  apply Asymptotics.IsBigO.of_bound 0
  filter_upwards [eventually_ge_atTop (max radius 0+1)] with x large
  have beyond:radius < |x| := by
    rw [abs_of_nonneg (by linarith [le_max_right radius 0])]
    linarith [le_max_left radius 0]
  simp only [logSource,outside x beyond,smul_zero,norm_zero,zero_mul,le_refl]

private theorem log_mellin_convergent (raw : ℝ→ℂ) (rawMem : MemLp raw 2 volume)
    (radius B : ℝ) (growth : ∀x,‖raw x‖≤B*|x|) (outside : ∀x,radius < |x| → raw x=0)
    (j : ℕ) (w : ℂ) (strip : -1<w.re) : MellinConvergent (logSource raw j) w := by
  have logarithm : ContinuousOn (fun x:ℝ=>(Real.log x)^j) (Ioi 0) := by
    intro x hx
    exact ((Real.continuousAt_log hx.ne').pow j).continuousWithinAt
  have localSource : LocallyIntegrableOn (logSource raw j) (Ioi 0) :=
    LocallyIntegrableOn.continuousOn_smul isOpen_Ioi.isLocallyClosed
      ((rawMem.locallyIntegrable (by norm_num)).locallyIntegrableOn _) logarithm
  exact mellinConvergent_of_isBigO_rpow localSource (log_top_bound raw radius outside j (w.re+1))
    (by linarith) (log_origin_bound raw B growth j ((w.re-1)/2) (by linarith)) (by linarith)

/-- Every logarithmic Mellin source of the actual difference is integrable on the full free half-plane. -/
theorem actual_difference_log_mellin (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) (j : ℕ) (w : ℂ) (strip : -1<w.re) :
    MellinConvergent (logSource (directRaw c h) j) w := by
  obtain ⟨B,_,growth⟩:=actual_direct_bound c zero h nonnegative
  exact log_mellin_convergent _ ((Lp.memLp (waveDifference c h)).ae_eq (actual_direct_raw c h))
    q B growth (fun x outside=>actual_direct_outer_zero c zero h nonnegative x outside.le) j w strip

theorem actual_difference_mellin (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) (w : ℂ) (strip : -1<w.re) : MellinConvergent (directRaw c h) w := by
  simpa only [logSource_zero] using actual_difference_log_mellin c zero h nonnegative 0 w strip

theorem actual_companion_log_mellin (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (j : ℕ) (w : ℂ) (strip : -1<w.re) :
    MellinConvergent (logSource (companionWholeRaw c) j) w := by
  obtain ⟨B,_,growth⟩:=companion_whole_bound c zero
  apply log_mellin_convergent _ ((Lp.memLp (companion c)).ae_eq (companion_whole_read c)) q B growth
    (fun x outside=>?_) j w strip
  change (symmetricInterval q).indicator (companionRaw c) x=0
  exact indicator_of_notMem (s:=symmetricInterval q)
    (fun inside=>not_le_of_gt outside (abs_le.mpr inside)) (companionRaw c)

theorem actual_companion_mellin (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (w : ℂ) (strip : -1<w.re) :
    HasMellin (companion c:ℝ→ℂ) w (mellin (companionWholeRaw c) w) := by
  have source:HasMellin (companionWholeRaw c) w (mellin (companionWholeRaw c) w) :=
    ⟨by simpa only [logSource_zero] using actual_companion_log_mellin c zero 0 w strip,rfl⟩
  exact mellin_source_ae _ _ _ _ (ae_restrict_of_ae (companion_whole_read c)) source

def annularCutoff (c : BurnolCompletedMellinCoordinate) (h : ℝ) (N : ℕ) : ℝ→ℂ :=
  cutoff (directRaw c h) N

theorem actual_log_cutoff_limit (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) (j : ℕ) (w : ℂ) (strip : -1<w.re) :
    Tendsto (fun N:ℕ=>mellin (logSource (annularCutoff c h N) j) w) atTop
      (𝓝 (mellin (logSource (directRaw c h) j) w)) := by
  let weighted:ℝ→ℂ:=fun x=>(x:ℂ)^(w-1) • logSource (directRaw c h) j x
  have source:IntegrableOn weighted (Ioi 0):=actual_difference_log_mellin c zero h nonnegative j w strip
  change Tendsto (fun N:ℕ=>∫x:ℝ in Ioi 0,(x:ℂ)^(w-1) • logSource (annularCutoff c h N) j x)
    atTop (𝓝 (∫x:ℝ in Ioi 0,weighted x))
  apply tendsto_integral_of_dominated_convergence (fun x=>‖weighted x‖)
  · intro N
    have identity : (fun x:ℝ=>(x:ℂ)^(w-1) • logSource (annularCutoff c h N) j x)=
        (cutoffSet N).indicator weighted := by
      funext x
      by_cases inside:x∈cutoffSet N
      · rw [indicator_of_mem inside]
        change (x:ℂ)^(w-1) • ((Real.log x)^j • (cutoffSet N).indicator (directRaw c h) x)=_
        rw [indicator_of_mem inside]
        rfl
      · rw [indicator_of_notMem inside]
        change (x:ℂ)^(w-1) • ((Real.log x)^j • (cutoffSet N).indicator (directRaw c h) x)=0
        rw [indicator_of_notMem inside,smul_zero,smul_zero]
    rw [identity]
    exact source.aestronglyMeasurable.indicator (cutoff_measurableSet N)
  · exact source.norm
  · intro N
    filter_upwards with x
    simp only [weighted,logSource,norm_smul]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (cutoff_norm (directRaw c h) N x) (norm_nonneg _)) (norm_nonneg _)
  · filter_upwards with x
    exact ((cutoff_tendsto (directRaw c h) (actual_direct_origin c h) x).const_smul ((Real.log x)^j)).const_smul _

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Source
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
