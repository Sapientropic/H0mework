import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Schwartz

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.SchwartzMellin
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Consumer OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.DirectBound
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Schwartz
open scoped Topology ENNReal InnerProductSpace
open private log_mellin_convergent logSource_zero from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Source
local notation "q" => (1/4:ℝ)

private def envelope : ℝ→ℂ := (symmetricInterval (1:ℝ)).indicator (fun x:ℝ=>(x:ℂ))

private theorem envelope_memLp : MemLp envelope 2 volume := by
  have dominant:MemLp ((symmetricInterval (1:ℝ)).indicator (fun _:ℝ=>(1:ℂ))) 2 volume :=
    memLp_indicator_const (2:ℝ≥0∞) (measurableSet_symmetricInterval (1:ℝ)) (1:ℂ)
    (Or.inr (by simp [symmetricInterval]))
  apply dominant.mono (Complex.measurable_ofReal.indicator (measurableSet_symmetricInterval (1:ℝ))).aestronglyMeasurable
  filter_upwards with x
  change ‖envelope x‖≤‖(symmetricInterval (1:ℝ)).indicator (fun _:ℝ=>(1:ℂ)) x‖
  by_cases inside:x∈symmetricInterval (1:ℝ)
  · rw [envelope,indicator_of_mem inside,indicator_of_mem inside,Complex.norm_real,Real.norm_eq_abs,norm_one]
    exact abs_le.mpr inside
  · rw [envelope,indicator_of_notMem inside,indicator_of_notMem inside]

private theorem envelope_growth (x : ℝ) : ‖envelope x‖≤1*|x| := by
  by_cases inside:x∈symmetricInterval (1:ℝ)
  · rw [envelope,indicator_of_mem inside,Complex.norm_real,Real.norm_eq_abs,one_mul]
  · rw [envelope,indicator_of_notMem inside,norm_zero,one_mul]
    exact abs_nonneg x

private theorem envelope_mellin (j : ℕ) (w : ℂ) (strip : -1<w.re) :
    MellinConvergent (logSource envelope j) w := by
  apply log_mellin_convergent envelope envelope_memLp 1 1 envelope_growth
    (fun x outside=>?_) j w strip
  exact indicator_of_notMem (s:=symmetricInterval (1:ℝ))
    (fun inside=>not_le_of_gt outside (abs_le.mpr inside)) (fun y:ℝ=>(y:ℂ))

theorem actual_schwartz_log_mellin_limit (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) (j : ℕ) (w : ℂ) (strip : -1<w.re) :
    Tendsto (fun N:ℕ=>mellin (logSource (schwartzApprox c zero h nonnegative N) j) w) atTop
      (𝓝 (mellin (logSource (directRaw c h) j) w)) := by
  let bound:=4*(sourceLipschitz c zero h nonnegative:ℝ)
  let weighted:ℝ→ℂ:=fun x=>(x:ℂ)^(w-1) • logSource envelope j x
  have integrable:IntegrableOn weighted (Ioi 0):=envelope_mellin j w strip
  change Tendsto (fun N:ℕ=>∫x:ℝ in Ioi 0,(x:ℂ)^(w-1) • logSource (schwartzApprox c zero h nonnegative N) j x)
    atTop (𝓝 (∫x:ℝ in Ioi 0,(x:ℂ)^(w-1) • logSource (directRaw c h) j x))
  apply tendsto_integral_of_dominated_convergence (fun x=>bound*‖weighted x‖)
  · intro N
    have convergent : MellinConvergent (logSource (schwartzApprox c zero h nonnegative N) j) w := by
      apply log_mellin_convergent _ ((schwartzApprox c zero h nonnegative N).memLp 2 volume) 1 bound
        (actual_schwartz_linear_bound c zero h nonnegative N)
        (fun x outside=>actual_schwartz_outer_zero c zero h nonnegative N x (by linarith [radius_bound N])) j w strip
    exact convergent.aestronglyMeasurable
  · exact integrable.norm.const_mul bound
  · intro N
    filter_upwards with x
    by_cases inside:x∈symmetricInterval (1:ℝ)
    · change ‖(x:ℂ)^(w-1) • ((Real.log x)^j • schwartzApprox c zero h nonnegative N x)‖≤
        bound*‖(x:ℂ)^(w-1) • ((Real.log x)^j • envelope x)‖
      rw [envelope,indicator_of_mem inside]
      simp only [norm_smul,Complex.norm_real,Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (actual_schwartz_linear_bound c zero h nonnegative N x) (abs_nonneg _))
        (norm_nonneg _)).trans_eq (by ring)
    · simp only [logSource]
      rw [actual_schwartz_outer_zero c zero h nonnegative N x
        (by have large:=lt_of_not_ge (fun small=>inside (abs_le.mp small));linarith [radius_bound N])]
      simp only [smul_zero,norm_zero]
      exact mul_nonneg (by dsimp [bound];positivity) (norm_nonneg _)
  · filter_upwards with x
    exact ((actual_schwartz_tendsto c zero h nonnegative x).const_smul ((Real.log x)^j)).const_smul _

theorem actual_schwartz_mellin_limit (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) (w : ℂ) (strip : -1<w.re) :
    Tendsto (fun N:ℕ=>mellin (schwartzApprox c zero h nonnegative N) w) atTop
      (𝓝 (mellin (directRaw c h) w)) := by
  simpa only [logSource_zero] using actual_schwartz_log_mellin_limit c zero h nonnegative 0 w strip

private theorem unit_memLp : MemLp ((symmetricInterval (1:ℝ)).indicator (fun _:ℝ=>(1:ℂ))) 2 volume :=
  memLp_indicator_const 2 (measurableSet_symmetricInterval (1:ℝ)) (1:ℂ)
    (Or.inr (by simp [symmetricInterval]))

private def compactUnit : BurnolL2 := unit_memLp.toLp ((symmetricInterval (1:ℝ)).indicator (fun _:ℝ=>(1:ℂ)))

private theorem source_norm_bound (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) (N : ℕ) :
    ‖(schwartzApprox c zero h nonnegative N).toLp 2 volume-waveDifference c h‖≤
      ((7*(sourceLipschitz c zero h nonnegative:ℝ))*radius N)*‖compactUnit‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_sub ((schwartzApprox c zero h nonnegative N).toLp 2 volume) (waveDifference c h),
    (schwartzApprox c zero h nonnegative N).coeFn_toLp 2 volume,actual_direct_raw c h,
    unit_memLp.coeFn_toLp] with x difference approximation source unit
  change ‖((schwartzApprox c zero h nonnegative N).toLp 2 volume-waveDifference c h:BurnolL2) x‖≤_
  change compactUnit x=(symmetricInterval (1:ℝ)).indicator (fun _:ℝ=>(1:ℂ)) x at unit
  rw [difference,Pi.sub_apply,approximation,source,unit]
  by_cases inside:x∈symmetricInterval (1:ℝ)
  · rw [indicator_of_mem inside,norm_one,mul_one]
    exact actual_schwartz_approximation c zero h nonnegative N x
  · have outside:1 < |x|:=lt_of_not_ge (fun small=>inside (abs_le.mp small))
    rw [indicator_of_notMem inside,norm_zero,mul_zero,
      actual_schwartz_outer_zero c zero h nonnegative N x (by linarith [radius_bound N]),
      actual_direct_outer_zero c zero h nonnegative x (by linarith),sub_self,norm_zero]

/-- The same concrete Schwartz sources converge strongly to the original H_h in L². -/
theorem actual_schwartz_L2_limit (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) :
    Tendsto (fun N:ℕ=>(schwartzApprox c zero h nonnegative N).toLp 2 volume) atTop
      (𝓝 (waveDifference c h)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _=>norm_nonneg _) (fun N=>source_norm_bound c zero h nonnegative N)
  simpa only [mul_zero,zero_mul] using
    (radius_tendsto.const_mul (7*(sourceLipschitz c zero h nonnegative:ℝ))).mul_const ‖compactUnit‖

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.SchwartzMellin
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
