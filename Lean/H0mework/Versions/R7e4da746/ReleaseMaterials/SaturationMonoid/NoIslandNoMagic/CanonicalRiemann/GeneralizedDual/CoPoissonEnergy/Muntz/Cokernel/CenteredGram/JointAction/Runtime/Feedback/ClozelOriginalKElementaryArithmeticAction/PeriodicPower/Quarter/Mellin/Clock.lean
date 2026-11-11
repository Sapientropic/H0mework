import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Source

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Clock
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Consumer
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.DirectBound OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.ReciprocalMean.Source
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Source
open scoped Topology ENNReal InnerProductSpace
open private unitWeight driving_continuous from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.ReciprocalMean.Source
open private origin_bound log_top_bound logSource_zero from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Source
open private bochner_scaled_mellin mellin_source_ae from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.ResolventSource

def clockWeight (c : BurnolCompletedMellinCoordinate) (w : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (((1-star c.value-w)/2)*(t:ℂ))

def clockFactor (c : BurnolCompletedMellinCoordinate) (h : ℝ) (w : ℂ) : ℂ :=
  (Complex.exp ((star c.value-1/2)*(h:ℂ))/2)*∫t:ℝ in Ioc 0 (2*h),clockWeight c w t

private theorem weight_read (c : BurnolCompletedMellinCoordinate) (w : ℂ) (t : ℝ) :
    unitWeight c t*(Real.exp (t/2):ℂ)^(-w)=clockWeight c w t := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)),
    ←Complex.ofReal_log (Real.exp_pos _).le,Real.log_exp]
  unfold unitWeight clockWeight
  rw [←Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem integral_mellin (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (w : ℂ) (strip : -1<w.re) :
    HasMellin ((∫t:ℝ in Ioc 0 (2*h),drivingOrbit c t):BurnolL2) w
      ((∫t:ℝ in Ioc 0 (2*h),clockWeight c w t)*mellin (companionWholeRaw c) w) := by
  let clock:=Ioc (0:ℝ) (2*h)
  let family:ℝ→BurnolL2:=clock.indicator (drivingOrbit c)
  let weight:ℝ→ℂ:=clock.indicator (unitWeight c)
  let scale:ℝ→ℝ:=fun t=>Real.exp (t/2)
  have familyIntegrable : Integrable family :=
    (integrable_indicator_iff measurableSet_Ioc).mpr
      (((driving_continuous c).integrableOn_Icc).mono_set Ioc_subset_Icc_self)
  have weightMeasurable : Measurable weight :=
    (show Continuous (unitWeight c) by unfold unitWeight;fun_prop).measurable.indicator measurableSet_Ioc
  have reads : ∀ᵐt:ℝ∂volume.restrict (Ioi 0), (family t:ℝ→ℂ)=ᵐ[volume]
      fun x:ℝ=>weight t*(companion c:ℝ→ℂ) (scale t*x) := by
    filter_upwards with t
    by_cases inside:t∈clock
    · dsimp only [family,weight]
      rw [indicator_of_mem inside,indicator_of_mem inside]
      filter_upwards [Lp.coeFn_smul (positiveMellinQuarterRightResolventWeight (star c.value/2) t)
        (burnolMultiplicativeDilation (t/2) (companion c)),
        burnolMultiplicativeDilation_coeFn (t/2) (companion c)] with x scalar dilation
      change (positiveMellinQuarterRightResolventWeight (star c.value/2) t •
        burnolMultiplicativeDilation (t/2) (companion c):BurnolL2) x=_
      rw [scalar,Pi.smul_apply,smul_eq_mul,dilation]
      have price : positiveMellinQuarterRightResolventWeight (star c.value/2) t *
          (Real.exp ((t/2)/2):ℂ)=unitWeight c t := by
        unfold positiveMellinQuarterRightResolventWeight unitWeight
        rw [Complex.ofReal_exp,←Complex.exp_add]
        congr 1
        push_cast
        ring
      dsimp only [scale]
      rw [burnolL2RawNormalizedDilation,←mul_assoc,price]
    · dsimp only [family,weight]
      rw [indicator_of_notMem inside,indicator_of_notMem inside]
      filter_upwards [Lp.coeFn_zero ℂ 2 volume] with x source
      simp only [source,zero_mul,Pi.zero_apply]
  have clockRead : (fun t:ℝ=>weight t*(scale t:ℂ)^(-w))=clock.indicator (clockWeight c w) := by
    funext t
    by_cases inside:t∈clock
    · dsimp only [weight,scale]
      rw [indicator_of_mem inside,indicator_of_mem inside,weight_read]
    · dsimp only [weight]
      rw [indicator_of_notMem inside,indicator_of_notMem inside,zero_mul]
  have clockIntegrable : Integrable (clock.indicator (clockWeight c w)) :=
    (integrable_indicator_iff measurableSet_Ioc).mpr
      (((show Continuous (clockWeight c w) by unfold clockWeight;fun_prop).integrableOn_Icc).mono_set Ioc_subset_Icc_self)
  have budget : IntegrableOn (fun t:ℝ=>‖weight t*(scale t:ℂ)^(-w)‖) (Ioi 0) := by
    rw [show (fun t:ℝ=>‖weight t*(scale t:ℂ)^(-w)‖)=(fun t=>‖clock.indicator (clockWeight c w) t‖) from congrArg (fun f:ℝ→ℂ=>fun t=>‖f t‖) clockRead]
    exact clockIntegrable.norm.integrableOn
  have native:=bochner_scaled_mellin (companion c) w (mellin (companionWholeRaw c) w)
    family familyIntegrable.integrableOn weight scale weightMeasurable (by dsimp [scale];fun_prop)
    (fun t _=>Real.exp_pos (t/2)) reads (actual_companion_mellin c zero w strip) budget
  have sourceIntegral : (∫t:ℝ in Ioi 0,family t) = ∫t:ℝ in clock,drivingOrbit c t := by
    rw [show family=clock.indicator (drivingOrbit c) from rfl,setIntegral_indicator measurableSet_Ioc]
    rw [inter_eq_right.mpr (show clock⊆Ioi (0:ℝ) from fun _ ht=>ht.1)]
  have weightIntegral : (∫t:ℝ in Ioi 0,weight t*(scale t:ℂ)^(-w)) = ∫t:ℝ in clock,clockWeight c w t := by
    rw [clockRead,setIntegral_indicator measurableSet_Ioc]
    rw [inter_eq_right.mpr (show clock⊆Ioi (0:ℝ) from fun _ ht=>ht.1)]
  rw [sourceIntegral,weightIntegral] at native
  exact native

/-- Free Mellin data are generated by the actual finite source integral, including the resonant point. -/
theorem actual_wave_mellin (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) (w : ℂ) (strip : -1<w.re) :
    HasMellin (waveDifference c h:ℝ→ℂ) w (clockFactor c h w*mellin (companionWholeRaw c) w) := by
  let value:BurnolL2:=∫t:ℝ in Ioc 0 (2*h),drivingOrbit c t
  let scalar:ℂ:=Complex.exp ((star c.value-1/2)*(h:ℂ))/2
  have native:=integral_mellin c zero h w strip
  have scaled:=hasMellin_const_smul native.1 scalar
  rw [native.2,smul_eq_mul] at scaled
  have transported : HasMellin ((scalar • value:BurnolL2):ℝ→ℂ) w
      (scalar*((∫t:ℝ in Ioc 0 (2*h),clockWeight c w t)*mellin (companionWholeRaw c) w)) :=
    mellin_source_ae _ _ _ _ (ae_restrict_of_ae (s:=Ioi 0) (Lp.coeFn_smul scalar value)) scaled
  have same:waveDifference c h=scalar • value:=actual_wave_integral c zero h nonnegative
  rw [←same] at transported
  simpa only [clockFactor,scalar,mul_assoc] using transported

theorem actual_direct_mellin (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) (w : ℂ) (strip : -1<w.re) :
    HasMellin (directRaw c h) w (clockFactor c h w*mellin (companionWholeRaw c) w) :=
  mellin_source_ae _ _ _ _ (ae_restrict_of_ae (s:=Ioi 0) (actual_direct_raw c h).symm)
    (actual_wave_mellin c zero h nonnegative w strip)

theorem actual_nonresonant_factor (c : BurnolCompletedMellinCoordinate) (h : ℝ) (nonnegative : 0≤h)
    (w : ℂ) (nonresonant : w≠1-star c.value) :
    clockFactor c h w=(Complex.exp ((1/2-w)*(h:ℂ))-
      Complex.exp ((star c.value-1/2)*(h:ℂ)))/(1-star c.value-w) := by
  have nonzero:(1-star c.value-w:ℂ)≠0 := by
    intro equality
    exact nonresonant (sub_eq_zero.mp equality).symm
  have integral:(∫t:ℝ in Ioc 0 (2*h),clockWeight c w t)=
      (Complex.exp ((1-star c.value-w)*(h:ℂ))-1)/((1-star c.value-w)/2) := by
    rw [←intervalIntegral.integral_of_le (by linarith : (0:ℝ)≤2*h)]
    unfold clockWeight
    rw [integral_exp_mul_complex (div_ne_zero nonzero (by norm_num : (2:ℂ)≠0))]
    simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero,Complex.ofReal_mul,Complex.ofReal_ofNat]
    congr 2
    ring
  have product:Complex.exp ((star c.value-1/2)*(h:ℂ))*Complex.exp ((1-star c.value-w)*(h:ℂ))=
      Complex.exp ((1/2-w)*(h:ℂ)) := by
    rw [←Complex.exp_add]
    congr 1
    ring
  rw [clockFactor,integral]
  calc
    _=(Complex.exp ((star c.value-1/2)*(h:ℂ))*(Complex.exp ((1-star c.value-w)*(h:ℂ))-1))/(1-star c.value-w) := by
      field_simp [nonzero]
    _=_ := by rw [mul_sub,product,mul_one]

theorem actual_nonresonant_mellin (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) (w : ℂ) (strip : -1<w.re) (nonresonant : w≠1-star c.value) :
    HasMellin (directRaw c h) w
      (((Complex.exp ((1/2-w)*(h:ℂ))-Complex.exp ((star c.value-1/2)*(h:ℂ)))/(1-star c.value-w))*
        mellin (companionWholeRaw c) w) := by
  have source:=actual_direct_mellin c zero h nonnegative w strip
  rw [actual_nonresonant_factor c h nonnegative w nonresonant] at source
  exact source

theorem actual_resonant_factor (c : BurnolCompletedMellinCoordinate) (h : ℝ) (nonnegative : 0≤h) :
    clockFactor c h (1-star c.value)=(h:ℂ)*Complex.exp ((star c.value-1/2)*(h:ℂ)) := by
  have weight:clockWeight c (1-star c.value)=(fun _:ℝ=>(1:ℂ)) := by
    funext t
    simp only [clockWeight,sub_self,zero_div,zero_mul,Complex.exp_zero]
  rw [clockFactor,weight,←intervalIntegral.integral_of_le (by linarith : (0:ℝ)≤2*h),intervalIntegral.integral_const]
  simp only [sub_zero,Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_ofNat,mul_one]
  ring

theorem actual_resonant_mellin (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) :
    HasMellin (directRaw c h) (1-star c.value)
      ((h:ℂ)*Complex.exp ((star c.value-1/2)*(h:ℂ))*mellin (companionWholeRaw c) (1-star c.value)) := by
  have strip : -1<(1-star c.value).re := by simp only [sub_re,one_re,star_def,conj_re];linarith [c.belowOne]
  have native:=actual_direct_mellin c zero h nonnegative (1-star c.value) strip
  rw [actual_resonant_factor c h nonnegative] at native
  exact native

theorem actual_direct_mellin_continuous (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) (w : ℂ) (strip : -1<w.re) : ContinuousAt (mellin (directRaw c h)) w := by
  obtain ⟨B,_,growth⟩:=actual_direct_bound c zero h nonnegative
  have localSource : LocallyIntegrableOn (directRaw c h) (Ioi 0) :=
    (((Lp.memLp (waveDifference c h)).ae_eq (actual_direct_raw c h)).locallyIntegrable (by norm_num)).locallyIntegrableOn _
  have top:=log_top_bound (directRaw c h) (1/4) (fun x outside=>
    actual_direct_outer_zero c zero h nonnegative x outside.le) 0 (w.re+1)
  rw [logSource_zero] at top
  have bottom:(directRaw c h)=O[𝓝[>] 0](fun x:ℝ=>x^(-(-1:ℝ))) := by
    simpa only [neg_neg] using origin_bound (directRaw c h) B growth
  exact (mellin_differentiableAt_of_isBigO_rpow localSource top (by linarith) bottom strip).continuousAt

/-- The apparent pole is evaluated by the genuine source Mellin limit, with its full resonant fee. -/
theorem actual_resonant_limit (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) :
    Tendsto (fun w:ℂ=>((Complex.exp ((1/2-w)*(h:ℂ))-Complex.exp ((star c.value-1/2)*(h:ℂ)))/
      (1-star c.value-w))*mellin (companionWholeRaw c) w) (𝓝[≠] (1-star c.value))
      (𝓝 ((h:ℂ)*Complex.exp ((star c.value-1/2)*(h:ℂ))*mellin (companionWholeRaw c) (1-star c.value))) := by
  have strip : -1<(1-star c.value).re := by simp only [sub_re,one_re,star_def,conj_re];linarith [c.belowOne]
  have limit:Tendsto (mellin (directRaw c h)) (𝓝[≠] (1-star c.value))
      (𝓝 (mellin (directRaw c h) (1-star c.value))) :=
    (actual_direct_mellin_continuous c zero h nonnegative (1-star c.value) strip).tendsto.mono_left
      nhdsWithin_le_nhds
  rw [(actual_resonant_mellin c zero h nonnegative).2] at limit
  apply limit.congr'
  have nearby:∀ᶠw:ℂ in 𝓝 (1-star c.value), -1<w.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds strip
  filter_upwards [nearby.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with w inside nonresonant
  exact (actual_nonresonant_mellin c zero h nonnegative w inside nonresonant).2

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Clock
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
