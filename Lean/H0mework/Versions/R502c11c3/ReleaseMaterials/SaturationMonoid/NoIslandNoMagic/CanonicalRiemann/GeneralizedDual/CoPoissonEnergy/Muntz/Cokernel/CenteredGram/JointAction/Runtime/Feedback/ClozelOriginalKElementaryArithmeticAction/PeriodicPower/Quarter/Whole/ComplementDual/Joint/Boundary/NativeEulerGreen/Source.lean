import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.SingularCounting
import H0mework.Versions.R7e4da746.Arithmetic.RieszEuler.Solve

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCanonicalNativeEulerGreen
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open scoped Topology InnerProductSpace ENNReal
attribute [local instance 1100] NormedSpace.complexToReal
local notation "q" => (1/4:ℝ)
local notation "μq" => volume.restrict (symmetricInterval q)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "E" => burnolQuarterZeroExtension
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "L" => burnolMeanZeroOneMinusSquare
local instance finiteQuarter : IsFiniteMeasure μq where
  measure_univ_lt_top := lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top q)

private theorem power_mul (s:ℂ) (x:ℝ) (positive:0<x) :
    (x:ℂ)*(x:ℂ)^(s-1)=(x:ℂ)^s := by
  calc
    _=(x:ℂ)^(s-1)*(x:ℂ)^(1:ℂ) := by rw [Complex.cpow_one,mul_comm]
    _=(x:ℂ)^((s-1)+1) := (Complex.cpow_add _ _
      (Complex.ofReal_ne_zero.mpr positive.ne')).symm
    _=_ := by congr 1; ring

def powerFlux (c:BurnolCompletedMellinCoordinate) (x:ℝ) : ℂ :=
  (x:ℂ)*SingularCounting.powerRaw c x

private theorem power_flux_positive (c:BurnolCompletedMellinCoordinate)
    (x:ℝ) (positive:0<x) : powerFlux c x=(x:ℂ)^(star c.value) := by
  rw [powerFlux,SingularCounting.powerRaw,abs_of_pos positive,power_mul _ x positive]

private theorem power_flux_negative (c:BurnolCompletedMellinCoordinate)
    (x:ℝ) (negative:x<0) : powerFlux c x=-((-x:ℝ):ℂ)^(star c.value) := by
  rw [powerFlux,SingularCounting.powerRaw,abs_of_neg negative]
  have source:=power_mul (star c.value) (-x) (by linarith)
  push_cast at source ⊢
  linear_combination -source

/-- The original power primitive has zero origin flux on both sides. -/
theorem power_flux_origin (c:BurnolCompletedMellinCoordinate) :
    Tendsto (powerFlux c) (𝓝 0) (𝓝 0) := by
  have positive : 0 < (star c.value).re := by
    simpa only [star_def,conj_re] using (lt_trans (by norm_num : (0:ℝ)<1/2) c.rightHalf)
  have value : (0:ℂ)^(star c.value)=0 := Complex.zero_cpow (by
    intro h
    rw [h] at positive
    norm_num at positive)
  have absolute : Tendsto (fun x:ℝ => ((|x|:ℝ):ℂ)^(star c.value)) (𝓝 0) (𝓝 0) := by
    simpa only [Function.comp_def,abs_zero,Complex.ofReal_zero,value] using
      ((Complex.continuous_ofReal_cpow_const positive).comp continuous_abs).tendsto (0:ℝ)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have absNorm : Tendsto (fun x:ℝ => ‖((|x|:ℝ):ℂ)^(star c.value)‖) (𝓝 0) (𝓝 0) := by
    simpa only [norm_zero] using absolute.norm
  apply absNorm.congr
  intro x
  by_cases hp:0<x
  · rw [power_flux_positive c x hp,abs_of_pos hp]
  · by_cases hn:x<0
    · rw [power_flux_negative c x hn,norm_neg,abs_of_neg hn]
    · have hx:x=0 := le_antisymm (le_of_not_gt hp) (le_of_not_gt hn)
      subst x
      simp only [powerFlux,Complex.ofReal_zero,zero_mul,abs_zero,value,norm_zero]

private theorem power_flux_derivative (c:BurnolCompletedMellinCoordinate)
    (x:ℝ) (nonzero:x≠0) :
    HasDerivAt (powerFlux c) (star c.value*SingularCounting.powerRaw c x) x := by
  have sne : star c.value≠0 := by
    intro h
    have positive : 0 < (star c.value).re := by
      simpa only [star_def,conj_re] using (lt_trans (by norm_num : (0:ℝ)<1/2) c.rightHalf)
    rw [h] at positive
    norm_num at positive
  rcases lt_or_gt_of_ne nonzero with hn|hp
  · have source := ((hasDerivAt_ofReal_cpow_const (neg_ne_zero.mpr nonzero) sne).scomp x
      (hasDerivAt_neg x)).neg
    have same : (fun y:ℝ => -((-y:ℝ):ℂ)^(star c.value)) =ᶠ[𝓝 x] powerFlux c := by
      filter_upwards [Iio_mem_nhds hn] with y hy
      exact (power_flux_negative c y hy).symm
    convert source.congr_of_eventuallyEq same.symm using 1 <;>
      first | rfl | simp [SingularCounting.powerRaw,abs_of_neg hn]
  · have source := hasDerivAt_ofReal_cpow_const nonzero sne
    have same : (fun y:ℝ => (y:ℂ)^(star c.value)) =ᶠ[𝓝 x] powerFlux c := by
      filter_upwards [Ioi_mem_nhds hp] with y hy
      exact (power_flux_positive c y hy).symm
    simpa only [SingularCounting.powerRaw,abs_of_pos hp] using source.congr_of_eventuallyEq same.symm

private theorem power_integrable (c:BurnolCompletedMellinCoordinate) :
    Integrable (SingularCounting.powerRaw c) μq :=
  (SingularCounting.power_memLp c).integrable (by norm_num)

/-- The actual power source pays its origin and both quarter endpoints. -/
theorem power_interval_green (c:BurnolCompletedMellinCoordinate) (test:SchwartzMap ℝ ℂ) :
    (∫x:ℝ in (-q)..q,
      powerFlux c x*deriv test x+star c.value*SingularCounting.powerRaw c x*test x)=
      (q:ℂ)*SingularCounting.powerRaw c q*(test q+test (-q)) := by
  let density:=fun x:ℝ => powerFlux c x*deriv test x+
    star c.value*SingularCounting.powerRaw c x*test x
  let flux:=fun x:ℝ => powerFlux c x*test x
  have first : Integrable (fun x:ℝ => powerFlux c x*deriv test x) μq := by
    apply (IntegrableOn.mul_continuousOn (power_integrable c) ((Complex.continuous_ofReal.mul (SchwartzMap.derivCLM ℂ ℂ test).continuous).continuousOn) isCompact_Icc).congr
    filter_upwards with x
    simp only [Pi.mul_apply,SchwartzMap.derivCLM_apply]
    unfold powerFlux
    ring
  have second : Integrable (fun x:ℝ => star c.value*SingularCounting.powerRaw c x*test x) μq :=
    IntegrableOn.mul_continuousOn ((power_integrable c).const_mul _) test.continuous.continuousOn isCompact_Icc
  have middle : IntervalIntegrable density volume (-q) q := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (-q:ℝ)≤q)]
    exact first.add second
  have left := middle.mono_set (show uIcc (-q) 0 ⊆ uIcc (-q) q by
    rw [uIcc_of_le (by norm_num : (-q:ℝ)≤0),uIcc_of_le (by norm_num : (-q:ℝ)≤q)]
    exact Icc_subset_Icc le_rfl (by norm_num))
  have right := middle.mono_set (show uIcc 0 q ⊆ uIcc (-q) q by
    rw [uIcc_of_le (by norm_num : (0:ℝ)≤q),uIcc_of_le (by norm_num : (-q:ℝ)≤q)]
    exact Icc_subset_Icc (by norm_num) le_rfl)
  have hd (x:ℝ) (nonzero:x≠0) : HasDerivAt flux (density x) x := by
    simpa only [flux,density,add_comm] using! (power_flux_derivative c x nonzero).mul (test.hasDerivAt x)
  have origin : Tendsto flux (𝓝 0) (𝓝 0) := by
    simpa only [zero_mul] using (power_flux_origin c).mul (test.continuous.tendsto 0)
  have negativeFTC:=intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    (by norm_num : (-q:ℝ)<0) (fun x hx=>hd x (by linarith [hx.2])) left
    (((hd (-q) (by norm_num)).continuousAt.tendsto).mono_left nhdsWithin_le_nhds)
    (origin.mono_left nhdsWithin_le_nhds)
  have positiveFTC:=intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    (by norm_num : (0:ℝ)<q) (fun x hx=>hd x (by linarith [hx.1])) right
    (origin.mono_left nhdsWithin_le_nhds)
    (((hd q (by norm_num)).continuousAt.tendsto).mono_left nhdsWithin_le_nhds)
  change (∫x:ℝ in (-q)..q,density x)=_
  rw [←intervalIntegral.integral_add_adjacent_intervals left right,negativeFTC,positiveFTC]
  dsimp only [flux,powerFlux,SingularCounting.powerRaw]
  norm_num
  ring


private theorem power_test_integrable (c:BurnolCompletedMellinCoordinate) (test:SchwartzMap ℝ ℂ) :
    Integrable (fun x:ℝ => SingularCounting.powerRaw c x*test x) μq :=
  IntegrableOn.mul_continuousOn (power_integrable c) test.continuous.continuousOn isCompact_Icc

/-- The same primitive fixes the actual quarter mean; centering retains its flux. -/
theorem power_mean (c:BurnolCompletedMellinCoordinate) :
    star c.value*burnolQuarterMeanCoefficient (SingularCounting.powerL2 c)=
      SingularCounting.powerRaw c q := by
  let test:=Euler.WindowTest.wave 0
  have wave (x:ℝ) (inside:x∈symmetricInterval q) : test x=1 := by
    rw [Euler.WindowTest.wave_eq 0 inside]
    simp [Constructor.phase]
  have slope (x:ℝ) (inside:x∈symmetricInterval q) : deriv test x=0 := by
    rw [Euler.WindowTest.wave_deriv 0 inside]
    simp
  have source:=power_interval_green c test
  have read : (∫x:ℝ in (-q)..q,
      powerFlux c x*deriv test x+star c.value*SingularCounting.powerRaw c x*test x)=
      star c.value*(∫x:ℝ in (-q)..q,SingularCounting.powerRaw c x) := by
    rw [←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_ae
    filter_upwards with x hx
    have inside:x∈symmetricInterval q := Ioc_subset_Icc_self (by
      simpa only [uIoc_of_le (by norm_num : (-q:ℝ)≤q)] using hx)
    rw [wave x inside,slope x inside]
    ring
  rw [read,wave q (by norm_num [symmetricInterval]),wave (-q) (by norm_num [symmetricInterval])] at source
  rw [Constructor.mean_integral,integral_congr_ae (SingularCounting.power_coeFn c)]
  rw [intervalIntegral.integral_of_le (by norm_num : (-q:ℝ)≤q),←integral_Icc_eq_integral_Ioc] at source
  change star c.value*(2*∫x:ℝ,SingularCounting.powerRaw c x ∂μq)=_
  norm_num at source
  simp only [symmetricInterval,starRingEnd_apply] at source ⊢
  linear_combination 2*source

/-- The canonical power is consumed as its true distribution, with both actual endpoints. -/
theorem power_euler (c:BurnolCompletedMellinCoordinate) :
    GapEuler.euler (E (SingularCounting.powerL2 c):TemperedDistribution ℝ ℂ)=
      (star c.value-1/2) • (E (SingularCounting.powerL2 c):TemperedDistribution ℝ ℂ)-
        ((q:ℂ)*SingularCounting.powerRaw c q) •
          (TemperedDistribution.delta q+TemperedDistribution.delta (-q)) := by
  ext test
  simp only [sub_apply,add_apply,smul_apply,smul_eq_mul,TemperedDistribution.delta_apply]
  rw [Translator.ForcingCutoff.euler_zeroExtension_pairing _ _ (SingularCounting.power_coeFn c),
    Translator.ForcingCutoff.zeroExtension_pairing _ _ (SingularCounting.power_coeFn c)]
  have source:=power_interval_green c test
  rw [intervalIntegral.integral_of_le (by norm_num : (-q:ℝ)≤q)] at source
  have first:Integrable (fun x:ℝ => powerFlux c x*deriv test x) μq := by
    apply (IntegrableOn.mul_continuousOn (power_integrable c)
      ((Complex.continuous_ofReal.mul (SchwartzMap.derivCLM ℂ ℂ test).continuous).continuousOn)
      isCompact_Icc).congr
    filter_upwards with x
    simp only [Pi.mul_apply,SchwartzMap.derivCLM_apply]
    unfold powerFlux
    ring
  have second:Integrable (fun x:ℝ => star c.value*SingularCounting.powerRaw c x*test x) μq := by
    simpa only [mul_assoc] using (power_test_integrable c test).const_mul (star c.value)
  rw [←integral_Icc_eq_integral_Ioc] at source
  simp only [symmetricInterval] at first second
  rw [integral_add first second] at source
  have scaled:(∫x:ℝ,star c.value*SingularCounting.powerRaw c x*test x ∂μq)=
      star c.value*(∫x:ℝ,SingularCounting.powerRaw c x*test x ∂μq) := by
    simpa only [mul_assoc] using integral_const_mul (star c.value)
      (fun x:ℝ => SingularCounting.powerRaw c x*test x) (μ:=μq)
  simp only [symmetricInterval] at scaled
  rw [scaled] at source
  rw [←integral_Icc_eq_integral_Ioc,←integral_Icc_eq_integral_Ioc]
  change -(∫x:ℝ,powerFlux c x*deriv test x ∂μq)-
    (1/2:ℂ)*(∫x:ℝ,SingularCounting.powerRaw c x*test x ∂μq)=_
  simp only [symmetricInterval] at source ⊢
  linear_combination -source

end OriginalCanonicalNativeEulerGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
