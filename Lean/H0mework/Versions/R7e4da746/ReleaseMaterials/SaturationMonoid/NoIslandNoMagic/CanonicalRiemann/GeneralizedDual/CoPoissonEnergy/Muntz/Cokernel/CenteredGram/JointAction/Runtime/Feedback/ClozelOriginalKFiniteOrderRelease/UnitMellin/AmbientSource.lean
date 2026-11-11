import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.PowerSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKForcingGapAction.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.UnitMellin.AmbientSource
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszFinitePairing.CoPoisson.Ward
open scoped Topology InnerProductSpace
local notation "q"=>(1/4:ℝ)
local notation "barC"=>OriginalPrimitiveRankBalance.conjugateCoordinate
open private mean_constant from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKForcingGapAction.Source
/-- The actual full power column pays its own quarter mean, before mean-zero projection. -/
theorem actual_power_mean (c:BurnolCompletedMellinCoordinate):
    burnolQuarterMeanCoefficient (SingularCounting.powerL2 (barC c))=
      (q:ℂ)^(c.value-1)/c.value:=by
  let raw:=SingularCounting.powerRaw (barC c)
  have native:IntervalIntegrable raw volume (-q) q:=by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num:(-q)≤q)).mpr
    exact MemLp.integrable (by norm_num) (SingularCounting.power_memLp (barC c))
  have lowerNative:IntervalIntegrable raw volume (-q) 0:=by
    apply native.mono_set
    rw [uIcc_of_le (by norm_num:(-q)≤(0:ℝ)),uIcc_of_le (by norm_num:(-q)≤q)]
    exact Icc_subset_Icc le_rfl (by norm_num)
  have upperNative:IntervalIntegrable raw volume 0 q:=by
    apply native.mono_set
    rw [uIcc_of_le (by norm_num:(0:ℝ)≤q),uIcc_of_le (by norm_num:(-q)≤q)]
    exact Icc_subset_Icc (by norm_num) le_rfl
  have negative:(∫ x:ℝ in (-q)..0,raw x)=∫ x:ℝ in 0..q,raw x:=by
    have moved:=intervalIntegral.integral_comp_neg (f:=raw) (a:=0) (b:=q)
    simpa only [raw,SingularCounting.powerRaw,abs_neg,neg_zero] using moved.symm
  have positive:(∫ x:ℝ in 0..q,raw x)=(q:ℂ)^c.value/c.value:=by
    have profile:(∫ x:ℝ in 0..q,raw x)=∫ x:ℝ in 0..q,(x:ℂ)^(c.value-1):=by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [] with x inside
      rw [uIoc_of_le (by norm_num:(0:ℝ)≤q)] at inside
      simp only [raw,SingularCounting.powerRaw,OriginalPrimitiveRankBalance.conjugateCoordinate,star_star,
        abs_of_pos inside.1]
    have nonzero:c.value≠0:=by
      intro h
      have bound:=c.rightHalf
      rw [h] at bound
      norm_num at bound
    rw [profile,integral_cpow (Or.inl (by
      change -1<c.value.re-1
      linarith [c.rightHalf]))]
    simp only [sub_add_cancel,Complex.ofReal_zero,Complex.zero_cpow nonzero,sub_zero]
  rw [OriginalRieszSource.Constructor.mean_integral,
    integral_congr_ae (SingularCounting.power_coeFn (barC c))]
  change (2:ℂ)*(∫ x:ℝ in Icc (-q) q,raw x)=_
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le (by norm_num:(-q)≤q),
    ←intervalIntegral.integral_add_adjacent_intervals lowerNative upperNative,negative,positive]
  have power:(q:ℂ)^c.value=(q:ℂ)^(c.value-1)*(q:ℂ):=by
    calc
      _=(q:ℂ)^((c.value-1)+1):=by congr 1;ring
      _=_:=by rw [Complex.cpow_add _ _ (by norm_num:(q:ℂ)≠0),Complex.cpow_one]
  rw [power]
  norm_num
  ring


private theorem gap_price (v:BurnolL2):
    burnolAmbientGapCoefficient q v=burnolQuarterMeanCoefficient (burnolQuarterRestriction v):=by
  change ((‖intervalConstant q‖:ℂ)^2)⁻¹*inner ℂ (intervalConstant q) (burnolQuarterRestriction v)=
    inner ℂ (intervalConstant q) (burnolQuarterRestriction v)/((‖intervalConstant q‖^2:ℝ):ℂ)
  push_cast
  ring

private theorem quarter_positive_profile (c:BurnolCompletedMellinCoordinate) (v:BurnolL2) (a b:ℂ)
    (profile:burnolQuarterRestriction v=a • intervalConstant q+b • SingularCounting.powerL2 (barC c)):
    (v:ℝ→ℂ)=ᵐ[volume.restrict (Ioc 0 q)] fun x:ℝ=>a+b*(x:ℂ)^(c.value-1):=by
  have subset:Ioc (0:ℝ) q⊆symmetricInterval q:=by
    intro x inside
    exact ⟨by linarith [inside.1],inside.2⟩
  have restricted:=LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) v
  filter_upwards [ae_restrict_of_ae_restrict_of_subset subset restricted,
    ae_restrict_of_ae_restrict_of_subset subset (Lp.coeFn_add (a • intervalConstant q)
      (b • SingularCounting.powerL2 (barC c))),
    ae_restrict_of_ae_restrict_of_subset subset (Lp.coeFn_smul a (intervalConstant q)),
    ae_restrict_of_ae_restrict_of_subset subset (Lp.coeFn_smul b (SingularCounting.powerL2 (barC c))),
    ae_restrict_of_ae_restrict_of_subset subset (intervalConstant_coeFn q),
    ae_restrict_of_ae_restrict_of_subset subset (SingularCounting.power_coeFn (barC c)),
    ae_restrict_mem measurableSet_Ioc]
    with x read added first second constant power inside
  change burnolQuarterRestriction v x=v x at read
  rw [profile,added,Pi.add_apply,first,second,Pi.smul_apply,Pi.smul_apply,
    constant,power] at read
  simp only [SingularCounting.powerRaw,OriginalPrimitiveRankBalance.conjugateCoordinate,
    star_star,abs_of_pos inside.1,smul_eq_mul,mul_one] at read
  exact read.symm

private theorem head_power (s:ℂ) (positive:0<s.re):
    IntegrableOn (fun x:ℝ=>(x:ℂ)^(s-1)) (Ioc 0 q) ∧
      (∫ x:ℝ in Ioc 0 q,(x:ℂ)^(s-1))=(q:ℂ)^s/s:=by
  have bound:-1<(s-1).re:=by simp only [sub_re,one_re];linarith
  refine ⟨(intervalIntegral.intervalIntegrable_cpow' (a:=0) (b:=q) bound).1,?_⟩
  rw [←intervalIntegral.integral_of_le (by norm_num:(0:ℝ)≤q),integral_cpow (Or.inl bound),
    sub_add_cancel]
  have sn:s≠0:=by intro h;rw [h] at positive;norm_num at positive
  simp only [Complex.ofReal_zero,Complex.zero_cpow sn,sub_zero]

/-- The actual quarter power is exactly the difference between the ambient read and the whole Mellin integral. -/
theorem actual_ambient_full_difference (c w:BurnolCompletedMellinCoordinate) (v:BurnolL2) (a b value:ℂ)
    (between:w.value.re<c.value.re)
    (profile:burnolQuarterRestriction v=a • intervalConstant q+b • SingularCounting.powerL2 (barC c))
    (source:HasMellin (v:ℝ→ℂ) (1-w.value) value):
    burnolAmbientCompletedMellinEvaluator w v=value+
      b*(q:ℂ)^(c.value-w.value)*(1/(c.value*(1-w.value))-1/(c.value-w.value)):=by
  have first:=head_power (1-w.value) (by simp only [sub_re,one_re];linarith [w.belowOne])
  have second:=head_power (c.value-w.value) (by simpa only [sub_re] using sub_pos.mpr between)
  have exponent:(1-w.value)-1= -w.value:=by ring
  have quarter:=quarter_positive_profile c v a b profile
  have raw:(fun x:ℝ=>(x:ℂ)^(-w.value)*v x)=ᵐ[volume.restrict (Ioc 0 q)]
      fun x:ℝ=>a*(x:ℂ)^(-w.value)+b*(x:ℂ)^(c.value-w.value-1):=by
    filter_upwards [quarter,ae_restrict_mem measurableSet_Ioc] with x actual inside
    rw [actual]
    have power:(x:ℂ)^(-w.value)*(x:ℂ)^(c.value-1)=(x:ℂ)^(c.value-w.value-1):=by
      rw [←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr inside.1.ne')]
      congr 1
      ring
    calc
      _=a*(x:ℂ)^(-w.value)+b*((x:ℂ)^(-w.value)*(x:ℂ)^(c.value-1)):=by ring
      _=_:=by rw [power]
  have iFirst:IntegrableOn (fun x:ℝ=>(x:ℂ)^(-w.value)) (Ioc 0 q):=by
    simpa only [exponent] using first.1
  have iSecond:IntegrableOn (fun x:ℝ=>(x:ℂ)^(c.value-w.value-1)) (Ioc 0 q):=second.1
  have head:(∫ x:ℝ in Ioc 0 q,(x:ℂ)^(-w.value)*v x)=
      a*(q:ℂ)^(1-w.value)/(1-w.value)+b*(q:ℂ)^(c.value-w.value)/(c.value-w.value):=by
    rw [integral_congr_ae raw,integral_add (iFirst.const_mul a) (iSecond.const_mul b),
      integral_const_mul,integral_const_mul]
    rw [show (∫ x:ℝ in Ioc 0 q,(x:ℂ)^(-w.value))=(q:ℂ)^(1-w.value)/(1-w.value) by
      simpa only [exponent] using first.2,second.2]
    ring
  have convergent:IntegrableOn (fun x:ℝ=>(x:ℂ)^(-w.value)*v x) (Ioi 0):=by
    simpa only [MellinConvergent,exponent,smul_eq_mul] using source.1
  have full:value=a*(q:ℂ)^(1-w.value)/(1-w.value)+b*(q:ℂ)^(c.value-w.value)/(c.value-w.value)+
      burnolRadiusMellinTailEvaluator q (by norm_num) w.value w.rightHalf v:=by
    rw [burnolRadiusMellinTailEvaluator_eq_integral]
    rw [←source.2]
    change (∫ x:ℝ in Ioi 0,(x:ℂ)^((1-w.value)-1)*v x)=_
    rw [exponent,←Ioc_union_Ioi_eq_Ioi (by norm_num:(0:ℝ)≤q),
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        (convergent.mono_set Ioc_subset_Ioi_self)
        (convergent.mono_set (Ioi_subset_Ioi (by norm_num:(0:ℝ)≤q))),head]
  have mean:burnolAmbientGapCoefficient q v=a+b*((q:ℂ)^(c.value-1)/c.value):=by
    rw [gap_price,profile]
    have constant:burnolQuarterMeanCoefficient (intervalConstant q)=1:=mean_constant
    have power:=actual_power_mean c
    unfold burnolQuarterMeanCoefficient at constant power ⊢
    rw [inner_add_right,inner_smul_right,inner_smul_right]
    calc
      _=a*(inner ℂ (intervalConstant q) (intervalConstant q)/((‖intervalConstant q‖^2:ℝ):ℂ))+
        b*(inner ℂ (intervalConstant q) (SingularCounting.powerL2 (barC c))/((‖intervalConstant q‖^2:ℝ):ℂ)):=by ring
      _=_:=by rw [constant,power];ring
  have phase:(q:ℂ)^(1-w.value)*(q:ℂ)^(c.value-1)=(q:ℂ)^(c.value-w.value):=by
    rw [←Complex.cpow_add _ _ (by norm_num:(q:ℂ)≠0)]
    congr 1
    ring
  change burnolRadiusMellinGapMoment q w.value*burnolAmbientGapCoefficient q v+
    burnolRadiusMellinTailEvaluator q (by norm_num) w.value w.rightHalf v=_
  rw [mean,full]
  unfold burnolRadiusMellinGapMoment
  simp only [div_eq_mul_inv,mul_inv_rev] at phase ⊢
  linear_combination (1/c.value)*b/(1-w.value)*phase

end OriginalKFiniteOrderRelease.UnitMellin.AmbientSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
