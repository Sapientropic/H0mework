import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.CompactPaired
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.CompactC1
import Mathlib.MeasureTheory.Integral.Asymptotics

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.CountedSchur.LogWeight
open Complex Filter MeasureTheory Set Asymptotics
open scoped Topology
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.CompactForward
open private sqrt_bound from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ReciprocalTail

def raw (a:BurnolCompletedMellinCoordinate) (j:ℕ) (x:ℝ) : ℂ :=
  SingularCounting.powerRaw a x*(Real.log |x|:ℂ)^j

def reciprocalWeight (a:BurnolCompletedMellinCoordinate) (j:ℕ) : ℝ→ℂ := weight (raw a j)

def weightSlope (a:BurnolCompletedMellinCoordinate) (j:ℕ) (u:ℝ) : ℂ :=
  (u:ℂ)^(-star a.value-1)*
    ((-star a.value)*(-(Real.log u:ℂ))^j-(j:ℂ)*(-(Real.log u:ℂ))^(j-1))

/-- The actual inverse-coordinate density fixes both the logarithmic sign and its full scale factor. -/
theorem reciprocal_actual (a:BurnolCompletedMellinCoordinate) (j:ℕ) (u:ℝ) (positive:0<u) :
    reciprocalWeight a j u=(u:ℂ)^(-star a.value)*(-(Real.log u:ℂ))^j := by
  have power:((u⁻¹:ℝ):ℂ)^(star a.value-1)/(u:ℂ)=(u:ℂ)^(-star a.value) := by
    rw [Complex.ofReal_inv,Complex.inv_cpow_ofReal_nonneg positive.le,div_eq_mul_inv,
      ←Complex.cpow_neg,show (u:ℂ)⁻¹=(u:ℂ)^(-1:ℂ) by rw [Complex.cpow_neg_one],
      ←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr positive.ne')]
    congr 1
    ring
  unfold reciprocalWeight weight raw SingularCounting.powerRaw
  rw [abs_of_pos (inv_pos.mpr positive),Real.log_inv,Complex.ofReal_neg]
  calc
    _=(((u⁻¹:ℝ):ℂ)^(star a.value-1)/(u:ℂ))*(-(Real.log u:ℂ))^j := by ring
    _=_ := by rw [power]

theorem weight_hasDerivAt (a:BurnolCompletedMellinCoordinate) (j:ℕ) (u:ℝ) (positive:0<u) :
    HasDerivAt (reciprocalWeight a j) (weightSlope a j u) u := by
  have exponentNonzero:-star a.value≠0 := by
    intro same
    have realPart:=congrArg Complex.re same
    simp only [neg_re,star_def,conj_re,zero_re] at realPart
    linarith [a.rightHalf]
  have power:=hasDerivAt_ofReal_cpow_const positive.ne' exponentNonzero
  have logarithm:HasDerivAt (fun t:ℝ=> -(Real.log t:ℂ)) (-(u:ℂ)⁻¹) u := by
    simpa only [Pi.neg_apply,Complex.ofReal_neg,Complex.ofReal_inv] using ((Real.hasDerivAt_log positive.ne').neg).ofReal_comp
  have amplitude:(u:ℂ)^(-star a.value)*(u:ℂ)⁻¹=(u:ℂ)^(-star a.value-1) := by
    have native:=Complex.cpow_sub (-star a.value) 1 (Complex.ofReal_ne_zero.mpr positive.ne')
    simpa only [Complex.cpow_one,div_eq_mul_inv] using native.symm
  have source:=power.mul (logarithm.pow j)
  have derivative: (-star a.value*(u:ℂ)^(-star a.value-1))*(-(Real.log u:ℂ))^j+
      (u:ℂ)^(-star a.value)*((j:ℂ)*(-(Real.log u:ℂ))^(j-1)*(-(u:ℂ)⁻¹))=weightSlope a j u := by
    calc
      _=(u:ℂ)^(-star a.value-1)*((-star a.value)*(-(Real.log u:ℂ))^j)-
        (j:ℂ)*(-(Real.log u:ℂ))^(j-1)*((u:ℂ)^(-star a.value)*(u:ℂ)⁻¹) := by ring
      _=_ := by rw [amplitude];unfold weightSlope;ring
  simp only [Pi.pow_apply] at source
  rw [derivative] at source
  apply source.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds positive] with t atPositive
  exact reciprocal_actual a j t atPositive

private theorem slope_continuous (a:BurnolCompletedMellinCoordinate) (j:ℕ) :
    ContinuousOn (weightSlope a j) (Ici 4) := by
  intro u large
  have positive:0<u:=lt_of_lt_of_le (by norm_num) large
  unfold weightSlope
  exact ((Complex.continuousAt_ofReal_cpow_const u _ (Or.inr positive.ne')).mul
    ((continuousAt_const.mul ((Complex.continuous_ofReal.continuousAt.comp
      (Real.continuousAt_log positive.ne')).neg.pow j)).sub
      (continuousAt_const.mul ((Complex.continuous_ofReal.continuousAt.comp
        (Real.continuousAt_log positive.ne')).neg.pow (j-1))))).continuousWithinAt

private theorem logarithm_rpow_integrable (j:ℕ) (b:ℝ) (below:b< -1) :
    IntegrableOn (fun u:ℝ=>u^b*(Real.log u)^j) (Ioi 4) := by
  let p:ℝ:=(b-1)/2
  have gap:0<p-b:=by dsimp only [p];linarith
  have logarithm:(fun u:ℝ=>(Real.log u)^j)=O[atTop](fun u:ℝ=>u^(p-b)) := by
    simpa only [Real.rpow_natCast] using (isLittleO_log_rpow_rpow_atTop (j:ℝ) gap).isBigO
  have product: (fun u:ℝ=>u^b*(Real.log u)^j)=O[atTop](fun u:ℝ=>u^p) := by
    have generated:=(isBigO_refl (fun u:ℝ=>u^b) atTop).mul logarithm
    apply generated.congr' (EventuallyEq.refl _ _)
    filter_upwards [eventually_gt_atTop (0:ℝ)] with u positive
    rw [←Real.rpow_add positive,add_sub_cancel]
  have regular:ContinuousOn (fun u:ℝ=>u^b*(Real.log u)^j) (Ici 4) := by
    intro u large
    have positive:0<u:=lt_of_lt_of_le (by norm_num) large
    exact ((Real.continuousAt_rpow_const u b (Or.inl positive.ne')).mul
      ((Real.continuousAt_log positive.ne').pow j)).continuousWithinAt
  have whole:IntegrableOn (fun u:ℝ=>u^b*(Real.log u)^j) (Ici 4) :=
    (regular.locallyIntegrableOn measurableSet_Ici).integrableOn_of_isBigO_atTop product
      ⟨Ioi 4,Ioi_mem_atTop 4,integrableOn_Ioi_rpow_of_lt (by dsimp only [p];linarith) (by norm_num)⟩
  exact whole.mono_set Ioi_subset_Ici_self

private theorem weighted_slope_bound (a:BurnolCompletedMellinCoordinate) (j:ℕ)
    (u:ℝ) (large:4≤u) :
    ‖weightSlope a j u‖*(Real.sqrt u+2)≤
      3*‖a.value‖*(u^(-a.value.re-1/2)*(Real.log u)^j)+
        3*(j:ℝ)*(u^(-a.value.re-1/2)*(Real.log u)^(j-1)) := by
  have positive:0<u:=lt_of_lt_of_le (by norm_num) large
  have logarithm:0≤Real.log u:=Real.log_nonneg (by linarith)
  have power:‖(u:ℂ)^(-star a.value-1)‖=u^(-a.value.re-1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos positive]
    simp only [sub_re,neg_re,star_def,conj_re,one_re]
  have polynomial:‖(-star a.value)*(-(Real.log u:ℂ))^j-(j:ℂ)*(-(Real.log u:ℂ))^(j-1)‖≤
      ‖a.value‖*(Real.log u)^j+(j:ℝ)*(Real.log u)^(j-1) := by
    simpa only [norm_mul,norm_neg,norm_star,norm_pow,Complex.norm_of_nonneg logarithm,
      Complex.norm_natCast] using norm_sub_le ((-star a.value)*(-(Real.log u:ℂ))^j)
        ((j:ℂ)*(-(Real.log u:ℂ))^(j-1))
  have scaling:u^(-a.value.re-1)*(Real.sqrt u+2)≤3*u^(-a.value.re-1/2) := by
    calc
      _≤u^(-a.value.re-1)*(3*Real.sqrt u):=
        mul_le_mul_of_nonneg_left (sqrt_bound u large) (Real.rpow_nonneg positive.le _)
      _=3*(u^(-a.value.re-1)*u^(1/2:ℝ)) := by rw [Real.sqrt_eq_rpow];ring
      _=_ := by rw [←Real.rpow_add positive];congr 2;ring
  rw [weightSlope,norm_mul,power]
  calc
    _≤(u^(-a.value.re-1)*(‖a.value‖*(Real.log u)^j+(j:ℝ)*(Real.log u)^(j-1)))*(Real.sqrt u+2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left polynomial
        (Real.rpow_nonneg positive.le _)) (by positivity)
    _=(u^(-a.value.re-1)*(Real.sqrt u+2))*(‖a.value‖*(Real.log u)^j+(j:ℝ)*(Real.log u)^(j-1)) := by ring
    _≤(3*u^(-a.value.re-1/2))*(‖a.value‖*(Real.log u)^j+(j:ℝ)*(Real.log u)^(j-1)) :=
      mul_le_mul_of_nonneg_right scaling (by positivity)
    _=_ := by ring

theorem weight_domain (a:BurnolCompletedMellinCoordinate) (j:ℕ) :
    IntegrableOn (InfiniteWeightedProgram.weight (deriv (reciprocalWeight a j))) (Ioi 4) := by
  have dominant:=((logarithm_rpow_integrable j (-a.value.re-1/2) (by linarith [a.rightHalf])).const_mul (3*‖a.value‖)).add
    ((logarithm_rpow_integrable (j-1) (-a.value.re-1/2) (by linarith [a.rightHalf])).const_mul (3*(j:ℝ)))
  apply dominant.mono' (((measurable_deriv _).norm.mul
    (Real.continuous_sqrt.measurable.add_const 2)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u large
  change ‖‖deriv (reciprocalWeight a j) u‖*(Real.sqrt u+2)‖≤_
  rw [Real.norm_of_nonneg (by positivity),(weight_hasDerivAt a j u (lt_trans (by norm_num) large)).deriv]
  exact weighted_slope_bound a j u large.le

theorem weight_head (a:BurnolCompletedMellinCoordinate) (j:ℕ) :
    Tendsto (fun u:ℝ=>Real.sqrt u*‖reciprocalWeight a j u‖) atTop (𝓝 0) := by
  have logarithm:(fun u:ℝ=>(Real.log u)^j)=o[atTop](fun u:ℝ=>u^(a.value.re-1/2)) := by
    simpa only [Real.rpow_natCast] using
      isLittleO_log_rpow_rpow_atTop (j:ℝ) (by linarith [a.rightHalf]:0<a.value.re-1/2)
  apply logarithm.tendsto_div_nhds_zero.congr'
  filter_upwards [eventually_ge_atTop (4:ℝ)] with u large
  have positive:0<u:=lt_of_lt_of_le (by norm_num) large
  rw [reciprocal_actual a j u positive,norm_mul,norm_pow,norm_neg,
    Complex.norm_of_nonneg (Real.log_nonneg (by linarith:1≤u)),
    Complex.norm_cpow_eq_rpow_re_of_pos positive]
  simp only [neg_re,star_def,conj_re]
  rw [Real.sqrt_eq_rpow,div_eq_mul_inv,←Real.rpow_neg positive.le,←mul_assoc,
    ←Real.rpow_add positive]
  rw [show -(a.value.re-1/2)=1/2-a.value.re by ring,mul_comm]
  simp only [sub_eq_add_neg]

/-- Every analytic input is generated from the original logarithmic source on the full half-strip. -/
theorem actual_inputs (a:BurnolCompletedMellinCoordinate) (j:ℕ) :
    (∀u:ℝ,4≤u→HasDerivAt (weight (raw a j)) (deriv (weight (raw a j)) u) u)∧
      ContinuousOn (deriv (weight (raw a j))) (Ici 4)∧
      IntegrableOn (InfiniteWeightedProgram.weight (deriv (weight (raw a j)))) (Ioi 4)∧
      Tendsto (fun u:ℝ=>Real.sqrt u*‖weight (raw a j) u‖) atTop (𝓝 0) := by
  refine ⟨fun u large=>(weight_hasDerivAt a j u (lt_of_lt_of_le (by norm_num) large)).differentiableAt.hasDerivAt,?_,weight_domain a j,weight_head a j⟩
  exact (slope_continuous a j).congr (fun u large=>(weight_hasDerivAt a j u
    (lt_of_lt_of_le (by norm_num) large)).deriv)

end OriginalRieszFinitePairing.CoPoisson.Ward.CountedSchur.LogWeight
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
