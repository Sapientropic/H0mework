import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.BForwardEndpointSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKExteriorCoPoissonAction.WindowH.Source

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalSBReverseCompactSource
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction OriginalKCoefficientBFiniteAction OriginalKExteriorCoPoissonAction
open OriginalKFiniteOrderRelease OriginalFullLossRAction OriginalReverseCoreJumpMean
open scoped InnerProductSpace Topology
local notation "q" => (1/4:ℝ)
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "R" => burnolDirectRightResolventCLM
open private gamma unitPrice unitPrice_ne_zero unitCurrent boxScale boxProgram box_family_integrable
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.UnitRProgram
open private SBWeight SBSlope SB_regular
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FullLossRAction
open private scale_raw unitCurrent_raw
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.ReverseCoreJumpMean

/-- The field is constructed from the original computed unit programme, before its R recognition. -/
def sourceField (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) (h:ℝ) : BurnolL2 :=
  boxProgram q (q*Real.exp h) (SBWeight c h) (SBSlope c h) (unitCurrent c zero)+
    centeringMean c h 1 • unitCurrent c zero

def sourceRaw (c:BurnolCompletedMellinCoordinate) (h x:ℝ) : ℂ :=
  SBWeight c h (q*Real.exp h)*
      (scaleProfile (q*Real.exp h) (unitCurrentProfile c) x-scaleProfile q (unitCurrentProfile c) x)-
    (∫ r:ℝ in Ioc q (q*Real.exp h),SBSlope c h r*
      (scaleProfile r (unitCurrentProfile c) x-scaleProfile q (unitCurrentProfile c) x))+
    centeringMean c h 1*unitCurrentProfile c x

/-- This recognition consumes the original complete SB action, including its actual mean. -/
theorem actual_R_source (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nonnegative:0≤h) :
    R c (FullUnit.fullReverse c h 1)=sourceField c zero h :=
  full_reverse_SB_R c zero h nonnegative

private theorem elementary_tail (c:BurnolCompletedMellinCoordinate) (x:ℝ) (outside:q < |x|) :
    elementaryReverseRaw c x=0 := by
  have small:q/|x|<1:=(div_lt_one (by linarith : 0 < |x|)).mpr outside
  have floor:⌊q/|x|⌋₊=0:=Nat.floor_eq_zero.mpr small
  simp only [elementaryReverseRaw,DualSourceRaw.channels,floor,Finset.Icc_eq_empty_of_lt (by omega : (0:ℕ)<1),Finset.sum_empty,neg_zero]

/-- The actual source unit has no unaccounted power tail at the original zero. -/
theorem unit_profile_tail (c:BurnolCompletedMellinCoordinate) (x:ℝ) (outside:q < |x|) :
    unitCurrentProfile c x=(2/(1-c.value))*ConstantDual.sawtoothRaw x := by
  have priced:=unitPrice_ne_zero c
  change (1-c.value)*gamma (barC c)≠0 at priced
  have right:gamma (barC c)≠0:=(mul_ne_zero_iff.mp priced).2
  unfold unitCurrentProfile
  rw [elementary_tail (barC c) x outside,mul_zero,sub_zero]
  unfold unitPrice
  rw [mul_inv_rev]
  calc
    _=((gamma (barC c))⁻¹*gamma (barC c))*((2/(1-c.value))*ConstantDual.sawtoothRaw x) := by ring
    _=_ := by rw [inv_mul_cancel₀ right,one_mul]

open private actual_mean_primitive sourcePrimitive even_half_integral
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKExteriorCoPoissonAction.WindowH.Source
open private profile_even
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKExteriorCoPoissonAction.Source
open private SB_derivative
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FullLossRAction

private theorem mean_balance (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nn:0≤h) :
    (∫ x:ℝ in q..(q*Real.exp h),SBWeight c h x)+(q:ℂ)*centeringMean c h 1=0 := by
  have cont:=burnolRieszReturnRaw_continuous c
  have halfZero:(∫ x:ℝ in (0:ℝ)..q,burnolRieszReturnRaw c x)=0 := by
    have even:=even_half_integral (burnolRieszReturnRaw c) cont.integrableOn_Icc
      (fun x=>profile_even c 1 x)
    change (∫ x:ℝ in Icc (-q) q,burnolRieszReturnRaw c x)=_ at even
    rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le (by norm_num : -q≤q),
      Constructor.return_integral_zero,←intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤q)] at even
    exact (mul_eq_zero.mp even.symm).resolve_left (by norm_num)
  have mean:=actual_mean_primitive c h nn 1
  change centeringMean c h 1=4*(Real.exp (h/2):ℂ)*
    (∫ x:ℝ in (0:ℝ)..(q*Real.exp (-h)),burnolRieszReturnRaw c x) at mean
  have split:=intervalIntegral.integral_add_adjacent_intervals
    (cont.intervalIntegrable (μ:=volume) 0 (q*Real.exp (-h))) (cont.intervalIntegrable (μ:=volume) (q*Real.exp (-h)) q)
  rw [halfZero] at split
  have scale:Real.exp (-h/2)*(Real.exp (-h))⁻¹=Real.exp (h/2) := by
    rw [←Real.exp_neg,neg_neg,←Real.exp_add]
    congr 1
    ring
  have edge:Real.exp (-h)*(q*Real.exp h)=q := by
    rw [Real.exp_neg]
    field_simp
  have shifted:(∫ x:ℝ in q..(q*Real.exp h),SBWeight c h x)=
      (Real.exp (h/2):ℂ)*(∫ x:ℝ in (q*Real.exp (-h))..q,burnolRieszReturnRaw c x) := by
    unfold SBWeight
    rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_mul_left _ (Real.exp_ne_zero (-h)),edge]
    simp only [Complex.real_smul]
    rw [mul_comm (Real.exp (-h)) q,←mul_assoc,←Complex.ofReal_mul,scale]
  rw [shifted,mean]
  norm_num only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]
  linear_combination (Real.exp (h/2):ℂ)*split

private theorem weighted_mean_balance (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nn:0≤h) :
    SBWeight c h (q*Real.exp h)*((q*Real.exp h:ℝ)-q)-
      (∫ r:ℝ in Ioc q (q*Real.exp h),SBSlope c h r*((r:ℂ)-q))+
      (q:ℂ)*centeringMean c h 1=0 := by
  have regular:Continuous (SBWeight c h):=continuous_iff_continuousAt.mpr
    (fun x=>(SB_derivative c h x).continuousAt)
  have ordered:q≤q*Real.exp h:=by nlinarith [Real.one_le_exp_iff.mpr nn]
  have actual:=intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt
    (a:=q) (b:=q*Real.exp h) (u:=SBWeight c h) (u':=SBSlope c h)
    (v:=fun x:ℝ=>(x:ℂ)-(q:ℂ)) (v':=fun _=>(1:ℂ))
    regular.continuousOn ((Complex.continuous_ofReal.sub continuous_const).continuousOn)
    (fun x _=>SB_derivative c h x) (fun x _=>Complex.ofRealCLM.hasDerivAt.sub_const (q:ℂ))
    ((SB_regular c h).intervalIntegrable q (q*Real.exp h))
    (intervalIntegrable_const (c:=(1:ℂ)))
  have prod:IntervalIntegrable (fun r:ℝ=>SBSlope c h r*((r:ℂ)-q)) volume q (q*Real.exp h):=
    ((SB_regular c h).mul (Complex.continuous_ofReal.sub continuous_const)).intervalIntegrable _ _
  norm_num only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat,mul_one,sub_self,mul_zero,sub_zero] at actual
  norm_num only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] at prod
  rw [intervalIntegral.integral_add prod (regular.intervalIntegrable _ _)] at actual
  simp_rw [intervalIntegral.integral_of_le ordered] at actual
  have mean:=mean_balance c h nn
  rw [intervalIntegral.integral_of_le ordered] at mean
  push_cast at actual mean ⊢
  linear_combination -actual+mean

set_option backward.isDefEq.respectTransparency true in
private theorem unit_profile_measurable (c:BurnolCompletedMellinCoordinate) :
    Measurable (unitCurrentProfile c) := by
  let f:ℕ→ℝ→ℂ:=fun N x=>-(∑ n∈Finset.Icc 1 N,
    ((1/2:ℂ)*(((n:ℝ)*|x|:ℝ):ℂ)^(-star (barC c).value)-GapEuler.gapMean q (barC c)))
  have finite (N:ℕ):Measurable (f N) := by
    dsimp only [f]
    apply Measurable.neg
    apply Finset.measurable_sum
    intro n member
    apply measurable_of_continuousOn_compl_singleton 0
    intro x outside
    have nz:x≠0:=by simpa only [mem_compl_iff,mem_singleton_iff] using outside
    have np:(0:ℝ)<n:=by exact_mod_cast (Finset.mem_Icc.mp member).1
    have power:=Complex.continuousAt_ofReal_cpow_const ((n:ℝ)*|x|) (-star (barC c).value)
      (Or.inr (mul_ne_zero np.ne' (abs_ne_zero.mpr nz)))
    have argument:ContinuousAt (fun y:ℝ=>(n:ℝ)*|y|) x:=
      (continuous_const.mul continuous_abs).continuousAt
    have localPower:ContinuousAt (fun y:ℝ=>(((n:ℝ)*|y|:ℝ):ℂ)^(-star (barC c).value)) x:=
      ContinuousAt.comp (f:=fun y:ℝ=>(n:ℝ)*|y|) (x:=x) power argument
    exact ((continuousAt_const.mul localPower).sub
      continuousAt_const).continuousWithinAt
  have joint:Measurable (fun p:ℕ×ℝ=>f p.1 p.2):=measurable_from_prod_countable_right finite
  have count:Measurable (fun x:ℝ=>⌊q/|x|⌋₊):=(measurable_const.div continuous_abs.measurable).nat_floor
  have elementary:Measurable (elementaryReverseRaw (barC c)):=by
    change Measurable (fun x:ℝ=>-(∑ n∈Finset.Icc 1 ⌊q/|x|⌋₊,
      ((1/2:ℂ)*(((n:ℝ)*|x|:ℝ):ℂ)^(-star (barC c).value)-GapEuler.gapMean q (barC c))))
    simpa only [f,Function.comp_def,id_eq] using
      joint.comp (count.prodMk measurable_id)
  change Measurable (fun x:ℝ=>(unitPrice c)⁻¹*
    ((2*gamma (barC c))*ConstantDual.sawtoothRaw x-2*elementaryReverseRaw (barC c) x))
  simpa only [Pi.sub_apply] using
    ((ConstantDual.sawtooth_measurable.const_mul (2*gamma (barC c))).sub
      (elementary.const_mul 2)).const_mul ((unitPrice c)⁻¹)

private theorem source_raw (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) (h:ℝ) :
    (sourceField c zero h:ℝ→ℂ)=ᵐ[volume] sourceRaw c h := by
  have scale (r:ℝ):=(scale_raw r (unitCurrent c zero) (unitCurrentProfile c) (unitCurrent_raw c zero))
  have profile:=unit_profile_measurable c
  have slope:Measurable (SBSlope c h):=(SB_regular c h).measurable
  have integral:=OriginalPaPhysicalGreen.source_l2_bochner_coeFn
    (volume.restrict (Ioc q (q*Real.exp h)))
    (fun r=>SBSlope c h r • (boxScale (unitCurrent c zero) r-boxScale (unitCurrent c zero) q))
    (box_family_integrable _ _ _ (by norm_num) (SB_regular c h).continuousOn _)
    (fun p=>SBSlope c h p.1*(scaleProfile p.1 (unitCurrentProfile c) p.2-scaleProfile q (unitCurrentProfile c) p.2))
    (by unfold scaleProfile dilationProfile;fun_prop)
    (by
      filter_upwards with r
      filter_upwards [Lp.coeFn_smul (SBSlope c h r) (boxScale (unitCurrent c zero) r-boxScale (unitCurrent c zero) q),
        Lp.coeFn_sub (boxScale (unitCurrent c zero) r) (boxScale (unitCurrent c zero) q),scale r,scale q]
        with x scalar difference a b
      rw [scalar]
      simp only [Pi.smul_apply,smul_eq_mul,difference,Pi.sub_apply,a,b])
  filter_upwards [Lp.coeFn_add (boxProgram q (q*Real.exp h) (SBWeight c h) (SBSlope c h) (unitCurrent c zero))
      (centeringMean c h 1 • unitCurrent c zero),
    Lp.coeFn_sub (SBWeight c h (q*Real.exp h) • (boxScale (unitCurrent c zero) (q*Real.exp h)-boxScale (unitCurrent c zero) q))
      (∫ r:ℝ in Ioc q (q*Real.exp h),SBSlope c h r • (boxScale (unitCurrent c zero) r-boxScale (unitCurrent c zero) q)),
    Lp.coeFn_smul (SBWeight c h (q*Real.exp h)) (boxScale (unitCurrent c zero) (q*Real.exp h)-boxScale (unitCurrent c zero) q),
    Lp.coeFn_sub (boxScale (unitCurrent c zero) (q*Real.exp h)) (boxScale (unitCurrent c zero) q),
    scale (q*Real.exp h),scale q,integral,Lp.coeFn_smul (centeringMean c h 1) (unitCurrent c zero),unitCurrent_raw c zero]
    with x total difference scalar feet hi lo native unit read
  change (boxProgram _ _ _ _ (unitCurrent c zero)+centeringMean c h 1 • unitCurrent c zero:BurnolL2) x=_
  rw [total]
  change ((SBWeight c h (q*Real.exp h) • (boxScale (unitCurrent c zero) (q*Real.exp h)-boxScale (unitCurrent c zero) q)-
    ∫ r:ℝ in Ioc q (q*Real.exp h),SBSlope c h r • (boxScale (unitCurrent c zero) r-boxScale (unitCurrent c zero) q):BurnolL2) x)+_=_
  rw [difference]
  simp only [Pi.sub_apply]
  rw [scalar,unit]
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,feet,hi,lo,native,read,sourceRaw]

private theorem scale_profile (r:ℝ) (rp:0<r) (profile:ℝ→ℂ) (x:ℝ) :
    scaleProfile r profile x=profile (q*x/r) := by
  have root:Real.exp (Real.log r/2)=Real.sqrt r := by rw [Real.exp_half,Real.exp_log rp]
  have quarter:Real.exp (Real.log q/2)=1/2 := by
    rw [Real.exp_half,Real.exp_log (by norm_num : (0:ℝ)<q)]
    have four:Real.sqrt (4:ℝ)=2 := by
      rw [show (4:ℝ)=2^2 by norm_num,Real.sqrt_sq (by norm_num : (0:ℝ)≤2)]
    norm_num [Real.sqrt_div,four]
  have inverse:Real.sqrt r*Real.exp (-Real.log r/2)=1 := by
    rw [show -Real.log r/2=-(Real.log r/2) by ring,Real.exp_neg,root]
    exact mul_inv_cancel₀ (Real.sqrt_pos.mpr rp).ne'
  unfold scaleProfile dilationProfile
  rw [quarter,Real.exp_log (by norm_num : (0:ℝ)<q),Real.exp_neg,Real.exp_log rp]
  have moved:q*(r⁻¹*x)=q*x/r := by ring
  dsimp only
  rw [moved]
  calc
    _=((Real.sqrt r:ℂ)*(Real.exp (-Real.log r/2):ℂ))*profile (q*x/r) := by push_cast;ring
    _=_ := by rw [←Complex.ofReal_mul,inverse,Complex.ofReal_one,one_mul]

private theorem source_raw_tail (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nn:0≤h)
    (x:ℝ) (outside:q*Real.exp h < |x|) : sourceRaw c h x=0 := by
  let k:=-(2:ℂ)/((1-c.value)*((|x|:ℝ):ℂ))
  have ordered:q≤q*Real.exp h:=by nlinarith [Real.one_le_exp_iff.mpr nn]
  have xq:q < |x|:=ordered.trans_lt outside
  have scaled (r:ℝ) (rp:0<r) (small:r≤q*Real.exp h) :
      scaleProfile r (unitCurrentProfile c) x=(r:ℂ)*k := by
    have far:q < |q*x/r| := by
      rw [abs_div,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<q),abs_of_pos rp]
      exact (lt_div_iff₀ rp).mpr (by nlinarith [small.trans_lt outside])
    rw [scale_profile r rp,unit_profile_tail c _ far,ConstantDual.sawtooth_tail _ far]
    rw [abs_div,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<q),abs_of_pos rp]
    dsimp only [k]
    push_cast
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
    norm_num
    ring
  have unit:unitCurrentProfile c x=(q:ℂ)*k := by
    rw [unit_profile_tail c x xq,ConstantDual.sawtooth_tail x xq]
    dsimp only [k]
    push_cast
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  have native:(∫ r:ℝ in Ioc q (q*Real.exp h),SBSlope c h r*
      (scaleProfile r (unitCurrentProfile c) x-scaleProfile q (unitCurrentProfile c) x))=
      (∫ r:ℝ in Ioc q (q*Real.exp h),SBSlope c h r*((r:ℂ)-q))*k := by
    rw [←integral_mul_const]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro r inside
    dsimp only
    rw [scaled r (by linarith [inside.1]) inside.2,scaled q (by norm_num) ordered]
    push_cast
    ring
  unfold sourceRaw
  rw [native,scaled (q*Real.exp h) (by positivity) le_rfl,scaled q (by norm_num) ordered,unit]
  have balance:=weighted_mean_balance c h nn
  push_cast at balance ⊢
  linear_combination k*balance

/-- The native source field is compact before it is recognized as the original R effect. -/
theorem source_compact (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nn:0≤h) :
    OriginalPaPhysicalGreen.originalPhysicalCutoff (q*Real.exp h) (sourceField c zero h)=sourceField c zero h := by
  apply OriginalRieszFiniteColumns.cutoff_eq_self_of_ae_zero
  filter_upwards [source_raw c zero h] with x read outside
  have far:q*Real.exp h < |x|:=lt_of_not_ge (fun small=>outside (abs_le.mp small))
  rw [read,source_raw_tail c h nn x far]

/-- Complete SB centering and the entire R box pay their common tail together. -/
theorem actual_R_compact (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nn:0≤h) :
    OriginalPaPhysicalGreen.originalPhysicalCutoff (q*Real.exp h)
      (R c (FullUnit.fullReverse c h 1))=R c (FullUnit.fullReverse c h 1) := by
  rw [actual_R_source c zero h nn]
  exact source_compact c zero h nn

end OriginalSBReverseCompactSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
