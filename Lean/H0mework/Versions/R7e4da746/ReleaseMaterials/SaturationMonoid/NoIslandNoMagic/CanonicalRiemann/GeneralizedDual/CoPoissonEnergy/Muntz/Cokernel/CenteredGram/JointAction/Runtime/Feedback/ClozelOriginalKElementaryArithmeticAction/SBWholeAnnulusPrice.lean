import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.SBQuarterMeanSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.SBReverseCompactProgramme

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalSBWholeAnnulusPrice
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction OriginalKCoefficientBFiniteAction OriginalKExteriorCoPoissonAction
open OriginalFullLossRAction OriginalReverseCoreJumpMean OriginalSBReverseCompactSource
open scoped InnerProductSpace Topology
local notation "q" => (1/4:ℝ)
local notation "Rq" => burnolQuarterRestriction
local notation "mu" => burnolQuarterMeanCoefficient
local notation "C" => ConstantDual.value
local notation "K" => burnolCompletedMellinRieszVector
local instance quarterFinite : IsFiniteMeasure ((volume:Measure ℝ).restrict (symmetricInterval q)) where
  measure_univ_lt_top:=lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top q)
open private boxScale boxProgram box_family_integrable
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.UnitRProgram
open private SBWeight SBSlope SB_regular SB_derivative SB_reverse_actual
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FullLossRAction
open private scale_raw
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.ReverseCoreJumpMean
open private scale_profile weighted_mean_balance
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.SBReverseCompactSource
open private meanFunctional mean_functional mean_half_raw
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.SBQuarterMeanSource

private def wholeRaw (c:BurnolCompletedMellinCoordinate) (h x:ℝ) : ℂ :=
  SBWeight c h (q*Real.exp h)*(scaleProfile (q*Real.exp h) ConstantDual.sawtoothRaw x-scaleProfile q ConstantDual.sawtoothRaw x)-
    (∫r:ℝ in Ioc q (q*Real.exp h),SBSlope c h r*(scaleProfile r ConstantDual.sawtoothRaw x-scaleProfile q ConstantDual.sawtoothRaw x))+
    centeringMean c h 1*ConstantDual.sawtoothRaw x

private theorem whole_raw (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nn:0≤h) :
    (FullUnit.fullReverse c h 1:ℝ→ℂ)=ᵐ[volume]wholeRaw c h := by
  rw [SB_reverse_actual c h nn]
  have scale (r:ℝ):=scale_raw r C ConstantDual.sawtoothRaw ConstantDual.value_coeFn
  have slope:Measurable (SBSlope c h):=(SB_regular c h).measurable
  have profile:=ConstantDual.sawtooth_measurable
  have native:=OriginalPaPhysicalGreen.source_l2_bochner_coeFn
    (volume.restrict (Ioc q (q*Real.exp h)))
    (fun r=>SBSlope c h r • (boxScale C r-boxScale C q))
    (box_family_integrable _ _ _ (by norm_num) (SB_regular c h).continuousOn C)
    (fun p=>SBSlope c h p.1*(scaleProfile p.1 ConstantDual.sawtoothRaw p.2-scaleProfile q ConstantDual.sawtoothRaw p.2))
    (by unfold scaleProfile dilationProfile;fun_prop)
    (by
      filter_upwards with r
      filter_upwards [Lp.coeFn_smul (SBSlope c h r) (boxScale C r-boxScale C q),
        Lp.coeFn_sub (boxScale C r) (boxScale C q),scale r,scale q] with x scalar difference hi lo
      rw [scalar]
      simp only [Pi.smul_apply,smul_eq_mul,difference,Pi.sub_apply,hi,lo])
  filter_upwards [Lp.coeFn_add (boxProgram q (q*Real.exp h) (SBWeight c h) (SBSlope c h) C)
      (centeringMean c h 1 • C),
    Lp.coeFn_sub (SBWeight c h (q*Real.exp h) • (boxScale C (q*Real.exp h)-boxScale C q))
      (∫r:ℝ in Ioc q (q*Real.exp h),SBSlope c h r • (boxScale C r-boxScale C q)),
    Lp.coeFn_smul (SBWeight c h (q*Real.exp h)) (boxScale C (q*Real.exp h)-boxScale C q),
    Lp.coeFn_sub (boxScale C (q*Real.exp h)) (boxScale C q),scale (q*Real.exp h),scale q,native,
    Lp.coeFn_smul (centeringMean c h 1) C,ConstantDual.value_coeFn]
      with x total difference scalar feet hi lo integral unit read
  rw [total]
  change ((SBWeight c h (q*Real.exp h) • (boxScale C (q*Real.exp h)-boxScale C q)-
    ∫r:ℝ in Ioc q (q*Real.exp h),SBSlope c h r • (boxScale C r-boxScale C q):BurnolL2) x)+_=_
  rw [difference]
  simp only [Pi.sub_apply]
  rw [scalar,unit]
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,feet,hi,lo,integral,read,wholeRaw]

private theorem saw_one_cell (s:ℝ) (lo:q/2<s) (hi:s≤q) :
    ConstantDual.sawtoothRaw s=1-(q/s:ℝ) := by
  have sp:0<s:=by linarith
  have floor:⌊q/s⌋=(1:ℤ):=by
    apply Int.floor_eq_iff.mpr
    norm_num only [Int.cast_one]
    constructor
    · exact (le_div_iff₀ sp).mpr (by simpa using hi)
    · exact (div_lt_iff₀ sp).mpr (by linarith)
  simp only [ConstantDual.sawtoothRaw,abs_of_pos sp,Int.fract,floor,Int.cast_one]
  push_cast
  ring

private theorem scale_saw_outer (h x r:ℝ) (small:h<Real.log 2) (outside:q< |x|)
    (rp:0<r) (upper:r≤q*Real.exp h) :
    scaleProfile r ConstantDual.sawtoothRaw x=-(r:ℂ)/((|x|:ℝ):ℂ)+(if |x|≤r then 1 else 0) := by
  have xp:0< |x|:=by linarith
  have cap:q*Real.exp h<2*q:=by
    have ex:Real.exp h<2:=by simpa only [Real.exp_log (by norm_num : (0:ℝ)<2)] using Real.exp_lt_exp.mpr small
    nlinarith
  have absolute:|q*x/r|=q*|x|/r:=by
    rw [abs_div,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<q),abs_of_pos rp]
  rw [scale_profile r rp]
  have absRead:ConstantDual.sawtoothRaw (q*x/r)=ConstantDual.sawtoothRaw (q*|x|/r):=by
    simp only [ConstantDual.sawtoothRaw,absolute,abs_of_pos (by positivity : 0<q*|x|/r)]
  rw [absRead]
  by_cases active:|x|≤r
  · have low:q/2<q*|x|/r:=(lt_div_iff₀ rp).mpr (by nlinarith [upper.trans_lt cap])
    have high:q*|x|/r≤q:=(div_le_iff₀ rp).mpr (by nlinarith)
    rw [saw_one_cell _ low high,if_pos active]
    push_cast
    field_simp
    ring
  · have far:q<q*|x|/r:=(lt_div_iff₀ rp).mpr (by nlinarith [lt_of_not_ge active])
    have farAbs:q< |q*|x|/r|:=by simpa only [abs_of_pos (by positivity : 0<q*|x|/r)] using far
    rw [ConstantDual.sawtooth_tail _ farAbs,abs_of_pos (by positivity : 0<q*|x|/r),if_neg active,add_zero]
    push_cast
    field_simp

private theorem whole_outer (c:BurnolCompletedMellinCoordinate) (h x:ℝ)
    (nn:0≤h) (small:h<Real.log 2) (outside:q< |x|) :
    wholeRaw c h x=if |x|≤q*Real.exp h then SBWeight c h |x| else 0 := by
  let k:ℂ:=-1/((|x|:ℝ):ℂ)
  have ordered:q≤q*Real.exp h:=by nlinarith [Real.one_le_exp_iff.mpr nn]
  have unit:ConstantDual.sawtoothRaw x=(q:ℂ)*k:=by
    rw [ConstantDual.sawtooth_tail x outside]
    dsimp only [k]
    push_cast
    ring
  have low:scaleProfile q ConstantDual.sawtoothRaw x=(q:ℂ)*k:=by
    rw [scale_saw_outer h x q small outside (by norm_num) ordered,if_neg (not_le_of_gt outside),add_zero]
    dsimp only [k]
    ring
  have coefficients:IntegrableOn (fun r:ℝ=>SBSlope c h r*((r:ℂ)-(q:ℂ))) (Ioc q (q*Real.exp h)):=
    ((SB_regular c h).mul (Complex.continuous_ofReal.sub continuous_const)).integrableOn_Ioc
  have stepInt:IntegrableOn (fun r:ℝ=>SBSlope c h r*(if |x|≤r then (1:ℂ) else 0)) (Ioc q (q*Real.exp h)):=by
    have indicator:(fun r:ℝ=>SBSlope c h r*(if |x|≤r then (1:ℂ) else 0))=
      (Ici |x|).indicator (SBSlope c h):=by funext r;by_cases active:|x|≤r <;> simp [active]
    rw [indicator]
    exact (((SB_regular c h).integrableOn_Icc).mono_set Ioc_subset_Icc_self).indicator measurableSet_Ici
  have native:(∫r:ℝ in Ioc q (q*Real.exp h),SBSlope c h r*(scaleProfile r ConstantDual.sawtoothRaw x-scaleProfile q ConstantDual.sawtoothRaw x))=
    (∫r:ℝ in Ioc q (q*Real.exp h),SBSlope c h r*((r:ℂ)-(q:ℂ)))*k+
      ∫r:ℝ in Ioc q (q*Real.exp h),SBSlope c h r*(if |x|≤r then (1:ℂ) else 0) := by
    rw [←integral_mul_const,←integral_add (coefficients.mul_const k) stepInt]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro r member
    dsimp only
    rw [scale_saw_outer h x r small outside (by linarith [member.1]) member.2,low]
    dsimp only [k]
    ring
  have collapsed:wholeRaw c h x=SBWeight c h (q*Real.exp h)*(if |x|≤q*Real.exp h then (1:ℂ) else 0)-
      ∫r:ℝ in Ioc q (q*Real.exp h),SBSlope c h r*(if |x|≤r then (1:ℂ) else 0) := by
    unfold wholeRaw
    rw [native,scale_saw_outer h x (q*Real.exp h) small outside (by positivity) le_rfl,low,unit]
    have balance:=weighted_mean_balance c h nn
    dsimp only [k]
    push_cast at balance ⊢
    linear_combination k*balance
  rw [collapsed]
  have indicator:(fun r:ℝ=>SBSlope c h r*(if |x|≤r then (1:ℂ) else 0))=
      (Ici |x|).indicator (SBSlope c h):=by funext r;by_cases active:|x|≤r <;> simp [active]
  rw [indicator,setIntegral_indicator measurableSet_Ici]
  have intersection:Ioc q (q*Real.exp h)∩Ici |x|=Icc |x| (q*Real.exp h):=by
    ext r
    simp only [mem_inter_iff,mem_Ioc,mem_Ici,mem_Icc]
    constructor
    · rintro ⟨⟨_,hi⟩,lo⟩;exact ⟨lo,hi⟩
    · rintro ⟨lo,hi⟩;exact ⟨⟨outside.trans_le lo,hi⟩,lo⟩
  rw [intersection,integral_Icc_eq_integral_Ioc]
  by_cases inside:|x|≤q*Real.exp h
  · rw [if_pos inside,mul_one]
    have primitive:=intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r _=>SB_derivative c h r) ((SB_regular c h).intervalIntegrable |x| (q*Real.exp h))
    rw [intervalIntegral.integral_of_le inside] at primitive
    rw [primitive,if_pos inside]
    ring
  · simp only [if_neg inside,mul_zero,Ioc_eq_empty_of_le (le_of_not_ge inside),setIntegral_empty,sub_zero]

/-- The full reverse count recovers its original annulus source outside the quarter. -/
theorem whole_source_split (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nn:0≤h) (small:h<Real.log 2) :
    FullUnit.fullReverse c h 1=burnolQuarterZeroExtension (Rq (FullUnit.fullReverse c h 1))+exteriorSource c h 1 := by
  have cutoff:=OriginalPaPhysicalGreen.originalPhysicalCutoff_coeFn q (FullUnit.fullReverse c h 1)
  have source:=OriginalKExteriorRVolterra.actual_source_raw c h nn 1
  apply Lp.ext
  filter_upwards [whole_raw c h nn,cutoff,source,
    Lp.coeFn_add (burnolQuarterZeroExtension (Rq (FullUnit.fullReverse c h 1))) (exteriorSource c h 1)]
      with x raw crop exterior total
  rw [total]
  change FullUnit.fullReverse c h 1 x=OriginalPaPhysicalGreen.originalPhysicalCutoff q (FullUnit.fullReverse c h 1) x+exteriorSource c h 1 x
  rw [crop,exterior]
  unfold OriginalKExteriorRVolterra.shellRaw
  by_cases inside:x∈symmetricInterval q
  · rw [indicator_of_mem inside,if_neg (fun active=>not_lt_of_ge (abs_le.mpr inside) active.1),add_zero]
  · have outside:q< |x|:=lt_of_not_ge (fun small=>inside (abs_le.mp small))
    rw [indicator_of_notMem inside,zero_add,raw,whole_outer c h x nn small outside]
    change (if |x|≤q*Real.exp h then SBWeight c h |x| else 0)=
      if q< |x| ∧ |x|≤q*Real.exp h then SBWeight c h |x| else 0
    simp only [outside,true_and]

private theorem saw_integrable : IntervalIntegrable ConstantDual.sawtoothRaw volume 0 q := by
  have read:((Rq C:BurnolQuarterIntervalL2):ℝ→ℂ)=ᵐ[volume.restrict (symmetricInterval q)]ConstantDual.sawtoothRaw:=
    (LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) C).trans (ae_restrict_of_ae ConstantDual.value_coeFn)
  have integral:IntegrableOn ConstantDual.sawtoothRaw (symmetricInterval q):=
    ((Lp.memLp (Rq C)).integrable (by norm_num)).congr read
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0:ℝ)≤q)).mpr
  exact integral.mono_set (by intro x member;exact ⟨by linarith [member.1],member.2⟩)

private def correction (r:ℝ) : ℂ := 4*((r:ℂ)-(q:ℂ)-(r:ℂ)*(Real.log (r/q):ℂ))
private def drive (r:ℝ) : ℂ := -4*(Real.log (r/q):ℂ)
private theorem correction_zero : correction q=0 := by simp [correction]
private theorem correction_derivative (r:ℝ) (rp:0<r) : HasDerivAt correction (drive r) r := by
  have logarithm:=((Real.hasDerivAt_log (div_ne_zero rp.ne' (by norm_num : q≠0))).comp r
    ((hasDerivAt_id r).div_const q)).ofReal_comp
  have generated:=((Complex.ofRealCLM.hasDerivAt.sub_const (q:ℂ)).sub
    (Complex.ofRealCLM.hasDerivAt.mul logarithm)).const_mul 4
  convert! generated using 1
  unfold drive
  push_cast
  norm_num
  field_simp [Complex.ofReal_ne_zero.mpr rp.ne']
  ring

private theorem correction_continuous : ContinuousOn correction (Ioi 0):=
  fun r inside=>(correction_derivative r inside).continuousAt.continuousWithinAt
private theorem drive_continuous : ContinuousOn drive (Ioi 0):=by
  intro r inside
  have actual:ContinuousAt drive r:=by
    unfold drive
    exact (((continuous_id.div_const q).continuousAt.log (div_ne_zero inside.ne' (by norm_num : q≠0))).ofReal).const_mul (-4)
  exact actual.continuousWithinAt

private theorem correction_integral (r:ℝ) (lo:q≤r) (hi:r<2*q) :
    (4:ℂ)*(r/q:ℝ)*(∫s:ℝ in (q*q/r)..q,ConstantDual.sawtoothRaw s)=correction r := by
  have rp:0<r:=lt_of_lt_of_le (by norm_num) lo
  have low:q/2<q*q/r:=(lt_div_iff₀ rp).mpr (by nlinarith)
  have high:q*q/r≤q:=(div_le_iff₀ rp).mpr (by nlinarith)
  have positive:0≤q*q/r:=by positivity
  have integrable:=saw_integrable.mono_set (by
    rw [uIcc_of_le high,uIcc_of_le (by norm_num : (0:ℝ)≤q)]
    exact Icc_subset_Icc positive le_rfl)
  let primitive:ℝ→ℂ:=fun s=>(s:ℂ)-(q:ℂ)*(Real.log s:ℂ)
  have derivative (s:ℝ) (sp:0<s):HasDerivAt primitive (1-(q/s:ℝ)) s:=by
    convert! Complex.ofRealCLM.hasDerivAt.sub ((Real.hasDerivAt_log sp.ne').ofReal_comp.const_mul (q:ℂ)) using 1
    push_cast
    simp only [Complex.ofRealCLM_apply,Complex.ofReal_one]
    ring
  have computed:=intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le high
    (show ContinuousOn primitive (Icc (q*q/r) q) from fun s member=>(derivative s (by linarith [member.1])).continuousAt.continuousWithinAt)
    (fun s member=>by rw [saw_one_cell s (low.trans member.1) member.2.le];exact derivative s (by linarith [member.1])) integrable
  rw [computed]
  dsimp only [primitive]
  unfold correction
  rw [Real.log_div (mul_ne_zero (by norm_num : q≠0) (by norm_num : q≠0)) rp.ne',
    Real.log_mul (by norm_num : q≠0) (by norm_num : q≠0),Real.log_div rp.ne' (by norm_num : q≠0)]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr rp.ne']
  ring

private theorem scale_mean (r:ℝ) (lo:q≤r) (hi:r<2*q) :
    meanFunctional (boxScale C r)=(r/q:ℝ)*meanFunctional C-correction r := by
  have rp:0<r:=lt_of_lt_of_le (by norm_num) lo
  have scaled:(boxScale C r:ℝ→ℂ)=ᵐ[volume]fun x=>ConstantDual.sawtoothRaw (q*x/r):=by
    filter_upwards [scale_raw r _ _ ConstantDual.value_coeFn] with x read
    exact read.trans (scale_profile r rp _ x)
  have even:∀x:ℝ,ConstantDual.sawtoothRaw (q*(-x)/r)=ConstantDual.sawtoothRaw (q*x/r):=by
    intro x
    simp only [ConstantDual.sawtoothRaw,mul_neg,neg_div,abs_neg]
  have unitEven:∀x:ℝ,ConstantDual.sawtoothRaw (-x)=ConstantDual.sawtoothRaw x:=by intro x;simp only [ConstantDual.sawtoothRaw,abs_neg]
  rw [mean_half_raw _ _ scaled even,mean_half_raw _ _ ConstantDual.value_coeFn unitEven]
  have rewrite_integral:(∫x:ℝ in (0:ℝ)..q,ConstantDual.sawtoothRaw (q*x/r))=
      (r/q:ℝ)*(∫x:ℝ in (0:ℝ)..(q*q/r),ConstantDual.sawtoothRaw x):=by
    have body:(fun x:ℝ=>ConstantDual.sawtoothRaw (q*x/r))=(fun x:ℝ=>ConstantDual.sawtoothRaw ((q/r)*x)):=by funext x;congr 1;ring
    rw [body,intervalIntegral.integral_comp_mul_left _ (div_ne_zero (by norm_num) rp.ne')]
    simp only [mul_zero,Complex.real_smul]
    congr 1
    · field_simp
    · congr 1;ring
  rw [rewrite_integral]
  have high:q*q/r≤q:=(div_le_iff₀ rp).mpr (by nlinarith)
  have positive:0≤q*q/r:=by positivity
  have first:=saw_integrable.mono_set (by
    rw [uIcc_of_le positive,uIcc_of_le (by norm_num : (0:ℝ)≤q)]
    exact Icc_subset_Icc le_rfl high)
  have last:=saw_integrable.mono_set (by
    rw [uIcc_of_le high,uIcc_of_le (by norm_num : (0:ℝ)≤q)]
    exact Icc_subset_Icc positive le_rfl)
  have split:=intervalIntegral.integral_add_adjacent_intervals first last
  have computed:=correction_integral r lo hi
  linear_combination (norm:=ring_nf) 4*(r/q:ℝ)*split-computed

/-- The complete same-W mean is generated without evaluating the whole sawtooth mass. -/
theorem whole_quarter_mean (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nn:0≤h) (small:h<Real.log 2) :
    mu (Rq (FullUnit.fullReverse c h 1))=4*∫r:ℝ in Ioc q (q*Real.exp h),SBWeight c h r*(Real.log (r/q):ℂ) := by
  rw [SB_reverse_actual c h nn,←mean_functional]
  have ordered:q≤q*Real.exp h:=by nlinarith [Real.one_le_exp_iff.mpr nn]
  have bound:q*Real.exp h<2*q:=by
    have ex:Real.exp h<2:=by simpa only [Real.exp_log (by norm_num : (0:ℝ)<2)] using Real.exp_lt_exp.mpr small
    nlinarith
  have scaled (r:ℝ) (member:r∈Icc q (q*Real.exp h)):=scale_mean r member.1 (member.2.trans_lt bound)
  have meanIntegral:=meanFunctional.integral_comp_comm
    (box_family_integrable q (q*Real.exp h) (SBSlope c h) (by norm_num) (SB_regular c h).continuousOn C)
  have integral:(∫r:ℝ in Ioc q (q*Real.exp h),SBSlope c h r*
      (meanFunctional (boxScale C r)-meanFunctional (boxScale C q)))=
    (∫r:ℝ in Ioc q (q*Real.exp h),SBSlope c h r*((r:ℂ)-q))*(meanFunctional C/(q:ℂ))-
      ∫r:ℝ in Ioc q (q*Real.exp h),SBSlope c h r*correction r := by
    have first:IntegrableOn (fun r:ℝ=>SBSlope c h r*((r:ℂ)-q)) (Ioc q (q*Real.exp h)):=
      ((SB_regular c h).mul (Complex.continuous_ofReal.sub continuous_const)).integrableOn_Ioc
    have last:IntegrableOn (fun r:ℝ=>SBSlope c h r*correction r) (Ioc q (q*Real.exp h)):=
      (((SB_regular c h).continuousOn.mul (correction_continuous.mono (by intro r member;exact lt_of_lt_of_le (by norm_num) member.1))).integrableOn_Icc).mono_set Ioc_subset_Icc_self
    rw [←integral_mul_const,←integral_sub (first.mul_const _) last]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro r member
    dsimp only
    rw [scaled r ⟨member.1.le,member.2⟩,scaled q ⟨le_rfl,ordered⟩,correction_zero]
    push_cast
    ring
  have byParts:=intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt
    (a:=q) (b:=q*Real.exp h) (u:=SBWeight c h) (u':=SBSlope c h) (v:=correction) (v':=drive)
    (continuous_iff_continuousAt.mpr (fun x=>(SB_derivative c h x).continuousAt)).continuousOn
    (correction_continuous.mono (by rw [uIcc_of_le ordered];intro r member;exact lt_of_lt_of_le (by norm_num) member.1))
    (fun r _=>SB_derivative c h r)
    (fun r member=>correction_derivative r (by rw [min_eq_left ordered] at member;exact lt_trans (by norm_num) member.1))
    ((SB_regular c h).intervalIntegrable _ _)
    (drive_continuous.mono (by rw [uIcc_of_le ordered];intro r member;exact lt_of_lt_of_le (by norm_num) member.1)).intervalIntegrable
  have first:IntervalIntegrable (fun r:ℝ=>SBSlope c h r*correction r) volume q (q*Real.exp h):=
    ContinuousOn.intervalIntegrable ((SB_regular c h).continuousOn.mul
      (correction_continuous.mono (by rw [uIcc_of_le ordered];intro r member;exact lt_of_lt_of_le (by norm_num) member.1)))
  have second:IntervalIntegrable (fun r:ℝ=>SBWeight c h r*drive r) volume q (q*Real.exp h):=
    ContinuousOn.intervalIntegrable
      ((continuous_iff_continuousAt.mpr (fun x=>(SB_derivative c h x).continuousAt)).continuousOn.mul
        (drive_continuous.mono (by rw [uIcc_of_le ordered];intro r member;exact lt_of_lt_of_le (by norm_num) member.1)))
  rw [intervalIntegral.integral_add first second] at byParts
  simp_rw [intervalIntegral.integral_of_le ordered] at byParts
  rw [correction_zero,mul_zero,sub_zero] at byParts
  unfold boxProgram
  rw [map_add,map_sub,map_smul,←meanIntegral]
  simp only [map_smul,map_sub,smul_eq_mul] at *
  rw [integral,scaled _ ⟨ordered,le_rfl⟩,scaled q ⟨le_rfl,ordered⟩,correction_zero]
  have calculated:(∫r:ℝ in Ioc q (q*Real.exp h),SBWeight c h r*drive r)=
      -4*(∫r:ℝ in Ioc q (q*Real.exp h),SBWeight c h r*(Real.log (r/q):ℂ)):=by
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards with r
    unfold drive
    ring
  rw [calculated] at byParts
  have balance:=weighted_mean_balance c h nn
  push_cast at balance ⊢
  norm_num only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat,one_div,inv_div] at balance ⊢
  linear_combination (norm:=ring_nf) (meanFunctional C/(1/4:ℂ))*balance+byParts

private theorem original_gap (c:BurnolCompletedMellinCoordinate) :
    Rq (K c:BurnolL2)=burnolRieszStateQuarterInnerRaw c • intervalConstant q := by
  apply Lp.ext
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) (K c:BurnolL2),
    ae_restrict_of_ae (burnolRieszState_ae_raw c),
    Lp.coeFn_smul (burnolRieszStateQuarterInnerRaw c) (intervalConstant q),intervalConstant_coeFn q,
    ae_restrict_mem (measurableSet_symmetricInterval q)] with x restriction raw scalar constant inside
  rw [scalar]
  simp only [Pi.smul_apply,smul_eq_mul,constant,mul_one]
  exact restriction.trans (raw.trans (burnolRieszStateRaw_eq_quarterInner_of_mem c inside))

/-- The original whole reverse source pays its entire K price by the finite annulus. -/
theorem whole_annulus_price (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nn:0≤h) (small:h<Real.log 2) :
    (1/2:ℂ)*inner ℂ (sourceKernel c) (FullUnit.fullReverse c h 1)=
      ∫r:ℝ in Ioc q (q*Real.exp h),SBWeight c h r*
        (star (burnolRieszStatePositiveOuterRaw c r)+star (burnolRieszStateQuarterInnerRaw c)*(Real.log (r/q):ℂ)) := by
  have source:=whole_source_split c h nn small
  have quarter:inner ℂ (K c:BurnolL2) (burnolQuarterZeroExtension (Rq (FullUnit.fullReverse c h 1)))=
      star (burnolRieszStateQuarterInnerRaw c)*(1/2:ℂ)*mu (Rq (FullUnit.fullReverse c h 1)) := by
    have adjoint:=ContinuousLinearMap.adjoint_inner_right Rq (K c:BurnolL2) (Rq (FullUnit.fullReverse c h 1))
    change inner ℂ (K c:BurnolL2) (burnolQuarterZeroExtension (Rq (FullUnit.fullReverse c h 1)))=_ at adjoint
    rw [adjoint,original_gap,inner_smul_left]
    unfold burnolQuarterMeanCoefficient
    have norm:=burnolIntervalConstant_norm_sq (by norm_num : (0:ℝ)<q)
    rw [Complex.ofReal_pow,norm]
    norm_num
    ring
  have outside:=OriginalKExteriorWindowHAction.actual_exterior_cotest c h nn 1
  change inner ℂ (K c:BurnolL2) (exteriorSource c h 1)=OriginalKExteriorWindowHAction.exteriorPrice c h 1 at outside
  have outer:inner ℂ (K c:BurnolL2) (exteriorSource c h 1)=
      2*∫r:ℝ in Ioc q (q*Real.exp h),star (burnolRieszStatePositiveOuterRaw c r)*SBWeight c h r := by
    rw [outside]
    unfold OriginalKExteriorWindowHAction.exteriorPrice
    have ordered:q≤q*Real.exp h:=by nlinarith [Real.one_le_exp_iff.mpr nn]
    rw [intervalIntegral.integral_of_le ordered]
    simp only [OriginalKExteriorWindowHAction.exteriorTestRaw,Matrix.cons_val_one,Matrix.cons_val_zero]
    unfold SBWeight
    rw [←integral_const_mul,←integral_const_mul]
    apply integral_congr_ae
    filter_upwards with r
    change (2:ℂ)*(Real.exp (-h/2):ℂ)*(star (burnolRieszStatePositiveOuterRaw c r)*burnolRieszReturnRaw c (Real.exp (-h)*r))=_
    ring
  rw [sourceKernel_original,source,inner_add_right,quarter,outer,whole_quarter_mean c h nn small]
  have first:IntegrableOn (fun r:ℝ=>star (burnolRieszStatePositiveOuterRaw c r)*SBWeight c h r) (Ioc q (q*Real.exp h)):=by
    have cont:ContinuousOn (fun r:ℝ=>star (burnolRieszStatePositiveOuterRaw c r)*SBWeight c h r) (Icc q (q*Real.exp h)):=by
      intro r member
      have rp:0<r:=lt_of_lt_of_le (by norm_num) member.1
      exact ((OriginalKExteriorWindowHAction.physical_test_outer_continuous c 1 r rp).star.mul
        (SB_derivative c h r).continuousAt).continuousWithinAt
    exact cont.integrableOn_compact isCompact_Icc |>.mono_set Ioc_subset_Icc_self
  have last:IntegrableOn (fun r:ℝ=>star (burnolRieszStateQuarterInnerRaw c)*(SBWeight c h r*(Real.log (r/q):ℂ))) (Ioc q (q*Real.exp h)):=by
    have cont:ContinuousOn (fun r:ℝ=>star (burnolRieszStateQuarterInnerRaw c)*(SBWeight c h r*(Real.log (r/q):ℂ))) (Icc q (q*Real.exp h)):=by
      intro r member
      have rp:0<r:=lt_of_lt_of_le (by norm_num) member.1
      have logarithm:ContinuousAt (fun r:ℝ=>Real.log (r/q)) r:=
        ((continuous_id.div_const q).continuousAt).log (div_ne_zero rp.ne' (by norm_num : q≠0))
      have actual:ContinuousAt (fun r:ℝ=>star (burnolRieszStateQuarterInnerRaw c)*(SBWeight c h r*(Real.log (r/q):ℂ))) r:=
        ((SB_derivative c h r).continuousAt.mul logarithm.ofReal).const_mul _
      exact actual.continuousWithinAt
    exact cont.integrableOn_compact isCompact_Icc |>.mono_set Ioc_subset_Icc_self
  have split:(∫r:ℝ in Ioc q (q*Real.exp h),SBWeight c h r*
      (star (burnolRieszStatePositiveOuterRaw c r)+star (burnolRieszStateQuarterInnerRaw c)*(Real.log (r/q):ℂ)))=
    (∫r:ℝ in Ioc q (q*Real.exp h),star (burnolRieszStatePositiveOuterRaw c r)*SBWeight c h r)+
      star (burnolRieszStateQuarterInnerRaw c)*(∫r:ℝ in Ioc q (q*Real.exp h),SBWeight c h r*(Real.log (r/q):ℂ)) := by
    have body:(fun r:ℝ=>SBWeight c h r*(star (burnolRieszStatePositiveOuterRaw c r)+star (burnolRieszStateQuarterInnerRaw c)*(Real.log (r/q):ℂ)))=
      (fun r:ℝ=>star (burnolRieszStatePositiveOuterRaw c r)*SBWeight c h r+star (burnolRieszStateQuarterInnerRaw c)*(SBWeight c h r*(Real.log (r/q):ℂ))):=by funext r;ring
    rw [body,integral_add first last,integral_const_mul]
  rw [split]
  ring

/-- All remaining terms are the original B, collar, unit and counted source fields. -/
def remainder (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) (h:ℝ) : ℂ :=
  -(((pairedMellinTranslationCharacter c.value h-((Real.exp (h/2):ℂ)+(Real.exp (-h/2):ℂ))/2)*reverseMean c zero+
      (2*q:ℝ)*GapEuler.gapMean q c*(Complex.exp (OriginalKSourceResolventReconstruction.sourceRate c*(h:ℂ))-(Real.exp (-h/2):ℂ)))*
        inner ℂ (sourceKernel c) ConstantDual.seed)+
    (1/2:ℂ)*inner ℂ (sourceKernel c) (collarSource c h)+
    coreCharacterDefect c h*(reverseMean c zero*inner ℂ (sourceKernel c) ConstantDual.seed-
      inner ℂ (sourceKernel c) (elementarySource c))+positionLogPrice c h-
    (1/2:ℂ)*(OriginalKExteriorBCotest.sourcePrice c h+
      centeringMean c h 0*inner ℂ (sourceKernel c) (fourierL2 ConstantDual.seed))

def annulusPrice (c:BurnolCompletedMellinCoordinate) (h:ℝ) : ℂ :=
  ∫r:ℝ in Ioc q (q*Real.exp h),SBWeight c h r*
    (star (burnolRieszStatePositiveOuterRaw c r)+star (burnolRieszStateQuarterInnerRaw c)*(Real.log (r/q):ℂ))

def programmePrice (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) (h:ℝ) : ℂ :=
  remainder c zero h+annulusPrice c h

open private full_loss_source
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.CompleteCountedSource

/-- The complete original Ward consumer uses the new same-W price, with no division by c-star(c). -/
theorem fixedResidual_source (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nn:0≤h) (small:h<Real.log 2) (fixed:h=Real.log stageZeroSonineQ) :
    burnolPaFixedShiftResidual c zero=programmePrice c zero h := by
  have actual:=original_fixedResidual_firstBand_source c zero h nn small.le fixed
  rw [full_loss_source c h nn] at actual
  have calculated:=whole_annulus_price c h nn small
  unfold programmePrice remainder annulusPrice
  linear_combination -actual+calculated

private theorem fixed_small : Real.log stageZeroSonineQ<Real.log 2 := by
  have positive:0<Real.sqrt (3:ℝ):=Real.sqrt_pos.mpr (by norm_num)
  have below:Real.sqrt (3:ℝ)<2:=by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤3)]
  simpa only [stageZeroSonineQ] using Real.log_lt_log positive below

variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "h0" => Real.log stageZeroSonineQ

/-- The existing original programme is consumed, rather than used to construct its remainder. -/
theorem original_programmePrice :
    OriginalSBReverseCompactSource.programmePrice c h0=programmePrice c observation.mathlibZero h0 := by
  have old:=OriginalSBReverseCompactSource.original_fixedResidual_programme observation nontrivial half
  have fresh:=fixedResidual_source c observation.mathlibZero h0
    (Real.log_nonneg (by norm_num [stageZeroSonineQ])) fixed_small rfl
  exact old.symm.trans fresh

theorem original_fixedResidual_programme :
    burnolPaFixedShiftResidual c observation.mathlibZero=programmePrice c observation.mathlibZero h0 :=
  fixedResidual_source c observation.mathlibZero h0
    (Real.log_nonneg (by norm_num [stageZeroSonineQ])) fixed_small rfl

end OriginalSBWholeAnnulusPrice
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
