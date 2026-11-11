import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.SBReverseCompactSource

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalSBQuarterMeanSource
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction OriginalKCoefficientBFiniteAction OriginalKExteriorCoPoissonAction
open OriginalFullLossRAction OriginalReverseCoreJumpMean OriginalSBReverseCompactSource
open scoped InnerProductSpace Topology
local notation "q" => (1/4:ℝ)
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "Rq" => burnolQuarterRestriction
local notation "mu" => burnolQuarterMeanCoefficient
local instance quarterFinite : IsFiniteMeasure ((volume:Measure ℝ).restrict (symmetricInterval q)) where
  measure_univ_lt_top:=lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top q)

open private gamma unitPrice unitPrice_ne_zero unitCurrent boxScale boxProgram box_family_integrable
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.UnitRProgram
open private SBWeight SBSlope SB_regular SB_derivative
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FullLossRAction
open private scale_raw unitCurrent_raw
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.ReverseCoreJumpMean
open private scale_profile weighted_mean_balance unit_profile_measurable
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.SBReverseCompactSource
open private even_half_integral
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKExteriorCoPoissonAction.WindowH.Source

private theorem c_ne (c:BurnolCompletedMellinCoordinate) : c.value≠0 := by
  intro zero
  have real:=congrArg Complex.re zero
  simp only [Complex.zero_re] at real
  linarith [c.rightHalf]

private theorem one_ne (c:BurnolCompletedMellinCoordinate) : 1-c.value≠0 := by
  intro zero
  have real:=congrArg Complex.re (sub_eq_zero.mp zero)
  simp only [Complex.one_re] at real
  linarith [c.belowOne]

/-- Both original arithmetic channels are still present on this complete first cell. -/
private theorem unit_profile_one_cell (c:BurnolCompletedMellinCoordinate) (s:ℝ)
    (lo:q/2<s) (hi:s≤q) :
    unitCurrentProfile c s= -2*q/((1-c.value)*(s:ℂ))+
      (2/c.value)*(((q/s:ℝ):ℂ)^c.value-1) := by
  have sp:0<s:=by linarith
  have sn:(s:ℂ)≠0:=Complex.ofReal_ne_zero.mpr sp.ne'
  have lower:1≤q/s:=(le_div_iff₀ sp).mpr (by simpa using hi)
  have upper:q/s<2:=(div_lt_iff₀ sp).mpr (by linarith)
  have natFloor:⌊q/s⌋₊=1:=by
    apply (Nat.floor_eq_iff' (by norm_num : (1:ℕ)≠0)).mpr
    norm_num only [Nat.cast_one]
    exact ⟨lower,by simpa using upper⟩
  have intFloor:⌊q/s⌋=(1:ℤ):=by
    apply Int.floor_eq_iff.mpr
    norm_num only [Int.cast_one]
    exact ⟨lower,by simpa using upper⟩
  have gap:=GapEuler.gapMean_primitive q (by norm_num) (barC c)
  simp only [OriginalPrimitiveRankBalance.conjugateCoordinate,star_star] at gap
  have power:(q:ℂ)^(-c.value)*(((q/s:ℝ):ℂ)^c.value)=(s:ℂ)^(-c.value) := by
    rw [Complex.ofReal_div q s,Complex.div_cpow_ofReal_nonneg (by norm_num : (0:ℝ)≤q) sp.le,
      Complex.cpow_neg,Complex.cpow_neg]
    have qp:(q:ℂ)^c.value≠0:=Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
    field_simp
  have priced:=unitPrice_ne_zero c
  unfold unitCurrentProfile
  apply (mul_left_cancel₀ priced)
  rw [mul_inv_cancel_left₀ priced]
  simp only [ConstantDual.sawtoothRaw,elementaryReverseRaw,DualSourceRaw.channels,
    abs_of_pos sp,natFloor,Finset.Icc_self,Finset.sum_singleton,Int.fract,intFloor,
    Int.cast_one,Nat.cast_one,one_mul]
  unfold unitPrice gamma
  simp only [OriginalPrimitiveRankBalance.conjugateCoordinate,star_star]
  have gapValue:GapEuler.gapMean q (barC c)=(q:ℂ)^(-c.value)/(2*(1-c.value)):=by
    apply (eq_div_iff (mul_ne_zero (by norm_num) (one_ne c))).mpr
    dsimp only [OriginalPrimitiveRankBalance.conjugateCoordinate]
    linear_combination (norm:=ring_nf) 2*gap
  simp only [OriginalPrimitiveRankBalance.conjugateCoordinate] at gapValue
  rw [gapValue,←power]
  push_cast
  field_simp [c_ne c,one_ne c,sn]
  ring

private theorem inverse_ratio_power (a b:ℝ) (ap:0<a) (bp:0<b) (z:ℂ) :
    (((a/b:ℝ):ℂ)^z)=(((b/a:ℝ):ℂ)^(-z)) := by
  have inverse:a/b=(b/a)⁻¹:=by field_simp
  rw [inverse,Complex.ofReal_inv,Complex.inv_cpow_ofReal_nonneg (div_nonneg bp.le ap.le),
    Complex.cpow_neg]

private def unitPrimitive (c:BurnolCompletedMellinCoordinate) (s:ℝ) : ℂ :=
  -(2/c.value)*(s:ℂ)-(2*(q:ℂ)/(1-c.value))*(Real.log (s/q):ℂ)+
    (2*(q:ℂ)/(c.value*(1-c.value)))*(((s/q:ℝ):ℂ)^(1-c.value))

private theorem unit_primitive_derivative (c:BurnolCompletedMellinCoordinate) (s:ℝ)
    (sp:0<s) : HasDerivAt (unitPrimitive c)
      (-2*q/((1-c.value)*(s:ℂ))+(2/c.value)*(((q/s:ℝ):ℂ)^c.value-1)) s := by
  have ratio:HasDerivAt (fun x:ℝ=>x/q) (1/q) s:=(hasDerivAt_id s).div_const q
  have logarithm:=((Real.hasDerivAt_log (div_ne_zero sp.ne' (by norm_num : q≠0))).comp s ratio).ofReal_comp
  have power:=(hasDerivAt_ofReal_cpow_const (div_ne_zero sp.ne' (by norm_num : q≠0))
    (one_ne c)).scomp s ratio
  have generated:=(((Complex.ofRealCLM.hasDerivAt.const_mul (-(2/c.value))).sub
    (logarithm.const_mul (2*(q:ℂ)/(1-c.value)))).add
      (power.const_mul (2*(q:ℂ)/(c.value*(1-c.value)))))
  convert! generated using 1
  rw [inverse_ratio_power q s (by norm_num) sp]
  simp only [Complex.ofRealCLM_apply,Complex.real_smul]
  push_cast
  norm_num
  field_simp [c_ne c,one_ne c,Complex.ofReal_ne_zero.mpr sp.ne']
  ring

private def bandCorrection (c:BurnolCompletedMellinCoordinate) (r:ℝ) : ℂ :=
  -(2/(1-c.value))*
    (((r/q:ℝ):ℂ)*(Real.log (r/q):ℂ)-(r/q:ℝ)+1+
      ((((r/q:ℝ):ℂ)^c.value)-1)/c.value)

private def bandDrive (c:BurnolCompletedMellinCoordinate) (r:ℝ) : ℂ :=
  -(2/((q:ℂ)*(1-c.value)))*((Real.log (r/q):ℂ)+(((r/q:ℝ):ℂ)^(c.value-1)))

private theorem band_correction_zero (c:BurnolCompletedMellinCoordinate) : bandCorrection c q=0 := by
  simp [bandCorrection]

private theorem band_correction_derivative (c:BurnolCompletedMellinCoordinate) (r:ℝ)
    (rp:0<r) : HasDerivAt (bandCorrection c) (bandDrive c r) r := by
  have ratio:HasDerivAt (fun x:ℝ=>x/q) (1/q) r:=(hasDerivAt_id r).div_const q
  have logarithm:=((Real.hasDerivAt_log (div_ne_zero rp.ne' (by norm_num : q≠0))).comp r ratio).ofReal_comp
  have power:=(hasDerivAt_ofReal_cpow_const (div_ne_zero rp.ne' (by norm_num : q≠0))
    (c_ne c)).scomp r ratio
  have generated:=((((ratio.ofReal_comp.mul logarithm).sub ratio.ofReal_comp).add_const 1).add
    ((power.sub_const 1).div_const c.value)).const_mul (-(2/(1-c.value)))
  convert! generated using 1
  simp only [Function.comp_apply,Complex.real_smul]
  push_cast
  unfold bandDrive
  push_cast
  norm_num
  field_simp [c_ne c,one_ne c,Complex.ofReal_ne_zero.mpr rp.ne']
  ring

private theorem band_correction_continuous (c:BurnolCompletedMellinCoordinate) :
    ContinuousOn (bandCorrection c) (Ioi 0) :=
  fun r inside=>(band_correction_derivative c r inside).continuousAt.continuousWithinAt

private theorem band_drive_continuous (c:BurnolCompletedMellinCoordinate) :
    ContinuousOn (bandDrive c) (Ioi 0) := by
  intro r positive
  have ratio:ContinuousAt (fun r:ℝ=>r/q) r:=by fun_prop
  have logarithm:ContinuousAt (fun r:ℝ=>Real.log (r/q)) r:=ratio.log (div_ne_zero positive.ne' (by norm_num : q≠0))
  have outer:ContinuousAt (fun y:ℝ=>(y:ℂ)^(c.value-1)) (r/q):=
    Complex.continuousAt_ofReal_cpow_const (r/q) (c.value-1)
      (Or.inr (div_ne_zero positive.ne' (by norm_num : q≠0)))
  have power:ContinuousAt (fun r:ℝ=>((r/q:ℝ):ℂ)^(c.value-1)) r:=by
    exact outer.comp (f:=fun y:ℝ=>y/q) (x:=r) ratio
  have actual:ContinuousAt (bandDrive c) r:=
    (logarithm.ofReal.add power).const_mul (-(2/((q:ℂ)*(1-c.value))))
  exact actual.continuousWithinAt

private def meanFunctional : BurnolL2→L[ℂ]ℂ :=
  ((2:ℂ) • innerSL ℂ (intervalConstant q)).comp Rq

private theorem mean_functional (v:BurnolL2) : meanFunctional v=mu (Rq v) := by
  have norm:=burnolIntervalConstant_norm_sq (by norm_num : (0:ℝ)<q)
  have real:‖intervalConstant q‖^2=(1/2:ℝ):=by
    have read:‖intervalConstant q‖^2=2*q:=by exact_mod_cast norm
    linarith
  unfold meanFunctional burnolQuarterMeanCoefficient
  simp only [ContinuousLinearMap.comp_apply,smul_apply,innerSL_apply_apply,
    smul_eq_mul,real]
  norm_num
  ring

private theorem mean_half_raw (v:BurnolL2) (raw:ℝ→ℂ)
    (actual:(v:ℝ→ℂ)=ᵐ[volume]raw) (even:∀x,raw (-x)=raw x) :
    meanFunctional v=4*∫x:ℝ in (0:ℝ)..q,raw x := by
  have read:((Rq v:BurnolQuarterIntervalL2):ℝ→ℂ)=ᵐ[volume.restrict (symmetricInterval q)]raw:=
    (LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) v).trans (actual.filter_mono (ae_mono Measure.restrict_le_self))
  have integrable:IntegrableOn raw (symmetricInterval q):=
    ((Lp.memLp (Rq v)).integrable (by norm_num)).congr read
  rw [mean_functional,Constructor.mean_integral,integral_congr_ae read,
    even_half_integral raw integrable even,←intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤q)]
  ring

private theorem unit_profile_even (c:BurnolCompletedMellinCoordinate) (x:ℝ) :
    unitCurrentProfile c (-x)=unitCurrentProfile c x := by
  simp only [unitCurrentProfile,ConstantDual.sawtoothRaw,elementaryReverseRaw,DualSourceRaw.channels,abs_neg]

private theorem unit_profile_integrable (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) : IntervalIntegrable (unitCurrentProfile c) volume 0 q := by
  have raw:=unitCurrent_raw c zero
  have read:((Rq (unitCurrent c zero):BurnolQuarterIntervalL2):ℝ→ℂ)=ᵐ[volume.restrict (symmetricInterval q)]unitCurrentProfile c:=
    (LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) (unitCurrent c zero)).trans
      (raw.filter_mono (ae_mono Measure.restrict_le_self))
  have integrable:IntegrableOn (unitCurrentProfile c) (symmetricInterval q):=
    ((Lp.memLp (Rq (unitCurrent c zero))).integrable (by norm_num)).congr read
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0:ℝ)≤q)).mpr
  exact integrable.mono_set (by intro x inside;exact ⟨by linarith [inside.1],inside.2⟩)

private theorem band_correction_integral (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (r:ℝ) (lo:q≤r) (hi:r<2*q) :
    (4:ℂ)*(r/q:ℝ)*(∫s:ℝ in (q*q/r)..q,unitCurrentProfile c s)=bandCorrection c r := by
  have rp:0<r:=lt_of_lt_of_le (by norm_num) lo
  have lp:q/2<q*q/r:=(lt_div_iff₀ rp).mpr (by nlinarith)
  have lq:q*q/r≤q:=(div_le_iff₀ rp).mpr (by nlinarith)
  have ordered:0≤q*q/r:=by positivity
  have integrable:IntervalIntegrable (unitCurrentProfile c) volume (q*q/r) q:=
    (unit_profile_integrable c zero).mono_set (by
      rw [uIcc_of_le lq,uIcc_of_le (by norm_num : (0:ℝ)≤q)]
      exact Icc_subset_Icc ordered le_rfl)
  have derivatives:∀s∈Ioo (q*q/r) q, HasDerivAt (unitPrimitive c) (unitCurrentProfile c s) s:=by
    intro s inside
    rw [unit_profile_one_cell c s (lp.trans inside.1) inside.2.le]
    exact unit_primitive_derivative c s (by linarith [inside.1])
  have primitive:=intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le lq
    (show ContinuousOn (unitPrimitive c) (Icc (q*q/r) q) from fun s inside=>
      (unit_primitive_derivative c s (by linarith [inside.1])).continuousAt.continuousWithinAt)
    derivatives integrable
  rw [primitive]
  have ratio:q*q/r/q=q/r:=by field_simp
  have power:(((q/r:ℝ):ℂ)^(1-c.value))=(((r/q:ℝ):ℂ)^(c.value-1)) := by
    rw [inverse_ratio_power q r (by norm_num) rp]
    congr 1
    ring
  have shift:((r/q:ℝ):ℂ)*(((r/q:ℝ):ℂ)^(c.value-1))=(((r/q:ℝ):ℂ)^c.value) := by
    have rn:((r/q:ℝ):ℂ)≠0:=Complex.ofReal_ne_zero.mpr (div_ne_zero rp.ne' (by norm_num : q≠0))
    calc
      _=(((r/q:ℝ):ℂ)^(c.value-1))*(((r/q:ℝ):ℂ)^1):=by rw [Complex.cpow_one];ring
      _=(((r/q:ℝ):ℂ)^((c.value-1)+1)):=(Complex.cpow_add _ _ rn).symm
      _=_:=by congr 1;ring
  unfold unitPrimitive bandCorrection
  rw [ratio,power,Real.log_div (by norm_num : q≠0) rp.ne',Real.log_div rp.ne' (by norm_num : q≠0)]
  simp only [div_self (by norm_num : q≠0),Complex.ofReal_one,Complex.one_cpow,Real.log_one]
  rw [←shift]
  push_cast
  field_simp [c_ne c,one_ne c,Complex.ofReal_ne_zero.mpr rp.ne']
  ring

private theorem scale_mean (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (r:ℝ) (lo:q≤r) (hi:r<2*q) :
    meanFunctional (boxScale (unitCurrent c zero) r)=
      (r/q:ℝ)*meanFunctional (unitCurrent c zero)-bandCorrection c r := by
  have rp:0<r:=lt_of_lt_of_le (by norm_num) lo
  have scaled:((boxScale (unitCurrent c zero) r):ℝ→ℂ)=ᵐ[volume]
      fun x=>unitCurrentProfile c (q*x/r):=by
    filter_upwards [scale_raw r _ _ (unitCurrent_raw c zero)] with x read
    exact read.trans (scale_profile r rp _ x)
  have even:∀x:ℝ,unitCurrentProfile c (q*(-x)/r)=unitCurrentProfile c (q*x/r):=by
    intro x
    rw [mul_neg,neg_div,unit_profile_even]
  rw [mean_half_raw _ _ scaled even,mean_half_raw _ _ (unitCurrent_raw c zero) (unit_profile_even c)]
  have rewrite_integral:(∫x:ℝ in (0:ℝ)..q,unitCurrentProfile c (q*x/r))=
      (r/q:ℝ)*(∫x:ℝ in (0:ℝ)..(q*q/r),unitCurrentProfile c x) := by
    have body:(fun x:ℝ=>unitCurrentProfile c (q*x/r))=
        (fun x:ℝ=>unitCurrentProfile c ((q/r)*x)):=by funext x;congr 1;ring
    rw [body,intervalIntegral.integral_comp_mul_left _ (div_ne_zero (by norm_num) rp.ne')]
    simp only [mul_zero,Complex.real_smul]
    congr 1
    · field_simp
    · congr 1
      ring
  rw [rewrite_integral]
  have lq:q*q/r≤q:=(div_le_iff₀ rp).mpr (by nlinarith)
  have ordered:0≤q*q/r:=by positivity
  have whole:=unit_profile_integrable c zero
  have first:IntervalIntegrable (unitCurrentProfile c) volume 0 (q*q/r):=
    whole.mono_set (by
      rw [uIcc_of_le ordered,uIcc_of_le (by norm_num : (0:ℝ)≤q)]
      exact Icc_subset_Icc le_rfl lq)
  have last:IntervalIntegrable (unitCurrentProfile c) volume (q*q/r) q:=
    whole.mono_set (by
      rw [uIcc_of_le lq,uIcc_of_le (by norm_num : (0:ℝ)≤q)]
      exact Icc_subset_Icc ordered le_rfl)
  have split:=intervalIntegral.integral_add_adjacent_intervals first last
  have computed:=band_correction_integral c zero r lo hi
  linear_combination (norm:=ring_nf) 4*(r/q:ℝ)*split-computed

/-- The complete source balance cancels the unknown whole unit mass before this finite read. -/
theorem actual_source_quarter_mean (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nn:0≤h) (small:h<Real.log 2) :
    mu (Rq (sourceField c zero h))=
      (2/((q:ℂ)*(1-c.value)))*∫r:ℝ in Ioc q (q*Real.exp h),
        SBWeight c h r*((Real.log (r/q):ℂ)+(((r/q:ℝ):ℂ)^(c.value-1))) := by
  have ordered:q≤q*Real.exp h:=by nlinarith [Real.one_le_exp_iff.mpr nn]
  have bound:q*Real.exp h<2*q:=by
    have expBound:Real.exp h<2:=by simpa only [Real.exp_log (by norm_num : (0:ℝ)<2)] using Real.exp_lt_exp.mpr small
    nlinarith
  have meanIntegral:=meanFunctional.integral_comp_comm
    (box_family_integrable q (q*Real.exp h) (SBSlope c h) (by norm_num) (SB_regular c h).continuousOn (unitCurrent c zero))
  have scaled (r:ℝ) (inside:r∈Icc q (q*Real.exp h)):=
    scale_mean c zero r inside.1 (inside.2.trans_lt bound)
  have integral:(∫r:ℝ in Ioc q (q*Real.exp h),SBSlope c h r*
      (meanFunctional (boxScale (unitCurrent c zero) r)-meanFunctional (boxScale (unitCurrent c zero) q)))=
      (∫r:ℝ in Ioc q (q*Real.exp h),SBSlope c h r*((r:ℂ)-q))*(meanFunctional (unitCurrent c zero)/(q:ℂ))-
      ∫r:ℝ in Ioc q (q*Real.exp h),SBSlope c h r*bandCorrection c r := by
    have first:IntegrableOn (fun r:ℝ=>SBSlope c h r*((r:ℂ)-q)) (Ioc q (q*Real.exp h)):=
      (((SB_regular c h).mul (Complex.continuous_ofReal.sub continuous_const)).integrableOn_Icc).mono_set Ioc_subset_Icc_self
    have last:IntegrableOn (fun r:ℝ=>SBSlope c h r*bandCorrection c r) (Ioc q (q*Real.exp h)):=
      (((SB_regular c h).continuousOn.mul ((band_correction_continuous c).mono (by
        intro r inside;exact lt_of_lt_of_le (by norm_num) inside.1))).integrableOn_Icc).mono_set Ioc_subset_Icc_self
    rw [←integral_mul_const,←integral_sub (first.mul_const _) last]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro r inside
    dsimp only
    rw [scaled r ⟨inside.1.le,inside.2⟩,scaled q ⟨le_rfl,ordered⟩,band_correction_zero]
    push_cast
    ring
  have balance:=weighted_mean_balance c h nn
  have byParts:=intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt
    (a:=q) (b:=q*Real.exp h) (u:=SBWeight c h) (u':=SBSlope c h)
    (v:=bandCorrection c) (v':=bandDrive c)
    (continuous_iff_continuousAt.mpr (fun x=>(SB_derivative c h x).continuousAt)).continuousOn
    ((band_correction_continuous c).mono (by rw [uIcc_of_le ordered];intro r inside;exact lt_of_lt_of_le (by norm_num) inside.1))
    (fun r _=>SB_derivative c h r)
    (fun r inside=>band_correction_derivative c r (by
      rw [min_eq_left ordered] at inside
      exact lt_trans (by norm_num) inside.1))
    ((SB_regular c h).intervalIntegrable _ _)
    (ContinuousOn.intervalIntegrable ((band_drive_continuous c).mono (by
      rw [uIcc_of_le ordered];intro r inside;exact lt_of_lt_of_le (by norm_num) inside.1)))
  have first:IntervalIntegrable (fun r:ℝ=>SBSlope c h r*bandCorrection c r) volume q (q*Real.exp h):=
    ContinuousOn.intervalIntegrable ((SB_regular c h).continuousOn.mul
      ((band_correction_continuous c).mono (by rw [uIcc_of_le ordered];intro r inside;exact lt_of_lt_of_le (by norm_num) inside.1)))
  have second:IntervalIntegrable (fun r:ℝ=>SBWeight c h r*bandDrive c r) volume q (q*Real.exp h):=
    ContinuousOn.intervalIntegrable
      ((continuous_iff_continuousAt.mpr (fun x=>(SB_derivative c h x).continuousAt)).continuousOn.mul
        ((band_drive_continuous c).mono (by rw [uIcc_of_le ordered];intro r inside;exact lt_of_lt_of_le (by norm_num) inside.1)))
  rw [intervalIntegral.integral_add first second] at byParts
  simp_rw [intervalIntegral.integral_of_le ordered] at byParts
  rw [band_correction_zero,mul_zero,sub_zero] at byParts
  rw [←mean_functional]
  unfold sourceField boxProgram
  rw [map_add,map_sub,map_smul,←meanIntegral]
  simp only [map_smul,map_sub,smul_eq_mul] at *
  rw [integral,scaled _ ⟨ordered,le_rfl⟩,scaled q ⟨le_rfl,ordered⟩,band_correction_zero]
  have drive:(∫r:ℝ in Ioc q (q*Real.exp h),SBWeight c h r*bandDrive c r)=
      -(2/((q:ℂ)*(1-c.value)))*(∫r:ℝ in Ioc q (q*Real.exp h),SBWeight c h r*
        ((Real.log (r/q):ℂ)+(((r/q:ℝ):ℂ)^(c.value-1)))) := by
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards with r
    unfold bandDrive
    ring
  rw [drive] at byParts
  push_cast at balance byParts ⊢
  norm_num only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat,one_div,inv_div] at balance byParts ⊢
  linear_combination (norm:=ring_nf) (meanFunctional (unitCurrent c zero)/(1/4:ℂ))*balance+byParts

theorem actual_R_quarter_mean (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nn:0≤h) (small:h<Real.log 2) :
    mu (Rq (burnolDirectRightResolventCLM c (FullUnit.fullReverse c h 1)))=
      (2/((q:ℂ)*(1-c.value)))*∫r:ℝ in Ioc q (q*Real.exp h),
        SBWeight c h r*((Real.log (r/q):ℂ)+(((r/q:ℝ):ℂ)^(c.value-1))) := by
  rw [actual_R_source c zero h nn]
  exact actual_source_quarter_mean c zero h nn small

end OriginalSBQuarterMeanSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
