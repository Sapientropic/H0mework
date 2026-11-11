import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.GammaMellin

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2800000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.ComplementMoment
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Tail
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.RegularForward OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.PositionPrice
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.Regularity OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.ReturnMellin
open scoped Topology InnerProductSpace
open private pweight pweight_summable channel channel_bound channel_summable forward_reindex
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Forward
open private local_growth from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.Regularity
open private logSource_zero log_top_bound from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Source
open private compact_memLp compact_origin from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.ReturnMellin
local notation "q" => (1/4:ℝ)
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "νq" => volume.restrict (Ioc (0:ℝ) q)

def logWeight (w:ℂ) (j:ℕ) (x:ℝ):ℂ := (x:ℂ)^(-w)*(Real.log x:ℂ)^j

def quarterMoment (raw:ℝ→ℂ) (w:ℂ) (j:ℕ):ℂ :=
  ∫x:ℝ in (0:ℝ)..q,logWeight w j x*raw x

private theorem compact_mellin_read (raw:ℝ→ℂ) (w:ℂ) (j:ℕ):
    mellin (logSource (compactRaw raw) j) (1-w)=quarterMoment raw w j:=by
  unfold mellin quarterMoment
  simp only [smul_eq_mul,show 1-w-1= -w by ring]
  have cut:EqOn (fun x:ℝ=>(x:ℂ)^(-w)*logSource (compactRaw raw) j x)
      ((Ioc (0:ℝ) q).indicator (fun x:ℝ=>logWeight w j x*raw x)) (Ioi 0):=by
    intro x positive
    change 0<x at positive
    dsimp only
    by_cases below:x≤q
    · rw [logSource,compactRaw,indicator_of_mem (show x∈symmetricInterval q from ⟨by linarith,below⟩),
        indicator_of_mem (show x∈Ioc (0:ℝ) q from ⟨positive,below⟩)]
      simp only [logWeight,Complex.real_smul,Complex.ofReal_pow]
      ring
    · rw [logSource,compactRaw,indicator_of_notMem (show x∉symmetricInterval q from fun hx=>below hx.2),
        smul_zero,mul_zero,indicator_of_notMem (show x∉Ioc (0:ℝ) q from fun hx=>below hx.2)]
  rw [setIntegral_congr_fun measurableSet_Ioi cut,integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc,inter_eq_left.mpr Ioc_subset_Ioi_self,
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤q)]

private theorem weighted_integrable (raw:ℝ→ℂ) (regular:Continuous raw)
    (w:ℂ) (j:ℕ) (below:w.re<1):
    Integrable (fun x:ℝ=>logWeight w j x*raw x) νq:=by
  have source:=actual_compact_log_mellin raw regular j (1-w)
    (by simp only [sub_re,one_re];linarith)
  change IntegrableOn (fun x:ℝ=>(x:ℂ)^((1-w)-1) • logSource (compactRaw raw) j x) (Ioi 0) at source
  apply (source.mono_set Ioc_subset_Ioi_self).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x inside
  rw [show (1-w)-1= -w by ring,smul_eq_mul,logSource,compactRaw,
    indicator_of_mem (show x∈symmetricInterval q from ⟨by linarith [inside.1],inside.2⟩)]
  simp only [logWeight,Complex.real_smul,Complex.ofReal_pow]
  ring

private theorem weight_integrable (w:ℂ) (j:ℕ) (below:w.re<1):
    Integrable (logWeight w j) νq:=by
  simpa only [mul_one] using weighted_integrable (fun _:ℝ=>(1:ℂ)) continuous_const w j below

private def weightedTerm (c:BurnolCompletedMellinCoordinate) (w:ℂ) (j n:ℕ) (x:ℝ):ℂ:=
  logWeight w j x*channel (regularLocal c) n x

private theorem term_envelope (c:BurnolCompletedMellinCoordinate) (L:ℝ) (nonnegative:0≤L)
    (growth:∀x:ℝ,‖regularLocal c x‖≤L*|x|) (w:ℂ) (j n:ℕ) (x:ℝ) (inside:x∈Ioc (0:ℝ) q):
    ‖weightedTerm c w j n x‖≤(L*q*pweight n)*‖logWeight w j x‖:=by
  rw [weightedTerm,norm_mul]
  have bound:‖channel (regularLocal c) n x‖≤L*q*pweight n:=by
    apply (channel_bound _ L growth n x).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by simpa only [abs_of_pos inside.1] using inside.2) nonnegative)
      (by unfold pweight;positivity)
  calc
    _≤‖logWeight w j x‖*(L*q*pweight n):=mul_le_mul_of_nonneg_left bound (norm_nonneg _)
    _=_:=by ring

private theorem term_integrable (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (w:ℂ) (j n:ℕ) (below:w.re<1):Integrable (weightedTerm c w j n) νq:=by
  obtain ⟨L,nonnegative,lip⟩:=actual_regular_local_lipschitz c
  have growth:=local_growth c zero L lip
  have regular:Continuous (channel (regularLocal c) n):=by
    exact continuous_const.mul ((actual_regular_local_continuous c).comp (continuous_id.div_const _))
  apply ((weight_integrable w j below).norm.const_mul (L*q*pweight n)).mono'
    ((weight_integrable w j below).aestronglyMeasurable.mul regular.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x inside
  exact term_envelope c L nonnegative growth w j n x inside

private theorem norm_integral_summable (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (w:ℂ) (j:ℕ) (below:w.re<1):
    Summable (fun n:ℕ=>∫x:ℝ,‖weightedTerm c w j n x‖ ∂νq):=by
  obtain ⟨L,nonnegative,lip⟩:=actual_regular_local_lipschitz c
  have growth:=local_growth c zero L lip
  apply (pweight_summable.mul_left (L*q*(∫x:ℝ,‖logWeight w j x‖ ∂νq))).of_nonneg_of_le
    (fun n=>integral_nonneg (fun x=>norm_nonneg _))
  intro n
  calc
    _≤∫x:ℝ,(L*q*pweight n)*‖logWeight w j x‖ ∂νq:=by
      apply integral_mono_ae (term_integrable c zero w j n below).norm
        ((weight_integrable w j below).norm.const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x inside
      exact term_envelope c L nonnegative growth w j n x inside
    _=_:=by rw [integral_const_mul];ring

private theorem term_integral_change (c:BurnolCompletedMellinCoordinate) (w:ℂ) (j n:ℕ):
    (∫x:ℝ in (0:ℝ)..q,weightedTerm c w j n x)=
      (((n+1:ℕ):ℂ)^(-w))*(∫u:ℝ in (0:ℝ)..(q/(n+1:ℕ)),
        (u:ℂ)^(-w)*(Real.log ((n+1:ℕ)*u):ℂ)^j*regularRaw c u):=by
  let N:ℝ:=(n+1:ℕ)
  have positive:0<N:=by dsimp [N];positivity
  let f:ℝ→ℂ:=fun u=>(u:ℂ)^(-w)*(Real.log (N*u):ℂ)^j*regularLocal c u
  have field:(∫x:ℝ in (0:ℝ)..q,weightedTerm c w j n x)=
      ((N:ℂ)^(-w)*(N:ℂ)⁻¹)*(∫x:ℝ in (0:ℝ)..q,f (x/N)):=by
    rw [←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro x inside
    have xp:0<x/N:=div_pos inside.1 positive
    have same:N*(x/N)=x:=mul_div_cancel₀ x positive.ne'
    have power:(x:ℂ)^(-w)=(N:ℂ)^(-w)*((x/N:ℝ):ℂ)^(-w):=by
      rw [←Complex.mul_cpow_ofReal_nonneg positive.le xp.le,←Complex.ofReal_mul,same]
    dsimp only [weightedTerm,logWeight,channel,f]
    rw [same,power]
    change (N:ℂ)^(-w)*((x/N:ℝ):ℂ)^(-w)*(Real.log x:ℂ)^j*
      ((N:ℂ)⁻¹*regularLocal c (x/N))=_
    ring
  rw [field,intervalIntegral.integral_comp_div f positive.ne',zero_div,Complex.real_smul]
  have coefficient:(N:ℂ)^(-w)*(N:ℂ)⁻¹*(N:ℂ)=(N:ℂ)^(-w):=by
    rw [mul_assoc,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr positive.ne'),mul_one]
  rw [←mul_assoc,coefficient]
  congr 1
  apply intervalIntegral.integral_congr_Ioo_of_le (by positivity)
  intro u inside
  have one:1≤N:=by dsimp [N];norm_cast;omega
  have uq:u<q:=(inside.2.trans_le (div_le_self (by norm_num) one))
  simp only [f,regularLocal,abs_of_pos inside.1,min_eq_right uq.le]
  rfl

def sourceTerm (c:BurnolCompletedMellinCoordinate) (w:ℂ) (j n:ℕ):ℂ:=
  (((n+1:ℕ):ℂ)^(-w))*(∫u:ℝ in (0:ℝ)..(q/(n+1:ℕ)),
    (u:ℂ)^(-w)*(Real.log ((n+1:ℕ)*u):ℂ)^j*regularRaw c u)

/-- The regular source's linear head pays absolute integration of the entire arithmetic bank. -/
theorem actual_bank_log_hasSum (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (w:ℂ) (j:ℕ) (below:w.re<1):
    HasSum (sourceTerm c w j) (quarterMoment (quarterBankRaw c) w j):=by
  have summed:=hasSum_integral_of_summable_integral_norm
    (fun n=>term_integrable c zero w j n below) (norm_integral_summable c zero w j below)
  have terms:(fun n:ℕ=>∫x:ℝ,weightedTerm c w j n x ∂νq)=sourceTerm c w j:=by
    funext n
    rw [←intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤q),term_integral_change]
    rfl
  rw [terms] at summed
  have whole:(∫x:ℝ,(∑'n:ℕ,weightedTerm c w j n x) ∂νq)=quarterMoment (quarterBankRaw c) w j:=by
    rw [quarterMoment,intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤q)]
    apply integral_congr_ae
    filter_upwards with x
    simp only [weightedTerm,quarterBankRaw,forward_reindex,tsum_mul_left]
  exact whole ▸ summed

theorem actual_bank_log_absolute (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (w:ℂ) (j:ℕ) (below:w.re<1):Summable (fun n:ℕ=>‖sourceTerm c w j n‖):=by
  apply (norm_integral_summable c zero w j below).of_nonneg_of_le (fun n=>norm_nonneg _)
  intro n
  rw [←show (∫x:ℝ in (0:ℝ)..q,weightedTerm c w j n x)=sourceTerm c w j n from
    term_integral_change c w j n,intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤q)]
  exact norm_integral_le_integral_norm _

/-- The full logarithmic family retains the original quarter mean and the S² return. -/
theorem actual_inverse_log_moment (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (w:ℂ) (j:ℕ) (below:w.re<1):
    quarterMoment (inverseRaw c zero) w j=
      (∑'n:ℕ,sourceTerm c w j n)-
        burnolQuarterMeanCoefficient (forwardQuarter c zero)*quarterMoment (fun _:ℝ=>1) w j+
        mellin (logSource (returnRaw (S (sourceInverse c zero))) j) (1-w):=by
  rw [returnRaw,compact_mellin_read]
  have bankDomain:=weighted_integrable _ (actual_quarter_bank_continuous c zero) w j below
  have constantDomain:=(weight_integrable w j below).mul_const
    (burnolQuarterMeanCoefficient (forwardQuarter c zero))
  have returnDomain:=weighted_integrable (burnolMeanZeroFourierRaw (S (sourceInverse c zero)))
    ((burnolRadiusTruncatedFourierRaw_continuous _).sub continuous_const) w j below
  have meanSplit:quarterMoment (inverseRaw c zero) w j=
      quarterMoment (quarterBankRaw c) w j-
        burnolQuarterMeanCoefficient (forwardQuarter c zero)*quarterMoment (fun _:ℝ=>1) w j+
        quarterMoment (burnolMeanZeroFourierRaw (S (sourceInverse c zero))) w j:=by
    simp only [quarterMoment,intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤q),
      inverseRaw,mul_add,mul_sub]
    have added:=integral_add (bankDomain.sub constantDomain) returnDomain
    simp only [Pi.sub_apply] at added
    rw [added,integral_sub bankDomain constantDomain,integral_mul_const]
    simp only [mul_one]
    ring
  rw [meanSplit,(actual_bank_log_hasSum c zero w j below).tsum_eq]

private theorem constant_moment (w:ℂ) (below:w.re<1):
    quarterMoment (fun _:ℝ=>(1:ℂ)) w 0=(q:ℂ)^(1-w)/(1-w):=by
  simp only [quarterMoment,logWeight,pow_zero,mul_one]
  rw [integral_cpow (Or.inl (by simp only [neg_re];linarith))]
  have nonzero:1-w≠0:=by intro eq;have re:=congrArg Complex.re eq;simp only [sub_re,one_re,zero_re] at re;linarith
  rw [show -w+1=1-w by ring,Complex.ofReal_zero,Complex.zero_cpow nonzero,sub_zero]

theorem actual_inverse_moment (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (w:ℂ) (below:w.re<1):
    (∫x:ℝ in (0:ℝ)..q,(x:ℂ)^(-w)*inverseRaw c zero x)=
      (∑'n:ℕ,(((n+1:ℕ):ℂ)^(-w))*(∫u:ℝ in (0:ℝ)..(q/(n+1:ℕ)),
        (u:ℂ)^(-w)*regularRaw c u))-
        burnolQuarterMeanCoefficient (forwardQuarter c zero)*(q:ℂ)^(1-w)/(1-w)+
        mellin (returnRaw (S (sourceInverse c zero))) (1-w):=by
  have source:=actual_inverse_log_moment c zero w 0 below
  rw [constant_moment w below] at source
  simpa only [quarterMoment,logWeight,sourceTerm,logSource_zero,pow_zero,mul_one,mul_div_assoc] using source

theorem actual_inverse_log_domain (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (w:ℂ) (j:ℕ) (below:w.re<1):
    Integrable (fun x:ℝ=>logWeight w j x*inverseRaw c zero x) νq:=
  weighted_integrable _ (actual_inverse_continuous c zero) w j below

private theorem moment_differentiable (raw:ℝ→ℂ) (regular:Continuous raw)
    (w:ℂ) (below:w.re<1):DifferentiableAt ℂ (fun z:ℂ=>quarterMoment raw z 0) w:=by
  have positive:0<(1-w).re:=by simp only [sub_re,one_re];linarith
  have outside:∀x:ℝ,q < |x| → compactRaw raw x=0:=by
    intro x beyond
    exact indicator_of_notMem (s:=symmetricInterval q)
      (fun inside=>not_le_of_gt beyond (abs_le.mpr inside)) raw
  have tail:compactRaw raw=O[atTop](fun x:ℝ=>x^(-((1-w).re+1))):=by
    simpa only [logSource_zero] using log_top_bound (compactRaw raw) q outside 0 ((1-w).re+1)
  have source:=mellin_differentiableAt_of_isBigO_rpow
    (((compact_memLp raw regular).locallyIntegrable (by norm_num)).locallyIntegrableOn _)
    tail (by linarith : (1-w).re<(1-w).re+1) (compact_origin raw regular) positive
  have field:(fun z:ℂ=>quarterMoment raw z 0)=fun z:ℂ=>mellin (compactRaw raw) (1-z):=by
    funext z
    simpa only [logSource_zero] using (compact_mellin_read raw z 0).symm
  rw [field]
  exact source.comp w ((differentiableAt_const (1:ℂ)).sub (differentiableAt_id))

theorem actual_inverse_moment_differentiable (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (w:ℂ) (below:w.re<1):
    DifferentiableAt ℂ (fun z:ℂ=>∫x:ℝ in (0:ℝ)..q,(x:ℂ)^(-z)*inverseRaw c zero x) w:=by
  simpa only [quarterMoment,logWeight,pow_zero,mul_one] using
    moment_differentiable _ (actual_inverse_continuous c zero) w below

theorem actual_bank_moment_differentiable (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (w:ℂ) (below:w.re<1):
    DifferentiableAt ℂ (fun z:ℂ=>∑'n:ℕ,sourceTerm c z 0 n) w:=by
  have same:(fun z:ℂ=>∑'n:ℕ,sourceTerm c z 0 n)=ᶠ[𝓝 w]
      (fun z:ℂ=>quarterMoment (quarterBankRaw c) z 0):=by
    filter_upwards [isOpen_lt continuous_re continuous_const |>.mem_nhds below] with z hz
    exact (actual_bank_log_hasSum c zero z 0 hz).tsum_eq
  exact (moment_differentiable _ (actual_quarter_bank_continuous c zero) w below).congr_of_eventuallyEq same

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.ComplementMoment
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
