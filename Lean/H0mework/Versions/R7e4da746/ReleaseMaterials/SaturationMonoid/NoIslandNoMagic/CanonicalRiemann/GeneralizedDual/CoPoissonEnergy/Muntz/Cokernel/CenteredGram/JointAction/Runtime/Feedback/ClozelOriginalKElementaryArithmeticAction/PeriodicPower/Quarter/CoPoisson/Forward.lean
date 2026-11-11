import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Whole
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.DirectBound
import Mathlib.Analysis.Normed.Group.Tannery

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Forward
open Complex Filter MeasureTheory Set BurnolPhysicalState
open scoped Topology ENNReal InnerProductSpace
local notation "q" => (1/4:ℝ)

private def cutoffSet (N : ℕ) : Set ℝ := {x | (N+1:ℝ)⁻¹≤|x|}
private def cutoff (raw : ℝ→ℂ) (N : ℕ) : ℝ→ℂ := (cutoffSet N).indicator raw

private theorem cutoff_measurableSet (N : ℕ) : MeasurableSet (cutoffSet N) :=
  measurableSet_le measurable_const continuous_abs.measurable

private theorem cutoff_measurable (raw : ℝ→ℂ) (measurable : Measurable raw) (N : ℕ) :
    Measurable (cutoff raw N) := measurable.indicator (cutoff_measurableSet N)

private theorem cutoff_norm (raw : ℝ→ℂ) (N : ℕ) (x : ℝ) :
    ‖cutoff raw N x‖≤‖raw x‖ := by
  unfold cutoff
  by_cases inside:x∈cutoffSet N
  · rw [indicator_of_mem inside]
  · rw [indicator_of_notMem inside,norm_zero]
    exact norm_nonneg _

private theorem cutoff_zero (raw : ℝ→ℂ) (N : ℕ) : cutoff raw N 0=0 := by
  apply indicator_of_notMem
  simp only [cutoffSet,mem_ofPred_eq,abs_zero,not_le]
  positivity

private theorem cutoff_even (raw : ℝ→ℂ) (even : ∀x,raw (-x)=raw x) (N : ℕ) (x : ℝ) :
    cutoff raw N (-x)=cutoff raw N x := by
  simp only [cutoff,indicator_apply,cutoffSet,mem_ofPred_eq,abs_neg,even]

private theorem cutoff_tendsto (raw : ℝ→ℂ) (atZero : raw 0=0) (x : ℝ) :
    Tendsto (fun N:ℕ=>cutoff raw N x) atTop (𝓝 (raw x)) := by
  by_cases origin:x=0
  · subst x
    simp only [cutoff_zero,atZero]
    exact tendsto_const_nhds
  have radius : Tendsto (fun N:ℕ=>(N+1:ℝ)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))
  have eventually:=radius.eventually (Iio_mem_nhds (abs_pos.mpr origin))
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually] with N small
  exact (indicator_of_mem (show x∈cutoffSet N from small.le) raw).symm

private theorem compact_norm_bound (B : ℝ) (_nonnegative : 0≤B) :
    Integrable ((symmetricInterval q).indicator (fun _:ℝ=>B)) := by
  apply (integrable_indicator_iff (measurableSet_symmetricInterval q)).mpr
  exact integrableOn_const (by simp [symmetricInterval])

private theorem reciprocal_bound (raw : ℝ→ℂ) (B : ℝ) (nonnegative : 0≤B)
    (growth : ∀x,‖raw x‖≤B*|x|) (outside : ∀x,q≤|x| → raw x=0) (x : ℝ) :
    ‖(x:ℂ)⁻¹*raw x‖≤(symmetricInterval q).indicator (fun _:ℝ=>B) x := by
  by_cases inside:x∈symmetricInterval q
  · rw [indicator_of_mem inside,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs]
    by_cases origin:x=0
    · subst x
      simpa using nonnegative
    have positive:0 < |x|:=abs_pos.mpr origin
    calc
      _≤|x|⁻¹*(B*|x|):=mul_le_mul_of_nonneg_left (growth x) (inv_nonneg.mpr positive.le)
      _=B:=by field_simp
  · rw [indicator_of_notMem inside,outside x (le_of_not_ge (fun small=>inside (abs_le.mp small))),mul_zero,norm_zero]

private theorem reciprocal_integrable (raw : ℝ→ℂ) (measurable : Measurable raw)
    (B : ℝ) (nonnegative : 0≤B) (growth : ∀x,‖raw x‖≤B*|x|)
    (outside : ∀x,q≤|x| → raw x=0) : Integrable (fun x:ℝ=>(x:ℂ)⁻¹*raw x) :=
  (compact_norm_bound B nonnegative).mono'
    ((Complex.measurable_ofReal.comp measurable_id).inv.mul measurable).aestronglyMeasurable
    (Eventually.of_forall (reciprocal_bound raw B nonnegative growth outside))

private theorem cutoff_growth (raw : ℝ→ℂ) (B : ℝ) (growth : ∀x,‖raw x‖≤B*|x|)
    (N : ℕ) (x : ℝ) : ‖cutoff raw N x‖≤B*|x| := (cutoff_norm raw N x).trans (growth x)

private theorem cutoff_outside (raw : ℝ→ℂ) (outside : ∀x,q≤|x| → raw x=0)
    (N : ℕ) (x : ℝ) (large : q≤|x|) : cutoff raw N x=0 := by
  unfold cutoff
  by_cases active:x∈cutoffSet N
  · rw [indicator_of_mem active,outside x large]
  · exact indicator_of_notMem active raw

private theorem cutoff_weighted (raw : ℝ→ℂ) (measurable : Measurable raw)
    (B : ℝ) (nonnegative : 0≤B) (growth : ∀x,‖raw x‖≤B*|x|)
    (outside : ∀x,q≤|x| → raw x=0) (N : ℕ) :
    Integrable (fun x:ℝ=>‖cutoff raw N x‖/|x|^3) := by
  let bound:=B*q*(N+1:ℝ)^3
  apply (compact_norm_bound bound (by dsimp [bound];positivity)).mono'
    (((cutoff_measurable raw measurable N).norm).div
      (continuous_abs.measurable.pow_const 3)).aestronglyMeasurable
  filter_upwards with x
  change ‖‖cutoff raw N x‖/|x|^3‖≤(symmetricInterval q).indicator (fun _:ℝ=>bound) x
  rw [Real.norm_of_nonneg (by positivity)]
  by_cases inside:x∈symmetricInterval q
  · rw [indicator_of_mem inside]
    by_cases active:x∈cutoffSet N
    · have positive:0 < |x| := (inv_pos.mpr (by positivity : (0:ℝ)<N+1)).trans_le active
      have inverse:|x|⁻¹≤(N+1:ℝ) := by
        have paid:=(inv_le_inv₀ positive (inv_pos.mpr (by positivity : (0:ℝ)<N+1))).mpr active
        simpa only [inv_inv] using paid
      calc
        _≤(B*q)/|x|^3:=div_le_div_of_nonneg_right
          ((cutoff_growth raw B growth N x).trans (mul_le_mul_of_nonneg_left (abs_le.mpr inside) nonnegative))
          (by positivity)
        _≤bound:=by
          rw [div_eq_mul_inv,←inv_pow]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.mpr positive.le) inverse 3)
            (mul_nonneg nonnegative (by norm_num))
    · rw [cutoff,indicator_of_notMem active,norm_zero,zero_div]
      dsimp [bound]
      positivity
  · rw [indicator_of_notMem inside,cutoff_outside raw outside N x
      (le_of_not_ge (fun small=>inside (abs_le.mp small))),norm_zero,zero_div]

private def pweight (n : ℕ) : ℝ := (((n+1:ℕ):ℝ)^2)⁻¹

private theorem pweight_summable : Summable pweight := by
  exact (summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr (by decide : (1:ℕ)<2))

private def channel (raw : ℝ→ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  ((n+1:ℕ):ℂ)⁻¹*raw (x/(n+1:ℕ))

private theorem channel_bound (raw : ℝ→ℂ) (B : ℝ)
    (growth : ∀x,‖raw x‖≤B*|x|) (n : ℕ) (x : ℝ) :
    ‖channel raw n x‖≤(B*|x|)*pweight n := by
  have positive:(0:ℝ)<(n+1:ℕ):=by positivity
  rw [channel,norm_mul,norm_inv,Complex.norm_natCast]
  apply (mul_le_mul_of_nonneg_left (growth (x/(n+1:ℕ))) (inv_nonneg.mpr positive.le)).trans_eq
  rw [abs_div,abs_of_pos positive,pweight]
  field_simp

private theorem channel_summable (raw : ℝ→ℂ) (B : ℝ)
    (growth : ∀x,‖raw x‖≤B*|x|) (x : ℝ) : Summable (fun n:ℕ=>‖channel raw n x‖) :=
  (pweight_summable.mul_left (B*|x|)).of_nonneg_of_le (fun _=>norm_nonneg _) (fun n=>channel_bound raw B growth n x)

private theorem forward_reindex (raw : ℝ→ℂ) (x : ℝ) :
    burnolInnerGapForward raw x=∑'n:ℕ,channel raw n x :=
  (Equiv.tsum_eq (Equiv.pnatEquivNat.symm)
    (fun n:ℕ+=>(((n:ℕ):ℂ)⁻¹)*raw (x/(n:ℕ)))).symm

private theorem forward_bound (raw : ℝ→ℂ) (B : ℝ)
    (growth : ∀x,‖raw x‖≤B*|x|) (x : ℝ) :
    ‖burnolInnerGapForward raw x‖≤B*|x| *(∑'n:ℕ,pweight n) := by
  rw [forward_reindex,←tsum_mul_left]
  exact (norm_tsum_le_tsum_norm (channel_summable raw B growth x)).trans
    (Summable.tsum_le_tsum (fun n=>channel_bound raw B growth n x) (channel_summable raw B growth x)
      (pweight_summable.mul_left (B*|x|)))

private theorem forward_cutoff_tendsto (raw : ℝ→ℂ) (atZero : raw 0=0)
    (B : ℝ) (growth : ∀x,‖raw x‖≤B*|x|) (x : ℝ) :
    Tendsto (fun N:ℕ=>burnolInnerGapForward (cutoff raw N) x) atTop (𝓝 (burnolInnerGapForward raw x)) := by
  simp only [forward_reindex]
  apply tendsto_tsum_of_dominated_convergence (pweight_summable.mul_left (B*|x|))
  · intro n
    exact (cutoff_tendsto raw atZero (x/(n+1:ℕ))).const_mul _
  · exact Eventually.of_forall (fun N n=>channel_bound (cutoff raw N) B (cutoff_growth raw B growth N) n x)

private theorem forward_measurable (raw : ℝ→ℂ) (measurable : Measurable raw) :
    Measurable (burnolInnerGapForward raw) := by
  unfold burnolInnerGapForward
  exact Measurable.tsum (fun n=>measurable_const.mul (measurable.comp (measurable_id.div_const _)))

private theorem test_dominant_integrable (test : SchwartzMap ℝ ℂ) (B : ℝ) :
    Integrable (fun x:ℝ=>‖test x‖*(B*|x| * (∑'n:ℕ,pweight n))) := by
  have paid:=(test.integrable_pow_mul volume 1).const_mul (B*(∑'n:ℕ,pweight n))
  convert paid using 1
  ext x
  simp only [pow_one,Real.norm_eq_abs]
  ring

private theorem forward_test_integrable (raw : ℝ→ℂ) (measurable : Measurable raw)
    (B : ℝ) (growth : ∀x,‖raw x‖≤B*|x|) (test : SchwartzMap ℝ ℂ) :
    Integrable (fun x:ℝ=>test x*burnolInnerGapForward raw x) := by
  apply (test_dominant_integrable test B).mono'
    (test.continuous.measurable.mul (forward_measurable raw measurable)).aestronglyMeasurable
  filter_upwards with x
  rw [Pi.mul_apply,norm_mul]
  exact mul_le_mul_of_nonneg_left (forward_bound raw B growth x) (norm_nonneg _)

private theorem forward_integral_limit (raw : ℝ→ℂ) (measurable : Measurable raw) (atZero : raw 0=0)
    (B : ℝ) (growth : ∀x,‖raw x‖≤B*|x|) (test : SchwartzMap ℝ ℂ) :
    Tendsto (fun N:ℕ=>∫x:ℝ,test x*burnolInnerGapForward (cutoff raw N) x) atTop
      (𝓝 (∫x:ℝ,test x*burnolInnerGapForward raw x)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun x:ℝ=>‖test x‖*(B*|x| * (∑'n:ℕ,pweight n)))
  · intro N
    exact (test.continuous.measurable.mul (forward_measurable _ (cutoff_measurable raw measurable N))).aestronglyMeasurable
  · exact test_dominant_integrable test B
  · intro N
    filter_upwards with x
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (forward_bound _ B (cutoff_growth raw B growth N) x) (norm_nonneg _)
  · exact Eventually.of_forall (fun x=>(forward_cutoff_tendsto raw atZero B growth x).const_mul (test x))

private theorem reciprocal_integral_limit (raw : ℝ→ℂ) (measurable : Measurable raw) (atZero : raw 0=0)
    (B : ℝ) (nonnegative : 0≤B) (growth : ∀x,‖raw x‖≤B*|x|)
    (outside : ∀x,q≤|x| → raw x=0) :
    Tendsto (fun N:ℕ=>∫x:ℝ in Ioi 0,(x:ℂ)⁻¹*cutoff raw N x) atTop
      (𝓝 (∫x:ℝ in Ioi 0,(x:ℂ)⁻¹*raw x)) := by
  apply tendsto_integral_of_dominated_convergence ((symmetricInterval q).indicator (fun _:ℝ=>B))
  · intro N
    exact (((Complex.measurable_ofReal.comp measurable_id).inv.mul
      (cutoff_measurable raw measurable N)).aestronglyMeasurable).restrict
  · exact (compact_norm_bound B nonnegative).integrableOn
  · intro N
    exact Eventually.of_forall (reciprocal_bound _ B nonnegative (cutoff_growth raw B growth N)
      (cutoff_outside raw outside N))
  · exact Eventually.of_forall (fun x=>(cutoff_tendsto raw atZero x).const_mul (x:ℂ)⁻¹)

private theorem source_read_raw (source : BurnolL2) (raw : ℝ→ℂ)
    (represents : (source:ℝ→ℂ)=ᵐ[volume]raw) (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead source test=(1/2:ℂ)*∫x:ℝ,raw x*coPoissonMuntzScaleRemainder test |x| := by
  rw [burnolRemainderSourceRead_integral]
  congr 1
  exact integral_congr_ae (represents.mul (EventuallyEq.refl _ _))

private theorem source_integral_limit (raw : ℝ→ℂ) (rawMem : MemLp raw 2 volume)
    (measurable : Measurable raw) (atZero : raw 0=0) (test : SchwartzMap ℝ ℂ) :
    Tendsto (fun N:ℕ=>∫x:ℝ,cutoff raw N x*coPoissonMuntzScaleRemainder test |x|) atTop
      (𝓝 (∫x:ℝ,raw x*coPoissonMuntzScaleRemainder test |x|)) := by
  have kernelMem:MemLp (fun x:ℝ=>coPoissonMuntzScaleRemainder test |x|) 2 volume:=
    (Lp.memLp (burnolRemainderL2Kernel test)).ae_eq (burnolRemainderL2Kernel_coeFn test)
  apply tendsto_integral_of_dominated_convergence (fun x:ℝ=>‖raw x*coPoissonMuntzScaleRemainder test |x|‖)
  · intro N
    exact (cutoff_measurable raw measurable N).aestronglyMeasurable.mul kernelMem.aestronglyMeasurable
  · exact (rawMem.integrable_mul kernelMem).norm
  · intro N
    filter_upwards with x
    simp only [norm_mul]
    exact mul_le_mul_of_nonneg_right (cutoff_norm raw N x) (norm_nonneg _)
  · exact Eventually.of_forall (fun x=>(cutoff_tendsto raw atZero x).mul_const _)

private theorem source_forward_of_linear_origin (source : BurnolL2) (raw : ℝ→ℂ)
    (represents : (source:ℝ→ℂ)=ᵐ[volume]raw) (measurable : Measurable raw)
    (atZero : raw 0=0) (even : ∀x,raw (-x)=raw x) (B : ℝ) (nonnegative : 0≤B)
    (growth : ∀x,‖raw x‖≤B*|x|) (outside : ∀x,q≤|x| → raw x=0) (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead source test=
      ∫x:ℝ,test x*(burnolInnerGapForward raw x-∫u:ℝ in Ioi 0,(u:ℂ)⁻¹*raw u) := by
  have rawMem:MemLp raw 2 volume:=(Lp.memLp source).ae_eq represents
  have finite (N:ℕ) :
      (1/2:ℂ)*(∫x:ℝ,cutoff raw N x*coPoissonMuntzScaleRemainder test |x|)=
        (∫x:ℝ,test x*burnolInnerGapForward (cutoff raw N) x)-
          (∫x:ℝ,test x)*(∫u:ℝ in Ioi 0,(u:ℂ)⁻¹*cutoff raw N u) := by
    let cutMem : MemLp (cutoff raw N) 2 volume:=rawMem.indicator (cutoff_measurableSet N)
    let cutValue:BurnolL2:=cutMem.toLp (cutoff raw N)
    have generated:=burnolRemainderSourceRead_forward cutValue (cutoff raw N)
      (cutoff_measurable raw measurable N) cutMem.coeFn_toLp (cutoff_zero raw N)
      (cutoff_even raw even N) (cutoff_weighted raw measurable B nonnegative growth outside N)
      (reciprocal_integrable _ (cutoff_measurable raw measurable N) B nonnegative
        (cutoff_growth raw B growth N) (cutoff_outside raw outside N)).integrableOn test
    rw [source_read_raw cutValue _ cutMem.coeFn_toLp] at generated
    simp only [mul_sub] at generated
    rw [integral_sub (forward_test_integrable _ (cutoff_measurable raw measurable N) B
      (cutoff_growth raw B growth N) test) (test.integrable.mul_const _),integral_mul_const] at generated
    exact generated
  have sourceLimit:=(source_integral_limit raw rawMem measurable atZero test).const_mul (1/2:ℂ)
  have valueLimit:=(forward_integral_limit raw measurable atZero B growth test).sub
    ((reciprocal_integral_limit raw measurable atZero B nonnegative growth outside).const_mul (∫x:ℝ,test x))
  have equal:=tendsto_nhds_unique sourceLimit (valueLimit.congr' (Eventually.of_forall (fun N=>(finite N).symm)))
  rw [source_read_raw source raw represents]
  rw [equal]
  simp only [mul_sub]
  rw [integral_sub (forward_test_integrable raw measurable B growth test) (test.integrable.mul_const _),integral_mul_const]

private theorem forward_locally_integrable (raw : ℝ→ℂ) (measurable : Measurable raw)
    (B : ℝ) (growth : ∀x,‖raw x‖≤B*|x|) : LocallyIntegrable (burnolInnerGapForward raw) volume := by
  have regular:Continuous (fun x:ℝ=>B*|x| * (∑'n:ℕ,pweight n)):=by fun_prop
  apply regular.locallyIntegrable.mono (forward_measurable raw measurable).aestronglyMeasurable
  exact Eventually.of_forall (fun x=>(forward_bound raw B growth x).trans (Real.le_norm_self _))

private theorem source_forward_realization (source value : BurnolL2) (raw : ℝ→ℂ)
    (represents : (source:ℝ→ℂ)=ᵐ[volume]raw) (measurable : Measurable raw)
    (atZero : raw 0=0) (even : ∀x,raw (-x)=raw x) (B : ℝ) (nonnegative : 0≤B)
    (growth : ∀x,‖raw x‖≤B*|x|) (outside : ∀x,q≤|x| → raw x=0)
    (realizes : ∀test:SchwartzMap ℝ ℂ,burnolRemainderSourceRead source test=
      (Lp.toTemperedDistributionCLM ℂ volume 2 value) test) :
    (value:ℝ→ℂ)=ᵐ[volume](fun x=>burnolInnerGapForward raw x-∫u:ℝ in Ioi 0,(u:ℂ)⁻¹*raw u) := by
  apply ae_eq_of_integral_contDiff_smul_eq ((Lp.memLp value).locallyIntegrable (by norm_num))
    ((forward_locally_integrable raw measurable B growth).sub continuous_const.locallyIntegrable)
  intro test smooth compact
  let complexTest : SchwartzMap ℝ ℂ :=
    (compact.comp_left (show Complex.ofRealCLM 0=0 from rfl)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp smooth)
  have actual:=source_forward_of_linear_origin source raw represents measurable atZero even B nonnegative growth outside complexTest
  rw [realizes,Lp.toTemperedDistributionCLM_apply,Lp.toTemperedDistribution_apply] at actual
  change (∫x:ℝ,(test x:ℂ)*value x)=∫x:ℝ,(test x:ℂ)*(burnolInnerGapForward raw x-
    ∫u:ℝ in Ioi 0,(u:ℂ)⁻¹*raw u) at actual
  simpa only [Complex.real_smul,Pi.sub_apply] using actual

open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Consumer OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Landing
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.DirectBound

def directMean (c : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
  ∫u:ℝ in Ioi 0,(u:ℂ)⁻¹*directRaw c h u

def directField (c : BurnolCompletedMellinCoordinate) (h x : ℝ) : ℂ :=
  burnolInnerGapForward (directRaw c h) x-directMean c h

/-- The original zero pays the n⁻² channel majorant of the entire direct co-sum. -/
theorem actual_direct_channels (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) (x : ℝ) :
    Summable (fun n:ℕ=>‖((n+1:ℕ):ℂ)⁻¹*directRaw c h (x/(n+1:ℕ))‖) := by
  obtain ⟨B,_,growth⟩:=actual_direct_bound c zero h nonnegative
  exact channel_summable _ B growth x

theorem actual_direct_mean_integrable (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) :
    IntegrableOn (fun u:ℝ=>(u:ℂ)⁻¹*directRaw c h u) (Ioi 0) := by
  obtain ⟨B,positive,growth⟩:=actual_direct_bound c zero h nonnegative
  exact (reciprocal_integrable _ (actual_direct_measurable c h) B positive growth
    (actual_direct_outer_zero c zero h nonnegative)).integrableOn

/-- The same actual H_h, rather than a Pa projection, generates this complete arithmetic field. -/
theorem actual_difference_forward (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (waveDifference c h) test=∫x:ℝ,test x*directField c h x := by
  obtain ⟨B,positive,growth⟩:=actual_direct_bound c zero h nonnegative
  exact source_forward_of_linear_origin (waveDifference c h) (directRaw c h)
    (actual_direct_raw c h) (actual_direct_measurable c h) (actual_direct_origin c h)
    (actual_direct_even c h) B positive growth (actual_direct_outer_zero c zero h nonnegative) test

theorem actual_difference_forward_raw (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) :
    (fourierL2 (countedValue c zero h nonnegative):ℝ→ℂ)=ᵐ[volume] directField c h := by
  obtain ⟨B,positive,growth⟩:=actual_direct_bound c zero h nonnegative
  exact source_forward_realization (waveDifference c h) (fourierL2 (countedValue c zero h nonnegative))
    (directRaw c h) (actual_direct_raw c h) (actual_direct_measurable c h) (actual_direct_origin c h)
    (actual_direct_even c h) B positive growth (actual_direct_outer_zero c zero h nonnegative)
    (actual_difference_realizes c zero h nonnegative)

theorem actual_direct_field_memLp (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) : MemLp (directField c h) 2 volume :=
  (Lp.memLp (fourierL2 (countedValue c zero h nonnegative))).ae_eq
    (actual_difference_forward_raw c zero h nonnegative)

theorem actual_direct_field_series (c : BurnolCompletedMellinCoordinate) (h x : ℝ) :
    directField c h x=(∑'n:ℕ,((n+1:ℕ):ℂ)⁻¹*directRaw c h (x/(n+1:ℕ)))-directMean c h := by
  rw [directField,forward_reindex]
  rfl

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Forward
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
