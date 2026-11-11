import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.CompactPaired
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Mean

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.StrongIdentification
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszFinitePairing.CoPoisson.Ward
open scoped Topology InnerProductSpace
open private channel channel_summable forward_reindex from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Forward

def finiteRaw (raw:ℝ→ℂ) (N:ℕ) (x:ℝ):ℂ:=
  (∑n∈Finset.Ico 1 N,(n:ℂ)⁻¹*raw (x/(n:ℝ)))-
    ∫a:ℝ in Ioc 0 (N:ℝ),(a:ℂ)⁻¹*raw (x/a)

private theorem channel_raw (source:BurnolL2) (raw:ℝ→ℂ)
    (represents:(source:ℝ→ℂ)=ᵐ[volume]raw) (a:ℝ) (positive:0<a):
    (ContinuousChannels.channel (-1) a source:ℝ→ℂ)=ᵐ[volume]fun x=>(a:ℂ)⁻¹*raw (x/a):=by
  have moved:∀ᵐx:ℝ∂volume,source (a⁻¹*x)=raw (a⁻¹*x):=
    (Measure.quasiMeasurePreserving_smul (μ:=(volume:Measure ℝ)) (inv_ne_zero positive.ne')).ae represents
  have squareRoot:Real.sqrt a=Real.exp (Real.log a/2):=by rw [Real.exp_half,Real.exp_log positive]
  simp only [ContinuousChannels.channel,neg_one_mul]
  filter_upwards [Lp.coeFn_smul (Real.sqrt a:ℂ)⁻¹ (burnolMultiplicativeDilation (-Real.log a) source),
    burnolMultiplicativeDilation_coeFn (-Real.log a) source,moved] with x scalarAt dilatedAt sourceAt
  rw [scalarAt]
  change (Real.sqrt a:ℂ)⁻¹*burnolMultiplicativeDilation (-Real.log a) source x=_
  rw [dilatedAt,burnolL2RawNormalizedDilation,Real.exp_neg,Real.exp_log positive,
    neg_div,Real.exp_neg,←squareRoot,Complex.ofReal_inv,←mul_assoc,←mul_inv_rev,
    ←Complex.ofReal_mul,Real.mul_self_sqrt positive.le,sourceAt]
  rw [div_eq_mul_inv,mul_comm x]

/-- The original finite graph keeps its integer and full 0..N normalization in one actual raw event. -/
theorem actual_finite_raw (source:BurnolL2) (raw:ℝ→ℂ)
    (represents:(source:ℝ→ℂ)=ᵐ[volume]raw) (measured:Measurable raw) (N:ℕ):
    (FiniteForcing.source N source:ℝ→ℂ)=ᵐ[volume]finiteRaw raw N:=by
  have integralRaw:((∫a:ℝ in Ioc 0 (N:ℝ),ContinuousChannels.channel (-1) a source:BurnolL2):ℝ→ℂ)=ᵐ[volume]
      fun x=>∫a:ℝ in Ioc 0 (N:ℝ),(a:ℂ)⁻¹*raw (x/a):=by
    apply source_l2_bochner_coeFn (volume.restrict (Ioc 0 (N:ℝ))) _
      (ContinuousChannels.channel_integrable (-1) N source)
      (fun p:ℝ×ℝ=>(p.1:ℂ)⁻¹*raw (p.2/p.1))
      ((Complex.measurable_ofReal.comp measurable_fst).inv.mul
        (measured.comp (measurable_snd.div measurable_fst)))
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with a inside
    exact channel_raw source raw represents a inside.1
  have channels:∀ᵐx:ℝ∂volume,∀n:{n:ℕ//n∈Finset.Ico 1 N},
      Channels.sourceChannel n source x=(n:ℂ)⁻¹*raw (x/(n:ℝ)):=by
    apply ae_all_iff.mpr
    intro n
    have sample:=channel_raw source raw represents (n:ℝ) (by exact_mod_cast (Finset.mem_Ico.mp n.property).1)
    filter_upwards [sample] with x actual
    simpa only [ContinuousChannels.channel,Channels.sourceChannel,neg_one_mul,Complex.ofReal_natCast] using actual
  filter_upwards [Lp.coeFn_sub (∑n∈Finset.Ico 1 N,Channels.sourceChannel n source)
      (∫a:ℝ in Ioc 0 (N:ℝ),ContinuousChannels.channel (-1) a source),
    Lp.coeFn_fun_finsetSum (Finset.Ico 1 N) (fun n=>Channels.sourceChannel n source),integralRaw,channels]
      with x subtraction sumRead normalization channelAt
  change ((∑n∈Finset.Ico 1 N,Channels.sourceChannel n source)-
    ∫a:ℝ in Ioc 0 (N:ℝ),ContinuousChannels.channel (-1) a source:BurnolL2) x=_
  rw [subtraction,Pi.sub_apply,sumRead,normalization,finiteRaw]
  congr 1
  apply Finset.sum_congr rfl
  intro n inside
  exact channelAt ⟨n,inside⟩

private theorem positive_normalization (raw:ℝ→ℂ)
    (reciprocal:IntegrableOn (fun u:ℝ=>(u:ℂ)⁻¹*raw u) (Ioi 0)) (x:ℝ) (positive:0<x):
    IntegrableOn (fun a:ℝ=>(a:ℂ)⁻¹*raw (x/a)) (Ioi 0) ∧
      (∫a:ℝ in Ioi 0,(a:ℂ)⁻¹*raw (x/a))=∫u:ℝ in Ioi 0,(u:ℂ)⁻¹*raw u:=by
  let g:ℝ→ℂ:=fun u=>(u:ℂ)⁻¹*raw u
  have scaled:IntegrableOn (fun a:ℝ=>g (x*a)) (Ioi 0):=by
    apply (integrableOn_Ioi_comp_mul_left_iff g 0 positive).mpr
    simpa only [mul_zero] using reciprocal
  have changed:= (integrableOn_Ioi_comp_rpow_iff (fun a:ℝ=>g (x*a)) (by norm_num:(-1:ℝ)≠0)).mpr scaled
  have identity:∀a∈Ioi (0:ℝ),(a:ℂ)⁻¹*raw (x/a)=
      (x:ℂ)*((abs (-1:ℝ)*a^((-1:ℝ)-1)) • g (x*a^(-1:ℝ))):=by
    intro a inside
    have aPositive:0<a:=inside
    dsimp only [g]
    rw [Real.rpow_neg_one,show (-1:ℝ)-1=-2 by norm_num,Real.rpow_neg aPositive.le,Real.rpow_two]
    simp only [abs_neg,abs_one,one_mul,Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_pow,
      Complex.ofReal_mul]
    rw [←div_eq_mul_inv x a]
    field_simp [Complex.ofReal_ne_zero.mpr positive.ne',Complex.ofReal_ne_zero.mpr aPositive.ne']
  constructor
  · apply (changed.const_mul (x:ℂ)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a inside
    exact (identity a inside).symm
  · rw [setIntegral_congr_fun measurableSet_Ioi identity,integral_const_mul,
      integral_comp_rpow_Ioi (fun a:ℝ=>g (x*a)) (by norm_num:(-1:ℝ)≠0),integral_comp_mul_left_Ioi g 0 positive,mul_zero,
      Complex.real_smul,Complex.ofReal_inv]
    simp only [g]
    field_simp [Complex.ofReal_ne_zero.mpr positive.ne']

private theorem integer_tendsto (raw:ℝ→ℂ) (B:ℝ) (growth:∀x,‖raw x‖≤B*|x|) (x:ℝ):
    Tendsto (fun N:ℕ=>∑n∈Finset.Ico 1 N,(n:ℂ)⁻¹*raw (x/(n:ℝ))) atTop
      (𝓝 (burnolInnerGapForward raw x)):=by
  rw [forward_reindex]
  have summable:Summable (fun n:ℕ=>channel raw n x):=
    summable_norm_iff.mp (channel_summable raw B growth x)
  apply (tendsto_add_atTop_iff_nat 1).mp
  convert summable.hasSum.tendsto_sum_nat using 1
  funext N
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel,channel,Nat.cast_add,Nat.cast_one,add_comm]

/-- The complete continuous normalization converges to the same source's actual reciprocal mean. -/
theorem actual_normalization_tendsto (raw:ℝ→ℂ) (even:∀x,raw (-x)=raw x)
    (reciprocal:IntegrableOn (fun u:ℝ=>(u:ℂ)⁻¹*raw u) (Ioi 0)) (x:ℝ) (nonzero:x≠0):
    Tendsto (fun N:ℕ=>∫a:ℝ in Ioc 0 (N:ℝ),(a:ℂ)⁻¹*raw (x/a)) atTop
      (𝓝 (∫u:ℝ in Ioi 0,(u:ℂ)⁻¹*raw u)):=by
  have absolute:∀z:ℝ,raw |z|=raw z:=by
    intro z
    rcases le_total 0 z with nonnegative|nonpositive
    · rw [abs_of_nonneg nonnegative]
    · rw [abs_of_nonpos nonpositive,even]
  obtain ⟨domain,mean⟩:=positive_normalization raw reciprocal |x| (abs_pos.mpr nonzero)
  have original:=intervalIntegral_tendsto_integral_Ioi 0 domain (tendsto_natCast_atTop_atTop (R:=ℝ))
  rw [mean] at original
  apply original.congr'
  filter_upwards with N
  rw [intervalIntegral.integral_of_le (Nat.cast_nonneg N)]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro a inside
  dsimp only
  congr 1
  rw [←absolute (x/a),abs_div,abs_of_pos inside.1]

/-- Integer and continuous limits are taken at the same N, after the actual origin cancellation. -/
theorem actual_finite_pointwise (raw:ℝ→ℂ) (even:∀x,raw (-x)=raw x)
    (B:ℝ) (growth:∀x,‖raw x‖≤B*|x|)
    (reciprocal:IntegrableOn (fun u:ℝ=>(u:ℂ)⁻¹*raw u) (Ioi 0)) (x:ℝ) (nonzero:x≠0):
    Tendsto (fun N:ℕ=>finiteRaw raw N x) atTop
      (𝓝 (burnolInnerGapForward raw x-∫u:ℝ in Ioi 0,(u:ℂ)⁻¹*raw u)):=
  (integer_tendsto raw B growth x).sub (actual_normalization_tendsto raw even reciprocal x nonzero)

/-- A legitimate AE subsequence identifies the full strong graph, including its actual Unit normalizer. -/
theorem actual_strong_raw (source value:BurnolL2) (raw:ℝ→ℂ)
    (represents:(source:ℝ→ℂ)=ᵐ[volume]raw) (measured:Measurable raw)
    (even:∀x,raw (-x)=raw x) (B:ℝ) (growth:∀x,‖raw x‖≤B*|x|)
    (reciprocal:IntegrableOn (fun u:ℝ=>(u:ℂ)⁻¹*raw u) (Ioi 0))
    (graph:Tendsto (fun N:ℕ=>FiniteForcing.source N source) atTop (𝓝 value)):
    (value:ℝ→ℂ)=ᵐ[volume]fun x=>burnolInnerGapForward raw x-∫u:ℝ in Ioi 0,(u:ℂ)⁻¹*raw u:=by
  obtain ⟨indices,strict,pointwise⟩:=
    (tendstoInMeasure_of_tendsto_Lp graph).exists_seq_tendsto_ae
  have reads:∀ᵐx:ℝ∂volume,∀N:ℕ,FiniteForcing.source N source x=finiteRaw raw N x:=
    ae_all_iff.mpr (fun N=>actual_finite_raw source raw represents measured N)
  filter_upwards [pointwise,reads,volume.ae_ne (0:ℝ)] with x converges read nonzero
  have actual:=(actual_finite_pointwise raw even B growth reciprocal x nonzero).comp strict.tendsto_atTop
  have same:=(converges.congr' (Eventually.of_forall (fun n=>read (indices n))))
  exact tendsto_nhds_unique same actual

/-- The full strong counting value realizes the original source with the same actual reciprocal Unit. -/
theorem actual_strong_realizes (source value:BurnolL2) (raw:ℝ→ℂ)
    (represents:(source:ℝ→ℂ)=ᵐ[volume]raw) (measured:Measurable raw) (atZero:raw 0=0)
    (even:∀x,raw (-x)=raw x) (B:ℝ) (growth:∀x,‖raw x‖≤B*|x|)
    (reciprocal:Integrable (fun u:ℝ=>(u:ℂ)⁻¹*raw u))
    (graph:Tendsto (fun N:ℕ=>FiniteForcing.source N source) atTop (𝓝 value))
    (test:SchwartzMap ℝ ℂ) (paired:Integrable (fun x:ℝ=>raw x*coPoissonMuntzScaleRemainder test |x|)):
    burnolRemainderSourceRead source test=(Lp.toTemperedDistributionCLM ℂ volume 2 value) test:=by
  have actual:=actual_strong_raw source value raw represents measured even B growth reciprocal.integrableOn graph
  rw [burnolRemainderSourceRead_integral]
  calc
    _=(1/2:ℂ)*∫x:ℝ,raw x*coPoissonMuntzScaleRemainder test |x|:=by
      congr 1
      apply integral_congr_ae
      filter_upwards [represents] with x sourceAt
      rw [sourceAt]
    _=∫x:ℝ,test x*(burnolInnerGapForward raw x-∫u:ℝ in Ioi 0,(u:ℂ)⁻¹*raw u):=
      OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Forward.actual_regular_remainder_forward raw measured atZero even B growth
        reciprocal test paired
    _=_:=by
      rw [Lp.toTemperedDistributionCLM_apply,Lp.toTemperedDistribution_apply]
      apply integral_congr_ae
      filter_upwards [actual] with x valueAt
      rw [valueAt]
      ring

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.StrongIdentification
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
