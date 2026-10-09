import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceFullYSameHalfPlanePole
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.FullYDynamicResponse
open MeasureTheory Filter Set SourceJointResidualEnergy SourceResolventBandLimit
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussUnitaryHistory GaussDiagonalHistory
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open FullYDynamicSource FullYPairedParseval
open scoped Topology FourierTransform InnerProductSpace Interval
attribute [local irreducible] embed literalCoreResolvent literalSharpResolvent sourceOrbit sourceSpace

private def oscillation(a t:ℝ):ℂ:=Complex.exp (-(t:ℂ)*Complex.I*(a:ℂ))
private theorem oscillation_norm(a t:ℝ):‖oscillation a t‖=1:=by
  simp [oscillation,Complex.norm_exp,Complex.mul_re,Complex.mul_im]
def scalarWave(ν a:ℝ):ℝ→ℂ:=causalWave ν (oscillation a)

theorem scalar_wave_integrable(ν a:ℝ)(hν:0<ν):Integrable (scalarWave ν a):=by
  unfold scalarWave causalWave
  apply (integrable_indicator_iff measurableSet_Ioi).mpr
  apply (integrableOn_exp_mul_Ioi (neg_neg_of_pos hν) 0).mono'
    ((show Continuous (fun t:ℝ=>(Real.exp (-ν*t):ℂ) • oscillation a t) by unfold oscillation;fun_prop).aestronglyMeasurable.restrict)
  exact Eventually.of_forall (fun t=>by
    rw [norm_smul,oscillation_norm,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)])

theorem scalar_wave_fourier(ν a ξ:ℝ)(hν:0<ν):
    𝓕 (scalarWave ν a) ξ= -Complex.I*pole ν a (-2*Real.pi*ξ):=by
  rw [scalarWave,causal_wave_fourier]
  have he:(fun t:ℝ=>Complex.exp (t • (Complex.I*line ν (-2*Real.pi*ξ))) • oscillation a t)=
      (fun t:ℝ=>Complex.exp ((Complex.I*(line ν (-2*Real.pi*ξ)-(a:ℂ)))*(t:ℂ))):=by
    funext t
    simp only [oscillation,smul_eq_mul,←Complex.exp_add,Complex.real_smul]
    congr 1
    ring
  rw [he]
  have hh:(Complex.I*(line ν (-2*Real.pi*ξ)-(a:ℂ))).re<0:=by
    simp only [Complex.mul_re,Complex.I_re,zero_mul,Complex.I_im,one_mul,zero_sub,
      Complex.sub_im,Complex.ofReal_im,line_im,sub_zero]
    exact neg_neg_of_pos hν
  rw [integral_exp_mul_complex_Ioi hh 0]
  simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero,pole,mul_sub]
  have hz:(a:ℂ)-line ν (-2*Real.pi*ξ)≠0:=by
    intro h
    have hi:=congrArg Complex.im h
    simp only [Complex.sub_im,Complex.ofReal_im,line_im,zero_sub,Complex.zero_im,neg_eq_zero] at hi
    exact hν.ne' hi
  have hz':line ν (-2*Real.pi*ξ)-(a:ℂ)≠0:=sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp hz))
  field_simp [hz,hz',Complex.I_ne_zero]
  ring_nf
  simp only [Complex.I_sq]
  rw [←inv_neg]
  ring

section Fourier
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E]
private theorem real_inner_flip:(innerₗ ℝ).flip=innerₗ ℝ:=by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  exact real_inner_comm x y
private theorem fourier_twice(f:ℝ→E)(hf:Integrable f)(hF:Integrable (𝓕 f))(hc:Continuous f)(t:ℝ):
    𝓕 (𝓕 f) t=f (-t):=by
  have h:=congrFun (hc.fourierInv_fourier_eq hf hF) (-t)
  simpa only [Real.fourierInv_eq_fourier_neg,neg_neg] using h
omit [CompleteSpace E] in
private theorem fourier_smul_integrable(v:ℝ→ℂ)(u:ℝ→E)(hv:Integrable v)(hu:Integrable u)
    (hFu:Integrable (𝓕 u)):
    Integrable (fun ξ:ℝ=>𝓕 v ξ • 𝓕 u ξ):=by
  apply (hFu.norm.const_mul (∫t:ℝ,‖v t‖)).mono'
    ((fourier_continuous_of_integrable v hv).aestronglyMeasurable.smul
      (fourier_continuous_of_integrable u hu).aestronglyMeasurable)
  exact Eventually.of_forall (fun ξ=>by
    rw [Pi.smul_apply',norm_smul]
    exact mul_le_mul_of_nonneg_right (fourier_bound v ξ) (norm_nonneg _))
private theorem causal_fourier_zero(v:ℝ→ℂ)(u:ℝ→E)(hv:Integrable v)(hu:Integrable u)
    (hFu:Integrable (𝓕 u))(hc:Continuous u)(hz:∀t:ℝ,v t • u (-t)=0):
    (∫ξ:ℝ,𝓕 v ξ • 𝓕 u ξ)=0:=by
  have h:=VectorFourier.integral_fourierIntegral_smul_eq_flip (L:=innerₗ ℝ)
    Real.continuous_fourierChar continuous_inner hv hFu
  rw [real_inner_flip] at h
  change (∫ξ:ℝ,𝓕 v ξ • 𝓕 u ξ)=∫t:ℝ,v t • 𝓕 (𝓕 u) t at h
  simp_rw [fourier_twice u hu hFu hc,hz] at h
  simpa only [integral_zero] using h
omit [CompleteSpace E] in
private theorem append_fourier_zero(v:ℝ→ℂ)(u b:ℝ→E)(hu:Integrable u)(hb:Integrable b)
    (hdi:Integrable (fun ξ:ℝ=>𝓕 v ξ • 𝓕 (u-b) ξ))
    (hdz:(∫ξ:ℝ,𝓕 v ξ • 𝓕 (u-b) ξ)=0)
    (hbi:Integrable (fun ξ:ℝ=>𝓕 v ξ • 𝓕 b ξ))
    (hbz:(∫ξ:ℝ,𝓕 v ξ • 𝓕 b ξ)=0):
    Integrable (fun ξ:ℝ=>𝓕 v ξ • 𝓕 u ξ) ∧ (∫ξ:ℝ,𝓕 v ξ • 𝓕 u ξ)=0:=by
  have he:(fun ξ:ℝ=>𝓕 v ξ • 𝓕 u ξ)=
      (fun ξ:ℝ=>𝓕 v ξ • 𝓕 (u-b) ξ)+(fun ξ:ℝ=>𝓕 v ξ • 𝓕 b ξ):=by
    funext ξ
    simp only [Pi.add_apply]
    rw [fourier_sub_integrable _ _ hu hb]
    simp only [smul_sub,sub_add_cancel]
  rw [he]
  refine ⟨hdi.add hbi,?_⟩
  change (∫ξ:ℝ,𝓕 v ξ • 𝓕 (u-b) ξ+𝓕 v ξ • 𝓕 b ξ)=0
  rw [integral_add hdi hbi,hdz,hbz,add_zero]
end Fourier

private theorem scalar_correction_zero(F:Index)(sharp:Bool)(f:QuantumTest)(advanced:Bool)(μ ν a t:ℝ):
    scalarWave ν a t • waveCorrection F sharp f advanced μ (-t)=0:=by
  by_cases ht:t∈Ioi (0:ℝ)
  · have hn:(-t)∉Ioi (0:ℝ):=by
      change 0<t at ht
      change ¬0< -t
      linarith
    simp only [waveCorrection,sourceWave,causalWave,Pi.sub_apply,indicator_of_notMem hn,sub_self,smul_zero]
  · simp only [scalarWave,causalWave,indicator_of_notMem ht,zero_smul]

private theorem scalar_baseline_pair(μ ν a ξ:ℝ)(hμ:0<μ)(hν:0<ν)(f:QuantumTest):
    𝓕 (scalarWave ν a) ξ • 𝓕 (causalWave μ (fun _=>embed f)) ξ=
      -(pole ν a (-2*Real.pi*ξ)*pole μ 0 (-2*Real.pi*ξ)) • embed f:=by
  rw [scalar_wave_fourier ν a ξ hν,constant_wave_fourier μ hμ,smul_smul]
  congr 1
  simp only [pole,Complex.ofReal_zero,zero_sub,inv_neg,div_eq_mul_inv]
  ring_nf
  simp only [Complex.I_sq]
  ring

attribute [local irreducible] sourceWave waveCorrection scalarWave

private theorem scalar_baseline_hardy(μ ν a:ℝ)(hμ:0<μ)(hν:0<ν)(f:QuantumTest):
    Integrable (fun ξ:ℝ=>𝓕 (scalarWave ν a) ξ • 𝓕 (causalWave μ (fun _=>embed f)) ξ) ∧
    (∫ξ:ℝ,𝓕 (scalarWave ν a) ξ • 𝓕 (causalWave μ (fun _=>embed f)) ξ)=0:=by
  have hp:Integrable (fun ξ:ℝ=>pole ν a (-2*Real.pi*ξ)*pole μ 0 (-2*Real.pi*ξ)):=
    (mixed_same_half_integrable ν μ a 0 hν hμ).comp_mul_left' (by positivity : -2*Real.pi≠0)
  constructor
  · simp_rw [scalar_baseline_pair μ ν a _ hμ hν f]
    exact hp.neg.smul_const _
  · simp_rw [scalar_baseline_pair μ ν a _ hμ hν f]
    rw [integral_smul_const,integral_neg,Measure.integral_comp_mul_left
      (fun t:ℝ=>pole ν a t*pole μ 0 t) (-2*Real.pi),
      mixed_same_half_integral ν μ a 0 hν hμ,smul_zero,neg_zero,zero_smul]

/-- Literal full-Y Fourier response has source-generated same-causal Hardy cancellation. -/
theorem actual_source_hardy_fourier(F:Index)(sharp:Bool)(f:QuantumTest)(advanced:Bool)
    (μ ν a:ℝ)(hμ:0<μ)(hν:0<ν):
    Integrable (fun ξ:ℝ=>𝓕 (scalarWave ν a) ξ • 𝓕 (sourceWave F sharp f advanced μ) ξ) ∧
      (∫ξ:ℝ,𝓕 (scalarWave ν a) ξ • 𝓕 (sourceWave F sharp f advanced μ) ξ)=0:=by
  have hv:=scalar_wave_integrable ν a hν
  have hu:=actual_source_wave_integrable F sharp f advanced μ hμ
  have hb:=constant_wave_integrable μ hμ (embed f)
  have hd:=actual_wave_correction_integrable F sharp f advanced μ hμ
  have hFd:=actual_wave_correction_fourier_integrable F sharp f advanced μ hμ
  have hdi:=fourier_smul_integrable (scalarWave ν a) (waveCorrection F sharp f advanced μ) hv hd hFd
  have hdz:=causal_fourier_zero (scalarWave ν a) (waveCorrection F sharp f advanced μ) hv hd hFd
    (actual_wave_correction_continuous F sharp f advanced μ) (scalar_correction_zero F sharp f advanced μ ν a)
  have hbase:=scalar_baseline_hardy μ ν a hμ hν f
  simp only [waveCorrection] at hdi hdz
  exact append_fourier_zero (scalarWave ν a) (sourceWave F sharp f advanced μ)
    (causalWave μ (fun _=>embed f)) hu hb hdi hdz hbase.1 hbase.2

theorem causal_line_nonreal(advanced:Bool)(μ w:ℝ)(hμ:0<μ):
    (line (FullYPairedParseval.direction advanced*μ) w).im≠0:=by
  rw [line_im]
  cases advanced <;> simpa only [FullYPairedParseval.direction,ite_true,Bool.false_eq_true,ite_false,one_mul,
    neg_one_mul,neg_ne_zero] using hμ.ne'
def literalResponse(F:Index)(sharp:Bool)(f:QuantumTest)(advanced:Bool)(μ:ℝ)(hμ:0<μ)(w:ℝ):QuantumTest:=
  if sharp then literalSharpResolvent F (line (FullYPairedParseval.direction advanced*μ) w) (causal_line_nonreal advanced μ w hμ) f
    else literalCoreResolvent F (line (FullYPairedParseval.direction advanced*μ) w) (causal_line_nonreal advanced μ w hμ) f
private def frequencyScale(advanced:Bool):ℝ:= -FullYPairedParseval.direction advanced*(2*Real.pi)
private theorem scale_ne(advanced:Bool):frequencyScale advanced≠0:=by
  cases advanced <;> simp [frequencyScale,FullYPairedParseval.direction,Real.pi_ne_zero]
private theorem line_scale(advanced:Bool)(μ ξ:ℝ):
    line (FullYPairedParseval.direction advanced*μ) (frequencyScale advanced*ξ)=sourceLine advanced μ ξ:=by
  cases advanced <;> simp only [line,frequencyScale,sourceLine,FullYPairedParseval.direction,ite_true,Bool.false_eq_true,
    ite_false,Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_one,Complex.ofReal_ofNat]
  all_goals ring
private theorem scalar_pole_scale(advanced:Bool)(ν a ξ:ℝ):
    pole (FullYPairedParseval.direction advanced*ν) a (frequencyScale advanced*ξ)=
      (FullYPairedParseval.direction advanced:ℂ)*pole ν (FullYPairedParseval.direction advanced*a) (-2*Real.pi*ξ):=by
  cases advanced
  · simp only [FullYPairedParseval.direction,ite_false,Bool.false_eq_true,one_mul,Complex.ofReal_one,
      frequencyScale,neg_one_mul]
    congr 2
    ring
  · simp only [FullYPairedParseval.direction,ite_true,Complex.ofReal_neg,Complex.ofReal_one,
      frequencyScale,neg_neg,one_mul,pole,neg_mul,←inv_neg]
    congr 1
    simp only [line,Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_ofNat]
    ring
private theorem scalar_response_fourier(advanced:Bool)(ν a ξ:ℝ)(hν:0<ν):
    ((FullYPairedParseval.direction advanced:ℂ)*Complex.I)*𝓕 (scalarWave ν (FullYPairedParseval.direction advanced*a)) ξ=
      pole (FullYPairedParseval.direction advanced*ν) a (frequencyScale advanced*ξ):=by
  rw [scalar_wave_fourier ν (FullYPairedParseval.direction advanced*a) ξ hν,scalar_pole_scale]
  ring_nf
  simp only [Complex.I_sq]
  ring
private theorem response_fourier(F:Index)(sharp:Bool)(f:QuantumTest)(advanced:Bool)
    (μ:ℝ)(hμ:0<μ)(ξ:ℝ):
    embed (literalResponse F sharp f advanced μ hμ (frequencyScale advanced*ξ))=
      ((FullYPairedParseval.direction advanced:ℂ)*Complex.I) • 𝓕 (sourceWave F sharp f advanced μ) ξ:=by
  unfold literalResponse
  simp only [line_scale]
  exact (actual_source_wave_fourier F sharp f advanced μ hμ ξ).symm
private theorem double_phase(advanced:Bool)(c:ℂ):
    (((FullYPairedParseval.direction advanced:ℂ)*Complex.I)*c)*((FullYPairedParseval.direction advanced:ℂ)*Complex.I)= -c:=by
  cases advanced <;> simp only [FullYPairedParseval.direction,ite_true,Bool.false_eq_true,ite_false,
    Complex.ofReal_one,Complex.ofReal_neg,neg_mul,one_mul]
  all_goals ring_nf; simp only [Complex.I_sq];ring
private theorem weighted_response_fourier(F:Index)(sharp:Bool)(f:QuantumTest)(advanced:Bool)
    (μ ν a:ℝ)(hμ:0<μ)(hν:0<ν)(ξ:ℝ):
    pole (FullYPairedParseval.direction advanced*ν) a (frequencyScale advanced*ξ) •
      embed (literalResponse F sharp f advanced μ hμ (frequencyScale advanced*ξ))=
      -(𝓕 (scalarWave ν (FullYPairedParseval.direction advanced*a)) ξ • 𝓕 (sourceWave F sharp f advanced μ) ξ):=by
  rw [←scalar_response_fourier advanced ν a ξ hν,response_fourier,smul_smul,double_phase,neg_smul]

private theorem recover_scaled_integral {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]
    (c:ℝ)(hc:c≠0)(f:ℝ→E):
    (∫w:ℝ,f w)=|c| • ∫ξ:ℝ,f (c*ξ):=by
  rw [Measure.integral_comp_mul_left,smul_smul,←abs_mul,mul_inv_cancel₀ hc,abs_one,one_smul]

/-- The entire original full-Y response, on either causal branch, annihilates a same-half-plane pole. -/
theorem actual_same_causal_pole_response(F:Index)(sharp:Bool)(f:QuantumTest)(advanced:Bool)
    (μ ν a:ℝ)(hμ:0<μ)(hν:0<ν):
    Integrable (fun w:ℝ=>pole (FullYPairedParseval.direction advanced*ν) a w • embed (literalResponse F sharp f advanced μ hμ w)) ∧
      (∫w:ℝ,pole (FullYPairedParseval.direction advanced*ν) a w • embed (literalResponse F sharp f advanced μ hμ w))=0:=by
  have h:=actual_source_hardy_fourier F sharp f advanced μ ν (FullYPairedParseval.direction advanced*a) hμ hν
  have he:(fun ξ:ℝ=>pole (FullYPairedParseval.direction advanced*ν) a (frequencyScale advanced*ξ) •
      embed (literalResponse F sharp f advanced μ hμ (frequencyScale advanced*ξ)))=
      (fun ξ:ℝ=> -(𝓕 (scalarWave ν (FullYPairedParseval.direction advanced*a)) ξ • 𝓕 (sourceWave F sharp f advanced μ) ξ)):=
    funext (weighted_response_fourier F sharp f advanced μ ν a hμ hν)
  refine ⟨(integrable_comp_mul_left_iff _ (scale_ne advanced)).mp (he ▸ h.1.neg),?_⟩
  rw [recover_scaled_integral (frequencyScale advanced) (scale_ne advanced),he,integral_neg,h.2,neg_zero,smul_zero]

end LowEnergy.FullYDynamicResponse
