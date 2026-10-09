import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceFullYCausalFourierSource
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceResolventLorentzian
import Mathlib.Topology.Algebra.Indicator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.FullYPairedParseval
open MeasureTheory Filter Set
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussDiagonalHistory GaussUnitaryHistory
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge FullYDynamicSource FullYDynamicSourceNext
open SourceResolventBandLimit SourceResolventLorentzian SourceScalarPairedTransport
open scoped Topology FourierTransform InnerProductSpace Interval
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
attribute [local irreducible] embed literalCoreResolvent literalSharpResolvent sourceOrbit sourceSpace

section Fourier
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E]
omit [CompleteSpace E] in
theorem constant_wave_integrable(μ:ℝ)(hμ:0<μ)(x:E):Integrable (causalWave μ (fun _=>x)):=by
  apply (integrable_indicator_iff measurableSet_Ioi).mpr
  exact ((integrableOn_exp_mul_Ioi (neg_neg_of_pos hμ) 0).ofReal).smul_const x

theorem constant_wave_fourier(μ:ℝ)(hμ:0<μ)(x:E)(ξ:ℝ):
    𝓕 (causalWave μ (fun _=>x)) ξ=(Complex.I/line μ (-2*Real.pi*ξ)) • x:=by
  rw [causal_wave_fourier,integral_smul_const]
  have hh:(Complex.I*line μ (-2*Real.pi*ξ)).re<0:=by
    simpa only [Complex.mul_re,Complex.I_re,zero_mul,Complex.I_im,one_mul,zero_sub,line_im] using neg_neg_of_pos hμ
  have he:(fun t:ℝ=>Complex.exp (t • (Complex.I*line μ (-2*Real.pi*ξ))))=
      (fun t:ℝ=>Complex.exp ((Complex.I*line μ (-2*Real.pi*ξ))*(t:ℂ))):=by
    funext t
    rw [Complex.real_smul,mul_comm]
  rw [he,integral_exp_mul_complex_Ioi hh 0]
  simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero]
  congr 1
  have hz:line μ (-2*Real.pi*ξ)≠0:=by
    intro hz
    have h:=congrArg Complex.im hz
    apply hμ.ne'
    simpa only [line_im,Complex.zero_im] using h
  field_simp [hz,Complex.I_ne_zero]
  norm_num [Complex.I_sq,div_eq_mul_inv]

omit [CompleteSpace E] in
theorem fourier_sub_integrable(f g:ℝ→E)(hf:Integrable f)(hg:Integrable g)(ξ:ℝ):
    𝓕 (f-g) ξ=𝓕 f ξ-𝓕 g ξ:=by
  rw [Real.fourier_eq,Real.fourier_eq,Real.fourier_eq]
  simp only [Pi.sub_apply,smul_sub]
  exact integral_sub (Real.fourierIntegral_convergent_iff ξ |>.mpr hf)
    (Real.fourierIntegral_convergent_iff ξ |>.mpr hg)

omit [CompleteSpace E] in
theorem fourier_continuous_of_integrable(f:ℝ→E)(hf:Integrable f):Continuous (𝓕 f):=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hf
omit [CompleteSpace E] in
theorem fourier_bound(f:ℝ→E)(ξ:ℝ):‖𝓕 f ξ‖ ≤ ∫t:ℝ,‖f t‖:=
  VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

omit [CompleteSpace E] in
theorem correction_wave_continuous(μ:ℝ)(u:ℝ→E)(x:E)(hu:Continuous u)(h0:u 0=x):
    Continuous (causalWave μ u-causalWave μ (fun _=>x)):=by
  have he:causalWave μ u-causalWave μ (fun _=>x)=
      (Ioi 0).indicator (fun t:ℝ=>(Real.exp (-μ*t):ℂ) • (u t-x)):=by
    funext t
    by_cases ht:t∈Ioi (0:ℝ)
    · simp only [causalWave,Pi.sub_apply,indicator_of_mem ht,smul_sub]
    · simp only [causalWave,Pi.sub_apply,indicator_of_notMem ht,sub_self]
  rw [he]
  apply continuous_indicator
  · intro t ht
    simp only [frontier_Ioi,mem_singleton_iff] at ht
    subst t
    rw [h0,sub_self,smul_zero]
  · exact ((Complex.continuous_ofReal.comp (by fun_prop : Continuous (fun t:ℝ=>Real.exp (-μ*t)))).smul
      (hu.sub continuous_const)).continuousOn
omit [CompleteSpace E] in
private theorem fourier_difference_return(f b:ℝ→E)(hf:Integrable f)(hb:Integrable b)
    (β c:ℂ)(ξ:ℝ)(x y:E)(hF:β • 𝓕 f ξ=x)(hB:β • 𝓕 b ξ= -c • y):
    β • 𝓕 (f-b) ξ=x+c • y:=by
  rw [fourier_sub_integrable f b hf hb,smul_sub,hF,hB,neg_smul,sub_neg_eq_add]
end Fourier

private theorem source_nonreal(advanced:Bool)(μ ξ:ℝ)(hμ:0<μ):(sourceLine advanced μ ξ).im≠0:=by
  have h:=source_line_half_plane advanced μ ξ hμ
  cases advanced
  · exact h.ne'
  · exact h.ne
private def branchR(F:Index)(sharp:Bool)(z:ℂ)(hz:z.im≠0):End:=
  if sharp then literalSharpResolvent F z hz else literalCoreResolvent F z hz
private def branchA(F:Index)(sharp:Bool):End:=compressionCore F+sourceY sharp
private theorem branch_left(F:Index)(sharp:Bool)(z:ℂ)(hz:z.im≠0):
    branchR F sharp z hz*(branchA F sharp-z • (1:End))=1:=by
  cases sharp
  · exact literal_core_left_inverse F z hz
  · exact literal_sharp_left_inverse F z hz

private theorem inverse_second_jet {V:Type*}[AddCommGroup V][Module ℂ V]
    (A R:V→ₗ[ℂ]V)(z:ℂ)(hz:z≠0)(hi:R*(A-z • (1:V→ₗ[ℂ]V))=1):
    R+z⁻¹ • 1=z⁻¹^2 • (R*A^2-A):=by
  have h:z • R=R*A-1:=by
    simp only [mul_sub,mul_smul_comm,mul_one] at hi
    exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans (sub_eq_iff_eq_add.mp hi).symm)
  have hR:R=z⁻¹ • (R*A-1):=by rw [←h,smul_smul,inv_mul_cancel₀ hz,one_smul]
  have hRA:R*A=z⁻¹ • (R*A^2-A):=by
    conv_lhs => rw [hR]
    simp only [smul_mul_assoc,sub_mul,one_mul,mul_assoc,pow_two]
  calc
    _=z⁻¹ • (R*A):=by
      conv_lhs => rw [hR]
      rw [smul_sub]
      abel
    _=z⁻¹^2 • (R*A^2-A):=by
      have h:=congrArg (fun B:V→ₗ[ℂ]V=>z⁻¹ • B) hRA
      exact h.trans (by rw [smul_smul];congr 1;exact (pow_two _).symm)

def waveCorrection(F:Index)(sharp:Bool)(f:QuantumTest)(advanced:Bool)(μ:ℝ):ℝ→H:=
  sourceWave F sharp f advanced μ-causalWave μ (fun _=>embed f)

theorem actual_wave_correction_continuous(F:Index)(sharp:Bool)(f:QuantumTest)(advanced:Bool)(μ:ℝ):
    Continuous (waveCorrection F sharp f advanced μ):=by
  apply correction_wave_continuous
  · exact (continuous_iff_continuousAt.mpr
      (fun t=>(literal_core_time_derivative F sharp f t).continuousAt)).comp (continuous_const.mul continuous_id)
  · simp only [mul_zero,literal_core_time_zero]
theorem actual_wave_correction_integrable(F:Index)(sharp:Bool)(f:QuantumTest)(advanced:Bool)
    (μ:ℝ)(hμ:0<μ):Integrable (waveCorrection F sharp f advanced μ):=
  (actual_source_wave_integrable F sharp f advanced μ hμ).sub (constant_wave_integrable μ hμ (embed f))

private theorem direction_I_norm(advanced:Bool):‖(direction advanced:ℂ)*Complex.I‖=1:=by
  cases advanced <;> simp [direction]
private theorem response_norm_bound(F:Index)(sharp:Bool)(f:QuantumTest)(advanced:Bool)
    (μ:ℝ)(hμ:0<μ)(ξ:ℝ):
    ‖embed (branchR F sharp (sourceLine advanced μ ξ) (source_nonreal advanced μ ξ hμ) f)‖ ≤
      ∫t:ℝ,‖sourceWave F sharp f advanced μ t‖:=by
  have he:=actual_source_wave_fourier F sharp f advanced μ hμ ξ
  have hn:=congrArg norm he
  rw [norm_smul,direction_I_norm,one_mul] at hn
  cases sharp <;> exact hn.symm.trans_le (fourier_bound _ ξ)

private theorem baseline_return(advanced:Bool)(μ:ℝ)(hμ:0<μ)(f:QuantumTest)(ξ:ℝ):
    ((direction advanced:ℂ)*Complex.I) • 𝓕 (causalWave μ (fun _=>embed f)) ξ=
      -(sourceLine advanced μ ξ)⁻¹ • embed f:=by
  rw [constant_wave_fourier μ hμ,smul_smul]
  congr 1
  cases advanced <;> simp only [direction,sourceLine,ite_true,Bool.false_eq_true,ite_false,
    Complex.ofReal_one,Complex.ofReal_neg,one_mul,neg_mul,inv_neg,neg_neg,div_eq_mul_inv]
  all_goals simp only [←mul_assoc,Complex.I_mul_I,neg_one_mul,neg_neg]

private theorem source_inverse_square(advanced:Bool)(μ ξ:ℝ):
    ‖(sourceLine advanced μ ξ)⁻¹‖^2=kernel μ 0 (-2*Real.pi*ξ):=by
  have h:=inverse_norm_square μ 0 (-2*Real.pi*ξ)
  cases advanced <;> simpa only [sourceLine,direction,ite_true,Bool.false_eq_true,ite_false,
    Complex.ofReal_one,Complex.ofReal_neg,neg_mul,one_mul,inv_neg,norm_neg,Complex.ofReal_zero,
    zero_sub,norm_inv,line,mul_comm (μ:ℂ) Complex.I] using h

attribute [local irreducible] sourceWave

private theorem correction_return(F:Index)(sharp:Bool)(f:QuantumTest)(advanced:Bool)
    (μ:ℝ)(hμ:0<μ)(ξ:ℝ):
    ((direction advanced:ℂ)*Complex.I) • 𝓕 (waveCorrection F sharp f advanced μ) ξ=
      embed (branchR F sharp (sourceLine advanced μ ξ) (source_nonreal advanced μ ξ hμ) f)+
        (sourceLine advanced μ ξ)⁻¹ • embed f:=by
  have hf:((direction advanced:ℂ)*Complex.I) • 𝓕 (sourceWave F sharp f advanced μ) ξ=
      embed (branchR F sharp (sourceLine advanced μ ξ) (source_nonreal advanced μ ξ hμ) f):=by
    cases sharp <;> exact actual_source_wave_fourier F _ f advanced μ hμ ξ
  exact fourier_difference_return (sourceWave F sharp f advanced μ) (causalWave μ (fun _=>embed f))
    (actual_source_wave_integrable F sharp f advanced μ hμ) (constant_wave_integrable μ hμ (embed f))
    ((direction advanced:ℂ)*Complex.I) (sourceLine advanced μ ξ)⁻¹ ξ _ _ hf
    (baseline_return advanced μ hμ f ξ)

attribute [local irreducible] branchA branchR waveCorrection

private theorem norm_sub_bound {E:Type*}[SeminormedAddCommGroup E](x y:E)(M:ℝ)(h:‖x‖≤M):
    ‖x-y‖≤‖y‖+M:=by
  have hxy:=norm_sub_le x y
  linarith

/-- Two original generator jets pay the whole frequency correction; the bound is generated internally. -/
theorem actual_wave_correction_fourier_integrable(F:Index)(sharp:Bool)(f:QuantumTest)(advanced:Bool)
    (μ:ℝ)(hμ:0<μ):Integrable (𝓕 (waveCorrection F sharp f advanced μ)):=by
  let A:=branchA F sharp
  let D:ℝ:=‖embed (A f)‖+∫t:ℝ,‖sourceWave F sharp ((A^2) f) advanced μ t‖
  have hb(ξ:ℝ):‖𝓕 (waveCorrection F sharp f advanced μ) ξ‖ ≤ kernel μ 0 (-2*Real.pi*ξ)*D:=by
    let z:=sourceLine advanced μ ξ
    let hz:=source_nonreal advanced μ ξ hμ
    let R:=branchR F sharp z hz
    have hz0:z≠0:=by
      intro h
      apply hz
      exact congrArg Complex.im h
    have hid:=congrArg embed (LinearMap.congr_fun (inverse_second_jet A R z hz0
      (branch_left F sharp z hz)) f)
    simp only [LinearMap.add_apply,LinearMap.smul_apply,Module.End.one_apply,LinearMap.sub_apply,
      Module.End.mul_apply,map_add,map_smul,map_sub] at hid
    have hc:((direction advanced:ℂ)*Complex.I) • 𝓕 (waveCorrection F sharp f advanced μ) ξ=
        embed (R f)+z⁻¹ • embed f:=correction_return F sharp f advanced μ hμ ξ
    have hn:=congrArg norm (hc.trans hid)
    rw [norm_smul,direction_I_norm,one_mul,norm_smul,norm_pow] at hn
    rw [hn]
    have hh:‖embed (R ((A^2) f))‖ ≤ ∫t:ℝ,‖sourceWave F sharp ((A^2) f) advanced μ t‖:=
      response_norm_bound F sharp ((A^2) f) advanced μ hμ ξ
    have hB:‖embed (R ((A^2) f))-embed (A f)‖ ≤ D:=norm_sub_bound _ _ _ hh
    exact (mul_le_mul_of_nonneg_left hB (sq_nonneg _)).trans_eq
      (congrArg (fun v:ℝ=>v*D) (source_inverse_square advanced μ ξ))
  have hi:Integrable (fun ξ:ℝ=>kernel μ 0 (-2*Real.pi*ξ)*D):=
    ((kernel_integrable μ 0 hμ).comp_mul_left' (by positivity : -2*Real.pi≠0)).mul_const D
  exact hi.mono' (fourier_continuous_of_integrable _
    (actual_wave_correction_integrable F sharp f advanced μ hμ)).aestronglyMeasurable (Eventually.of_forall hb)

end LowEnergy.FullYPairedParseval
