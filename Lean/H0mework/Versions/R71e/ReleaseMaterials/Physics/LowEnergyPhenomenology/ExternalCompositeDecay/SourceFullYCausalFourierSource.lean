import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceFullYUncutRetardedKernel
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.FullYPairedParseval
open MeasureTheory Filter Set
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussDiagonalHistory GaussUnitaryHistory
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge FullYDynamicSource FullYDynamicSourceNext
open SourceResolventBandLimit
open scoped Topology FourierTransform InnerProductSpace Interval
attribute [local irreducible] embed literalCoreResolvent literalSharpResolvent sourceOrbit sourceSpace

def direction(advanced:Bool):ℝ:=if advanced then -1 else 1

section Wave
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E]

def causalWave(μ:ℝ)(u:ℝ→E):ℝ→E:=
  (Ioi 0).indicator (fun t:ℝ=>(Real.exp (-μ*t):ℂ) • u t)

theorem exp_polynomial_integrable(μ C:ℝ)(hμ:0<μ):
    IntegrableOn (fun t:ℝ=>Real.exp (-μ*t)*(∑j∈Finset.range 57,(|t| * C)^j)) (Ioi 0):=by
  have hterm(j:ℕ):IntegrableOn (fun t:ℝ=>C^j*(t^j*Real.exp (-μ*t))) (Ioi 0):=by
    have h:=integrableOn_rpow_mul_exp_neg_mul_rpow
      (s:=(j:ℝ)) (p:=1) (b:=μ) (by have hj:(0:ℝ)≤j:=Nat.cast_nonneg j;linarith) one_pos hμ
    simpa only [Real.rpow_natCast,Real.rpow_one] using! h.const_mul (C^j)
  apply (integrable_finsetSum (Finset.range 57) (fun j _=>hterm j)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change 0<t at ht
  simp only [abs_of_pos ht,Finset.mul_sum,mul_pow]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem causal_wave_integrable(μ:ℝ)(hμ:0<μ)(u:ℝ→E)(hu:Continuous u)(C D:ℝ)
    (hb:∀t:ℝ,‖u t‖ ≤ (∑j∈Finset.range 57,(|t| * C)^j)*D):
    Integrable (causalWave μ u):=by
  unfold causalWave
  apply (integrable_indicator_iff measurableSet_Ioi).mpr
  apply ((exp_polynomial_integrable μ C hμ).mul_const D).mono'
    (((Complex.continuous_ofReal.comp (by fun_prop : Continuous (fun t:ℝ=>Real.exp (-μ*t)))).smul hu).aestronglyMeasurable.restrict)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _ht
  change ‖(Real.exp (-μ*t):ℂ) • u t‖ ≤ (Real.exp (-μ*t)*(∑j∈Finset.range 57,(|t| * C)^j))*D
  simp only [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact (mul_le_mul_of_nonneg_left (hb t) (Real.exp_pos _).le).trans_eq (mul_assoc _ _ _).symm

private theorem wave_phase_eq(μ ξ:ℝ)(u:ℝ→E)(t:ℝ):
    𝐞 (-inner ℝ t ξ) • causalWave μ u t=
      (Ioi 0).indicator (fun t:ℝ=>Complex.exp (t • (Complex.I*line μ (-2*Real.pi*ξ))) • u t) t:=by
  by_cases ht:t∈Ioi (0:ℝ)
  · simp only [causalWave,indicator_of_mem ht,Circle.smul_def,Real.fourierChar_apply,smul_smul,
      Complex.ofReal_exp,←Complex.exp_add]
    congr 2
    simp only [Real.inner_apply,Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_ofNat,
      Complex.real_smul,line]
    ring_nf
    simp only [Complex.I_sq]
    ring
  · simp only [causalWave,indicator_of_notMem ht,smul_zero]

theorem causal_wave_fourier(μ ξ:ℝ)(u:ℝ→E):
    𝓕 (causalWave μ u) ξ=∫t:ℝ in Ioi 0,
      Complex.exp (t • (Complex.I*line μ (-2*Real.pi*ξ))) • u t:=by
  rw [Real.fourier_eq]
  simp_rw [wave_phase_eq]
  exact integral_indicator measurableSet_Ioi

theorem causal_wave_modulated_integrable(μ ξ:ℝ)(u:ℝ→E)(hi:Integrable (causalWave μ u)):
    IntegrableOn (fun t:ℝ=>Complex.exp (t • (Complex.I*line μ (-2*Real.pi*ξ))) • u t) (Ioi 0):=by
  have hf:=Real.fourierIntegral_convergent_iff ξ |>.mpr hi
  apply (integrable_indicator_iff measurableSet_Ioi).mp
  exact hf.congr (Eventually.of_forall (wave_phase_eq μ ξ u))

theorem causal_fourier_limit(μ ξ:ℝ)(u:ℝ→E)(hi:Integrable (causalWave μ u)):
    Tendsto (fun T:ℝ=>∫t in (0:ℝ)..T,
      Complex.exp (t • (Complex.I*line μ (-2*Real.pi*ξ))) • u t) atTop
      (𝓝 (𝓕 (causalWave μ u) ξ)):=by
  rw [causal_wave_fourier]
  exact intervalIntegral_tendsto_integral_Ioi 0 (causal_wave_modulated_integrable μ ξ u hi) tendsto_id
theorem direction_wave_integrable(μ:ℝ)(hμ:0<μ)(u:ℝ→E)(hu:Continuous u)(D:ℝ)
    (hb:∃C:ℝ,∀t:ℝ,‖u t‖ ≤ (∑j∈Finset.range 57,(|t| * C)^j)*D)(advanced:Bool):
    Integrable (causalWave μ (fun t:ℝ=>u (direction advanced*t))):=by
  obtain ⟨C,hC⟩:=hb
  apply causal_wave_integrable μ hμ _ (hu.comp (continuous_const.mul continuous_id)) C D
  intro t
  have h:=hC (direction advanced*t)
  cases advanced <;> simpa only [direction,ite_true,Bool.false_eq_true,ite_false,one_mul,
    neg_one_mul,abs_neg,Function.comp_apply,Pi.mul_apply,id_eq] using h
end Wave

def sourceWave(F:Index)(sharp:Bool)(f:QuantumTest)(advanced:Bool)(μ:ℝ):ℝ→H:=
  causalWave μ (fun t:ℝ=>embed (literalCoreTime F sharp f (direction advanced*t)))
def sourceLine(advanced:Bool)(μ ξ:ℝ):ℂ:=
  (direction advanced:ℂ)*line μ (-2*Real.pi*ξ)
theorem source_line_half_plane(advanced:Bool)(μ ξ:ℝ)(hμ:0<μ):
    if advanced then (sourceLine advanced μ ξ).im<0 else 0<(sourceLine advanced μ ξ).im:=by
  cases advanced <;> simpa only [sourceLine,direction,ite_true,Bool.false_eq_true,ite_false,
    Complex.ofReal_one,Complex.ofReal_neg,one_mul,neg_mul,Complex.neg_im,line_im,neg_neg,neg_lt_zero] using hμ

private theorem source_time_bound(F:Index)(sharp:Bool)(f:QuantumTest):
    ∃C:ℝ,∀t:ℝ,‖embed (literalCoreTime F sharp f t)‖ ≤
      (∑j∈Finset.range 57,(|t| * C)^j)*‖embed f‖:=by
  obtain ⟨C,_hC,hC⟩:=actual_source_time_polynomial_bound F sharp f
  refine ⟨C,fun t=>?_⟩
  let x:=sourceEquiv F sharp f ⟨f,sourceOrbit_input F sharp f⟩
  have he:embed (literalCoreTime F sharp f t)=
      (SourceFiniteUnitary.time (sourceGenerator F sharp f) t x:H):=
    congrArg Subtype.val ((sourceEquiv F sharp f).apply_symm_apply _)
  rw [he]
  exact ((SourceFiniteUnitary.time (sourceGenerator F sharp f) t).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (hC t) (norm_nonneg x))

/-- Original source support and grade pay Bochner integrability on either physical causal half-line. -/
theorem actual_source_wave_integrable(F:Index)(sharp:Bool)(f:QuantumTest)(advanced:Bool)
    (μ:ℝ)(hμ:0<μ):Integrable (sourceWave F sharp f advanced μ):=by
  exact direction_wave_integrable μ hμ (fun t:ℝ=>embed (literalCoreTime F sharp f t))
    (continuous_iff_continuousAt.mpr (fun t=>(literal_core_time_derivative F sharp f t).continuousAt))
    ‖embed f‖ (source_time_bound F sharp f) advanced

/-- The Fourier sign is determined by the original causal phase, including the independent advanced branch. -/
theorem actual_source_wave_fourier(F:Index)(sharp:Bool)(f:QuantumTest)(advanced:Bool)
    (μ:ℝ)(hμ:0<μ)(ξ:ℝ):
    ((direction advanced:ℂ)*Complex.I) • 𝓕 (sourceWave F sharp f advanced μ) ξ=
      embed (if sharp then literalSharpResolvent F (sourceLine advanced μ ξ)
        (by have h:=source_line_half_plane advanced μ ξ hμ;cases advanced;exact h.ne';exact h.ne) f
        else literalCoreResolvent F (sourceLine advanced μ ξ)
        (by have h:=source_line_half_plane advanced μ ξ hμ;cases advanced;exact h.ne';exact h.ne) f):=by
  have hi:=actual_source_wave_integrable F sharp f advanced μ hμ
  have hl: Tendsto (uncutCausalVector F sharp f advanced (sourceLine advanced μ ξ)) atTop
      (𝓝 (((direction advanced:ℂ)*Complex.I) • 𝓕 (sourceWave F sharp f advanced μ) ξ)):=by
    have h:=(causal_fourier_limit μ ξ
      (fun t:ℝ=>embed (literalCoreTime F sharp f (direction advanced*t))) hi).const_smul
        ((direction advanced:ℂ)*Complex.I)
    apply h.congr' (Eventually.of_forall (fun T=>?_))
    cases advanced
    · simp only [uncutCausalVector,sourceLine,direction,Bool.false_eq_true,ite_false,
        Complex.ofReal_one,one_mul]
      rfl
    · simp only [uncutCausalVector,sourceLine,direction,ite_true,Complex.ofReal_neg,
        Complex.ofReal_one,neg_mul,one_mul,neg_smul]
      congr 2
      apply intervalIntegral.integral_congr
      intro t _
      change Complex.exp (t • (Complex.I*line μ (-(2*Real.pi*ξ)))) •
          embed (literalCoreTime F sharp f (-t))=
        Complex.exp ((-t) • (Complex.I*(-line μ (-(2*Real.pi*ξ))))) •
          embed (literalCoreTime F sharp f (-t))
      simp only [mul_neg,smul_neg,neg_smul,neg_neg]
  exact tendsto_nhds_unique hl (actual_original_uncut_retarded_kernel F sharp f advanced
    (sourceLine advanced μ ξ) (source_line_half_plane advanced μ ξ hμ))

end LowEnergy.FullYPairedParseval
