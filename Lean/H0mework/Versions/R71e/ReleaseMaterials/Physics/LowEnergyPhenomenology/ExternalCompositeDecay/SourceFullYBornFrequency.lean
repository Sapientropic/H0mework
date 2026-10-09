import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceFullYHardyResponse
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.CompositeFullYBorn
open MeasureTheory Filter Set
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussDiagonalHistory GaussFockPair GaussUnitaryHistory
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge FullYDynamicSource
open FullYDynamicSourceNext FullYPairedParseval FullYDynamicResponse
open SourceResolventBandLimit SourceResolventLorentzian SourceScalarPairedTransport
open scoped Topology FourierTransform InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
attribute [local irreducible] embed sourcePair literalCoreResolvent literalSharpResolvent
  sourceOrbit sourceSpace sourceWave waveCorrection

section Fourier
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E]
omit [CompleteSpace E] in
private theorem correction_square_integrable(d:ℝ→E)(hd:Integrable d)(hF:Integrable (𝓕 d)):
    Integrable (fun ξ:ℝ=>‖𝓕 d ξ‖^2):=by
  apply (hF.norm.const_mul (∫t:ℝ,‖d t‖)).mono'
    ((fourier_continuous_of_integrable d hd).norm.pow 2).aestronglyMeasurable
  apply Eventually.of_forall
  intro ξ
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),pow_two]
  exact mul_le_mul_of_nonneg_right (fourier_bound d ξ) (norm_nonneg _)

private theorem baseline_square_integrable(μ:ℝ)(hμ:0<μ)(x:E):
    Integrable (fun ξ:ℝ=>‖𝓕 (causalWave μ (fun _=>x)) ξ‖^2):=by
  have he(ξ:ℝ):‖𝓕 (causalWave μ (fun _=>x)) ξ‖^2=
      kernel μ 0 (-2*Real.pi*ξ)*‖x‖^2:=by
    rw [constant_wave_fourier μ hμ,norm_smul,mul_pow]
    congr 1
    have h:=inverse_norm_square μ 0 (-2*Real.pi*ξ)
    simpa only [norm_div,Complex.norm_I,one_div,Complex.ofReal_zero,zero_sub,
      norm_inv,norm_neg,line,mul_comm (μ:ℂ) Complex.I] using h
  simp_rw [he]
  exact ((kernel_integrable μ 0 hμ).comp_mul_left' (by positivity : -2*Real.pi≠0)).mul_const _

omit [CompleteSpace E] in
private theorem assemble_fourier_square(u b:ℝ→E)(hu:Integrable u)(hb:Integrable b)
    (hd:Integrable (𝓕 (u-b)))(hb2:Integrable (fun ξ:ℝ=>‖𝓕 b ξ‖^2)):
    Integrable (fun ξ:ℝ=>‖𝓕 u ξ‖^2):=by
  have hdc:Continuous (𝓕 (u-b)):=fourier_continuous_of_integrable _ (hu.sub hb)
  have hbc:Continuous (𝓕 b):=fourier_continuous_of_integrable _ hb
  have hD:MemLp (𝓕 (u-b)) 2:=
    (memLp_two_iff_integrable_sq_norm hdc.aestronglyMeasurable).mpr
      (correction_square_integrable _ (hu.sub hb) hd)
  have hB:MemLp (𝓕 b) 2:=
    (memLp_two_iff_integrable_sq_norm hbc.aestronglyMeasurable).mpr hb2
  have he:𝓕 u=𝓕 (u-b)+𝓕 b:=by
    funext ξ
    simp only [Pi.add_apply,fourier_sub_integrable u b hu hb,sub_add_cancel]
  rw [he]
  exact (memLp_two_iff_integrable_sq_norm (hdc.add hbc).aestronglyMeasurable).mp (hD.add hB)
end Fourier

private def frequencyScale(advanced:Bool):ℝ:= -FullYPairedParseval.direction advanced*(2*Real.pi)
private theorem scale_ne(advanced:Bool):frequencyScale advanced≠0:=by
  cases advanced <;> simp [frequencyScale,FullYPairedParseval.direction,Real.pi_ne_zero]
private theorem line_scale(advanced:Bool)(μ ξ:ℝ):
    line (FullYPairedParseval.direction advanced*μ) (frequencyScale advanced*ξ)=sourceLine advanced μ ξ:=by
  cases advanced <;> simp only [line,frequencyScale,sourceLine,FullYPairedParseval.direction,
    ite_true,Bool.false_eq_true,ite_false,Complex.ofReal_mul,Complex.ofReal_neg,
    Complex.ofReal_one,Complex.ofReal_ofNat]
  all_goals ring

private theorem actual_response_fourier(F:Index)(sharp:Bool)(f:QuantumTest)(advanced:Bool)
    (μ:ℝ)(hμ:0<μ)(ξ:ℝ):
    embed (literalResponse F sharp f advanced μ hμ (frequencyScale advanced*ξ))=
      ((FullYPairedParseval.direction advanced:ℂ)*Complex.I) • 𝓕 (sourceWave F sharp f advanced μ) ξ:=by
  simp only [literalResponse,line_scale]
  exact (actual_source_wave_fourier F sharp f advanced μ hμ ξ).symm

/-- The original full-Y response, on either independent leg, pays its positive full-frequency norm. -/
theorem actual_response_square_integrable(F:Index)(sharp:Bool)(f:QuantumTest)(advanced:Bool)
    (μ:ℝ)(hμ:0<μ):
    Integrable (fun w:ℝ=>‖embed (literalResponse F sharp f advanced μ hμ w)‖^2):=by
  have h:=assemble_fourier_square (sourceWave F sharp f advanced μ)
    (causalWave μ (fun _=>embed f)) (actual_source_wave_integrable F sharp f advanced μ hμ)
    (constant_wave_integrable μ hμ (embed f))
    (by simpa only [waveCorrection] using actual_wave_correction_fourier_integrable F sharp f advanced μ hμ)
    (baseline_square_integrable μ hμ (embed f))
  apply (integrable_comp_mul_left_iff _ (scale_ne advanced)).mp
  apply h.congr
  apply Eventually.of_forall
  intro ξ
  dsimp only
  rw [actual_response_fourier,norm_smul]
  cases advanced <;> simp [FullYPairedParseval.direction]

theorem actual_response_continuous(F:Index)(sharp:Bool)(f:QuantumTest)(advanced:Bool)
    (μ:ℝ)(hμ:0<μ):Continuous (fun w:ℝ=>embed (literalResponse F sharp f advanced μ hμ w)):=by
  have h:Continuous (fun w:ℝ=>((FullYPairedParseval.direction advanced:ℂ)*Complex.I) •
      𝓕 (sourceWave F sharp f advanced μ) ((frequencyScale advanced)⁻¹*w)):=
    (continuous_const : Continuous (fun _:ℝ=>(FullYPairedParseval.direction advanced:ℂ)*Complex.I)).smul
      ((fourier_continuous_of_integrable _
        (actual_source_wave_integrable F sharp f advanced μ hμ)).comp
          ((continuous_const : Continuous (fun _:ℝ=>(frequencyScale advanced)⁻¹)).mul continuous_id))
  apply h.congr
  intro w
  have he:=actual_response_fourier F sharp f advanced μ hμ ((frequencyScale advanced)⁻¹*w)
  simpa only [←mul_assoc,mul_inv_cancel₀ (scale_ne advanced),one_mul] using he.symm

/-- A core word is bounded on the finite orbit generated by the actual input and original Y. -/
def sourceReader(F:Index)(sharp:Bool)(f:QuantumTest)(A:End):H→L[ℂ]H:=
  ((embed.comp (A.comp ((sourceOrbit F sharp f).subtype.comp
    (sourceEquiv F sharp f).symm.toLinearMap))).toContinuousLinearMap).comp
      (sourceSpace F sharp f).orthogonalProjectionOnto

theorem source_reader_return(F:Index)(sharp:Bool)(f q:QuantumTest)(A:End)
    (hq:q∈sourceOrbit F sharp f):sourceReader F sharp f A (embed q)=embed (A q):=by
  let x:=sourceEquiv F sharp f ⟨q,hq⟩
  have hx:(x:H)=embed q:=rfl
  rw [←hx]
  simp only [sourceReader,ContinuousLinearMap.comp_apply,
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
    LinearMap.coe_toContinuousLinearMap',LinearMap.comp_apply,
    LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply,Submodule.subtype_apply,x]

theorem actual_response_orbit(F:Index)(sharp:Bool)(f:QuantumTest)(advanced:Bool)
    (μ:ℝ)(hμ:0<μ)(w:ℝ):literalResponse F sharp f advanced μ hμ w∈sourceOrbit F sharp f:=by
  rw [literalResponse,←source_resolvent_literal_return]
  exact Subtype.property _

theorem actual_core_word_square_integrable(F:Index)(sharp:Bool)(f:QuantumTest)(advanced:Bool)
    (μ:ℝ)(hμ:0<μ)(A:End):
    Integrable (fun w:ℝ=>‖embed (A (literalResponse F sharp f advanced μ hμ w))‖^2):=by
  let T:=sourceReader F sharp f A
  have he(w:ℝ):embed (A (literalResponse F sharp f advanced μ hμ w))=
      T (embed (literalResponse F sharp f advanced μ hμ w)):=
    (source_reader_return F sharp f _ A (actual_response_orbit F sharp f advanced μ hμ w)).symm
  simp_rw [he]
  apply ((actual_response_square_integrable F sharp f advanced μ hμ).const_mul (‖T‖^2)).mono'
    ((T.continuous.comp (actual_response_continuous F sharp f advanced μ hμ)).norm.pow 2).aestronglyMeasurable
  apply Eventually.of_forall
  intro w
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact (pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm _) 2).trans_eq (mul_pow _ _ _)

end LowEnergy.CompositeFullYBorn
