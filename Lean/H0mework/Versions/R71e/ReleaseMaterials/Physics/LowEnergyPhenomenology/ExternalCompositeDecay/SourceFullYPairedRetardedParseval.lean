import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceFullYCausalCorrectionPrice
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceFullYCofinalResolventUpdate
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.FullYPairedParseval
open MeasureTheory Filter Set
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussDiagonalHistory GaussUnitaryHistory
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge FullYDynamicSource FullYDynamicSourceNext
open SourceResolventBandLimit SourceResolventLorentzian SourceScalarPairedTransport
open scoped Topology FourierTransform InnerProductSpace Interval
attribute [local irreducible] embed literalCoreResolvent literalSharpResolvent sourceOrbit sourceSpace

section Parseval
variable {E:Type*}[NormedAddCommGroup E][InnerProductSpace ℂ E][CompleteSpace E]

omit [CompleteSpace E] in
private theorem fourier_cross_integrable(f g:ℝ→E)(hf:Integrable f)(hg:Integrable g)
    (hFg:Integrable (𝓕 g)):
    Integrable (fun ξ:ℝ=>inner ℂ (𝓕 f ξ) (𝓕 g ξ)):=by
  apply (hFg.norm.const_mul (∫t:ℝ,‖f t‖)).mono'
    ((fourier_continuous_of_integrable f hf).aestronglyMeasurable.inner
      (fourier_continuous_of_integrable g hg).aestronglyMeasurable)
  exact Eventually.of_forall (fun ξ=>(norm_inner_le_norm (𝓕 f ξ) (𝓕 g ξ)).trans
    (mul_le_mul_of_nonneg_right (fourier_bound f ξ) (norm_nonneg _)))

private theorem one_sided_parseval(f g:ℝ→E)(hf:Integrable f)(hg:Integrable g)
    (hgc:Continuous g)(hFg:Integrable (𝓕 g)):
    (∫ξ:ℝ,inner ℂ (𝓕 f ξ) (𝓕 g ξ))=∫t:ℝ,inner ℂ (f t) (g t):=by
  have h:=VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip (innerSL ℂ)
    (L:=innerₗ ℝ) Real.continuous_fourierChar continuous_inner hf hFg
  have he:(innerₗ ℝ).flip=innerₗ ℝ:=by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change inner ℝ y x=inner ℝ x y
    exact real_inner_comm x y
  rw [he] at h
  change (∫ξ:ℝ,inner ℂ (𝓕 f ξ) (𝓕 g ξ))=
    ∫t:ℝ,inner ℂ (f t) (𝓕⁻ (𝓕 g) t) at h
  rw [hgc.fourierInv_fourier_eq hg hFg] at h
  exact h

private theorem paired_parseval_cancellation(u v b c:ℝ→E)
    (hu:Integrable u)(hv:Integrable v)(hb:Integrable b)(hc:Integrable c)
    (huc:Continuous (u-b))(hvc:Continuous (v-c))
    (hFu:Integrable (𝓕 (u-b)))(hFv:Integrable (𝓕 (v-c)))
    (hbase:Integrable (fun ξ:ℝ=>inner ℂ (𝓕 b ξ) (𝓕 c ξ)))
    (hp:∀t:ℝ,inner ℂ (u t) (v t)=inner ℂ (b t) (c t)):
    Integrable (fun ξ:ℝ=>inner ℂ (𝓕 u ξ) (𝓕 v ξ)) ∧
      (∫ξ:ℝ,inner ℂ (𝓕 u ξ) (𝓕 v ξ))=∫ξ:ℝ,inner ℂ (𝓕 b ξ) (𝓕 c ξ):=by
  have hleft:Integrable (fun ξ:ℝ=>inner ℂ (𝓕 (u-b) ξ) (𝓕 c ξ)):=by
    apply (Complex.conjCLE.toContinuousLinearMap.integrable_comp
      (fourier_cross_integrable c (u-b) hc (hu.sub hb) hFu)).congr
    exact Eventually.of_forall (fun ξ=>inner_conj_symm (𝕜:=ℂ) (𝓕 (u-b) ξ) (𝓕 c ξ))
  have hright:=fourier_cross_integrable u (v-c) hu (hv.sub hc) hFv
  have he:(fun ξ:ℝ=>inner ℂ (𝓕 u ξ) (𝓕 v ξ))=
      (fun ξ:ℝ=>inner ℂ (𝓕 b ξ) (𝓕 c ξ)+
        inner ℂ (𝓕 (u-b) ξ) (𝓕 c ξ)+inner ℂ (𝓕 u ξ) (𝓕 (v-c) ξ)):=by
    funext ξ
    rw [fourier_sub_integrable u b hu hb,fourier_sub_integrable v c hv hc]
    simp only [inner_sub_left,inner_sub_right]
    abel
  have hli:(∫ξ:ℝ,inner ℂ (𝓕 (u-b) ξ) (𝓕 c ξ))=∫t:ℝ,inner ℂ ((u-b) t) (c t):=by
    have h:=congrArg (starRingEnd ℂ) (one_sided_parseval c (u-b) hc (hu.sub hb) huc hFu)
    simpa only [←integral_conj,inner_conj_symm] using h
  have hri:=one_sided_parseval u (v-c) hu (hv.sub hc) hvc hFv
  have ht:(fun t:ℝ=>inner ℂ ((u-b) t) (c t))=
      (fun t:ℝ=> -inner ℂ (u t) ((v-c) t)):=by
    funext t
    simp only [Pi.sub_apply,inner_sub_left,inner_sub_right,hp]
    ring
  rw [he]
  refine ⟨(hbase.add hleft).add hright,?_⟩
  have hs:=integral_add (hbase.add hleft) hright
  simp only [Pi.add_apply] at hs
  rw [hs,integral_add hbase hleft,hli,hri,ht,integral_neg]
  ring
end Parseval

private theorem source_wave_pair(F:Index)(f g:QuantumTest)(advanced:Bool)(μ t:ℝ):
    inner ℂ (sourceWave F false f advanced μ t) (sourceWave F true g advanced μ t)=
      inner ℂ (causalWave μ (fun _=>embed f) t) (causalWave μ (fun _=>embed g) t):=by
  by_cases ht:t∈Ioi (0:ℝ)
  · have h:=literal_dynamic_two_leg_pair F f g (direction advanced*t)
    simp only [sourcePair] at h
    simp only [sourceWave,causalWave,indicator_of_mem ht,inner_smul_left,inner_smul_right,h]
  · simp only [sourceWave,causalWave,indicator_of_notMem ht,inner_zero_left]

private theorem constant_fourier_pair(μ:ℝ)(hμ:0<μ)(f g:QuantumTest)(ξ:ℝ):
    inner ℂ (𝓕 (causalWave μ (fun _=>embed f)) ξ) (𝓕 (causalWave μ (fun _=>embed g)) ξ)=
      (kernel μ 0 (-2*Real.pi*ξ):ℂ)*sourcePair f g:=by
  rw [constant_wave_fourier μ hμ,constant_wave_fourier μ hμ,inner_smul_left,inner_smul_right,←mul_assoc]
  have hn:‖Complex.I/line μ (-2*Real.pi*ξ)‖^2=kernel μ 0 (-2*Real.pi*ξ):=by
    have h:=inverse_norm_square μ 0 (-2*Real.pi*ξ)
    simpa only [norm_div,Complex.norm_I,one_div,Complex.ofReal_zero,zero_sub,norm_inv,norm_neg,
      line,mul_comm (μ:ℂ) Complex.I] using h
  rw [←Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq,hn]
  rfl

private theorem constant_frequency_integrable(μ:ℝ)(hμ:0<μ)(f g:QuantumTest):
    Integrable (fun ξ:ℝ=>inner ℂ (𝓕 (causalWave μ (fun _=>embed f)) ξ)
      (𝓕 (causalWave μ (fun _=>embed g)) ξ)):=by
  simp_rw [constant_fourier_pair μ hμ f g]
  exact (((kernel_integrable μ 0 hμ).comp_mul_left' (by positivity : -2*Real.pi≠0)).ofReal).mul_const _

private theorem constant_frequency_integral(μ:ℝ)(hμ:0<μ)(f g:QuantumTest):
    (∫ξ:ℝ,inner ℂ (𝓕 (causalWave μ (fun _=>embed f)) ξ)
      (𝓕 (causalWave μ (fun _=>embed g)) ξ))=(1/(2*μ):ℂ)*sourcePair f g:=by
  simp_rw [constant_fourier_pair μ hμ f g]
  rw [integral_mul_const,integral_complex_ofReal,Measure.integral_comp_mul_left,kernel_integral μ 0 hμ]
  congr 1
  rw [smul_eq_mul,abs_inv,abs_mul,abs_neg,abs_of_nonneg (by norm_num : (0:ℝ)≤2),abs_of_pos Real.pi_pos]
  push_cast
  field_simp [hμ.ne',Real.pi_ne_zero]

/-- The complete original paired frequency mass has no source-size or Yukawa growth constant. -/
theorem actual_full_y_paired_fourier(F:Index)(f g:QuantumTest)(advanced:Bool)(μ:ℝ)(hμ:0<μ):
    Integrable (fun ξ:ℝ=>inner ℂ (𝓕 (sourceWave F false f advanced μ) ξ)
      (𝓕 (sourceWave F true g advanced μ) ξ)) ∧
    (∫ξ:ℝ,inner ℂ (𝓕 (sourceWave F false f advanced μ) ξ)
      (𝓕 (sourceWave F true g advanced μ) ξ))=(1/(2*μ):ℂ)*sourcePair f g:=by
  have h:=paired_parseval_cancellation (sourceWave F false f advanced μ) (sourceWave F true g advanced μ)
    (causalWave μ (fun _=>embed f)) (causalWave μ (fun _=>embed g))
    (actual_source_wave_integrable F false f advanced μ hμ) (actual_source_wave_integrable F true g advanced μ hμ)
    (constant_wave_integrable μ hμ (embed f)) (constant_wave_integrable μ hμ (embed g))
    (actual_wave_correction_continuous F false f advanced μ) (actual_wave_correction_continuous F true g advanced μ)
    (actual_wave_correction_fourier_integrable F false f advanced μ hμ)
    (actual_wave_correction_fourier_integrable F true g advanced μ hμ)
    (constant_frequency_integrable μ hμ f g) (source_wave_pair F f g advanced μ)
  exact ⟨h.1,h.2.trans (constant_frequency_integral μ hμ f g)⟩

private theorem line_nonreal(advanced:Bool)(μ w:ℝ)(hμ:0<μ):
    (line (direction advanced*μ) w).im≠0:=by
  rw [line_im]
  cases advanced <;> simpa only [direction,ite_true,Bool.false_eq_true,ite_false,one_mul,
    neg_one_mul,neg_ne_zero] using hμ.ne'

def pairedResponse(F:Index)(f g:QuantumTest)(advanced:Bool)(μ:ℝ)(hμ:0<μ)(w:ℝ):ℂ:=
  sourcePair (literalCoreResolvent F (line (direction advanced*μ) w) (line_nonreal advanced μ w hμ) f)
    (literalSharpResolvent F (line (direction advanced*μ) w) (line_nonreal advanced μ w hμ) g)

private def frequencyScale(advanced:Bool):ℝ:= -direction advanced*(2*Real.pi)
private theorem scale_abs(advanced:Bool):|frequencyScale advanced|=2*Real.pi:=by
  cases advanced <;> simp [frequencyScale,direction,abs_of_pos Real.pi_pos]
private theorem scale_ne(advanced:Bool):frequencyScale advanced≠0:=by
  have h:0 < |frequencyScale advanced|:=by rw [scale_abs];positivity
  exact abs_pos.mp h
private theorem line_scale(advanced:Bool)(μ ξ:ℝ):
    line (direction advanced*μ) (frequencyScale advanced*ξ)=sourceLine advanced μ ξ:=by
  cases advanced <;> simp only [line,frequencyScale,sourceLine,direction,ite_true,Bool.false_eq_true,
    ite_false,Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_one,Complex.ofReal_ofNat]
  all_goals ring

private theorem paired_response_fourier(F:Index)(f g:QuantumTest)(advanced:Bool)(μ:ℝ)(hμ:0<μ)(ξ:ℝ):
    pairedResponse F f g advanced μ hμ (frequencyScale advanced*ξ)=
      inner ℂ (𝓕 (sourceWave F false f advanced μ) ξ) (𝓕 (sourceWave F true g advanced μ) ξ):=by
  have hp:=actual_source_wave_fourier F false f advanced μ hμ ξ
  have hq:=actual_source_wave_fourier F true g advanced μ hμ ξ
  simp only [Bool.false_eq_true,ite_false,ite_true] at hp hq
  unfold pairedResponse
  simp only [line_scale]
  change inner ℂ (embed _) (embed _)=_
  rw [←hp,←hq,inner_smul_left,inner_smul_right]
  cases advanced <;> simp [direction,←mul_assoc,Complex.I_mul_I]

private theorem recover_scaled_integral(c:ℝ)(hc:c≠0)(f:ℝ→ℂ):
    (∫w:ℝ,f w)=|c| • ∫ξ:ℝ,f (c*ξ):=by
  rw [Measure.integral_comp_mul_left,smul_smul,←abs_mul,mul_inv_cancel₀ hc,abs_one,one_smul]

/-- Both causal lines have the same full-Y, independent-dual complex mass, independent of the finite source. -/
theorem actual_full_y_paired_frequency(F:Index)(f g:QuantumTest)(advanced:Bool)(μ:ℝ)(hμ:0<μ):
    Integrable (pairedResponse F f g advanced μ hμ) ∧
      (∫w:ℝ,pairedResponse F f g advanced μ hμ w)=(Real.pi/μ:ℂ)*sourcePair f g:=by
  have h:=actual_full_y_paired_fourier F f g advanced μ hμ
  have he:(fun ξ:ℝ=>pairedResponse F f g advanced μ hμ (frequencyScale advanced*ξ))=
      (fun ξ:ℝ=>inner ℂ (𝓕 (sourceWave F false f advanced μ) ξ)
        (𝓕 (sourceWave F true g advanced μ) ξ)):=funext (paired_response_fourier F f g advanced μ hμ)
  refine ⟨(integrable_comp_mul_left_iff _ (scale_ne advanced)).mp (he ▸ h.1),?_⟩
  rw [recover_scaled_integral (frequencyScale advanced) (scale_ne advanced),he,h.2,scale_abs,Complex.real_smul]
  push_cast
  field_simp [hμ.ne']

def ownDefectCurrent(F K:Index)(f g:QuantumTest)(advanced:Bool)(μ:ℝ)(hμ:0<μ)(w:ℝ):ℂ:=
  let z:=line (direction advanced*μ) w
  let hz:=line_nonreal advanced μ w hμ
  sourcePair (literalCoreResolvent K z hz (defectAction F (literalCoreResolvent F z hz f)))
    (literalSharpResolvent K z hz g)+
  sourcePair (literalCoreResolvent F z hz f)
    (literalSharpResolvent K z hz (defectAction F (literalSharpResolvent F z hz g)))

private theorem paired_difference {E:Type*}[NormedAddCommGroup E][InnerProductSpace ℂ E]
    (a b a' b' x y:E)(ha:a'-a= -x)(hb:b'-b= -y):
    inner ℂ x b'+inner ℂ a y=inner ℂ a b-inner ℂ a' b':=by
  have hx:x=a-a':=by rw [←neg_inj,←ha,neg_sub]
  have hy:y=b-b':=by rw [←neg_inj,←hb,neg_sub]
  rw [hx,hy,inner_sub_left,inner_sub_right]
  abel

/-- The complete two-leg own-defect current is a signed cofinal payment, with no absolute-value tail premise. -/
theorem actual_cofinal_own_defect_frequency(F:Index)(f g:QuantumTest):
    ∃K₀:Index,F⊆K₀ ∧ ∀K:Index,K₀⊆K → ∀advanced:Bool,∀μ:ℝ,∀hμ:0<μ,
      Integrable (ownDefectCurrent F K f g advanced μ hμ) ∧
        (∫w:ℝ,ownDefectCurrent F K f g advanced μ hμ w)=0:=by
  obtain ⟨K₀,hF,_hG,hK₀⟩:=FullYDynamicSourceRefinement.literal_cofinal_resolvent_update F F f g
  refine ⟨K₀,hF,?_⟩
  intro K hK advanced μ hμ
  have he:ownDefectCurrent F K f g advanced μ hμ=
      pairedResponse F f g advanced μ hμ-pairedResponse K f g advanced μ hμ:=by
    funext w
    let z:=line (direction advanced*μ) w
    let hz:=line_nonreal advanced μ w hμ
    have h:=hK₀ K hK z hz
    have ha:=congrArg embed h.2.2.1
    have hb:=congrArg embed h.2.2.2
    simp only [map_sub,map_neg] at ha hb
    exact paired_difference _ _ _ _ _ _ ha hb
  have hFmass:=actual_full_y_paired_frequency F f g advanced μ hμ
  have hKmass:=actual_full_y_paired_frequency K f g advanced μ hμ
  rw [he]
  refine ⟨hFmass.1.sub hKmass.1,?_⟩
  simp only [Pi.sub_apply]
  rw [integral_sub hFmass.1 hKmass.1,hFmass.2,hKmass.2,sub_self]

/-- The frequency measure is complex and keeps both original source legs. -/
def pairedSourceMeasure(F:Index)(f g:QuantumTest)(advanced:Bool)(μ:ℝ)(hμ:0<μ):VectorMeasure ℝ ℂ:=
  volume.withDensityᵥ (pairedResponse F f g advanced μ hμ)

/-- Its total variation is finite and its complete mass is generated by the original paired dynamics. -/
theorem actual_paired_source_measure(F:Index)(f g:QuantumTest)(advanced:Bool)(μ:ℝ)(hμ:0<μ):
    (∀s:Set ℝ,MeasurableSet s → pairedSourceMeasure F f g advanced μ hμ s=
      ∫w:ℝ in s,pairedResponse F f g advanced μ hμ w) ∧
    (pairedSourceMeasure F f g advanced μ hμ).variation Set.univ<⊤ ∧
    pairedSourceMeasure F f g advanced μ hμ Set.univ=(Real.pi/μ:ℂ)*sourcePair f g:=by
  have h:=actual_full_y_paired_frequency F f g advanced μ hμ
  refine ⟨fun s hs=>withDensityᵥ_apply h.1 hs,?_,?_⟩
  · rw [pairedSourceMeasure,Measure.variation_withDensityᵥ h.1,withDensity_apply _ MeasurableSet.univ]
    simpa only [Measure.restrict_univ] using hasFiniteIntegral_iff_enorm.mp h.1.hasFiniteIntegral
  · rw [pairedSourceMeasure,withDensityᵥ_apply h.1 MeasurableSet.univ,Measure.restrict_univ]
    exact h.2

end LowEnergy.FullYPairedParseval
