import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceNamedMatterFourGradeTimeMeasure
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceFullYPairedRetardedParseval
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.FourGradeOutputParseval
open MeasureTheory Filter Set FullYPairedParseval
open scoped FourierTransform InnerProductSpace

private theorem one_sided_positive_parseval {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (f g : ℝ → E) (hf : Integrable f)
    (hg : Integrable g) (hgc : Continuous g) (hFg : Integrable (𝓕 g)) :
    (∫ξ : ℝ,inner ℂ (𝓕 f ξ) (𝓕 g ξ)) = ∫t : ℝ,inner ℂ (f t) (g t) := by
  have h := VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip (innerSL ℂ)
    (L:=innerₗ ℝ) Real.continuous_fourierChar continuous_inner hf hFg
  have he : (innerₗ ℝ).flip=innerₗ ℝ := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change inner ℝ y x=inner ℝ x y
    exact real_inner_comm x y
  rw [he] at h
  change (∫ξ : ℝ,inner ℂ (𝓕 f ξ) (𝓕 g ξ)) = ∫t : ℝ,inner ℂ (f t) (𝓕⁻ (𝓕 g) t) at h
  rw [hgc.fourierInv_fourier_eq hg hFg] at h
  exact h

/-- The complete positive output consumes its own two-jet correction; no conservation of nonselfadjoint fullY norm is assumed. -/
private theorem positive_output_parseval {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (u b : ℝ → E)
    (hu : Integrable u) (hb : Integrable b) (hc : Continuous (u-b))
    (hFc : Integrable (𝓕 (u-b)))
    (hbu : Integrable (fun ξ : ℝ => inner ℂ (𝓕 b ξ) (𝓕 b ξ)))
    (hbt : Integrable (fun t : ℝ => inner ℂ (b t) (b t)))
    (hub : Integrable (fun t : ℝ => inner ℂ ((u-b) t) (b t)))
    (huc : Integrable (fun t : ℝ => inner ℂ (u t) ((u-b) t)))
    (hebase : (∫ξ : ℝ,inner ℂ (𝓕 b ξ) (𝓕 b ξ)) = ∫t : ℝ,inner ℂ (b t) (b t)) :
    (∫ξ : ℝ,inner ℂ (𝓕 u ξ) (𝓕 u ξ)) = ∫t : ℝ,inner ℂ (u t) (u t) := by
  let c := u-b
  have hcf : Integrable (fun ξ : ℝ => inner ℂ (𝓕 u ξ) (𝓕 c ξ)) := by
    apply (hFc.norm.const_mul (∫t : ℝ,‖u t‖)).mono'
      ((fourier_continuous_of_integrable u hu).aestronglyMeasurable.inner
        (fourier_continuous_of_integrable c (hu.sub hb)).aestronglyMeasurable)
    exact Eventually.of_forall (fun ξ => (norm_inner_le_norm (𝓕 u ξ) (𝓕 c ξ)).trans
      (mul_le_mul_of_nonneg_right (fourier_bound u ξ) (norm_nonneg _)))
  have hcbf : Integrable (fun ξ : ℝ => inner ℂ (𝓕 c ξ) (𝓕 b ξ)) := by
    have hbf : Integrable (fun ξ : ℝ => inner ℂ (𝓕 b ξ) (𝓕 c ξ)) := by
      apply (hFc.norm.const_mul (∫t : ℝ,‖b t‖)).mono'
        ((fourier_continuous_of_integrable b hb).aestronglyMeasurable.inner
          (fourier_continuous_of_integrable c (hu.sub hb)).aestronglyMeasurable)
      exact Eventually.of_forall (fun ξ => (norm_inner_le_norm (𝓕 b ξ) (𝓕 c ξ)).trans
        (mul_le_mul_of_nonneg_right (fourier_bound b ξ) (norm_nonneg _)))
    exact (Complex.conjCLE.toContinuousLinearMap.integrable_comp hbf).congr
      (Eventually.of_forall (fun ξ => inner_conj_symm (𝕜:=ℂ) (𝓕 c ξ) (𝓕 b ξ)))
  have hcb : (∫ξ : ℝ,inner ℂ (𝓕 c ξ) (𝓕 b ξ)) = ∫t : ℝ,inner ℂ (c t) (b t) := by
    have h := congrArg (starRingEnd ℂ) (one_sided_positive_parseval b c hb (hu.sub hb) hc hFc)
    simpa only [←integral_conj,inner_conj_symm] using h
  have hcu := one_sided_positive_parseval u c hu (hu.sub hb) hc hFc
  have expand (v w : E) : inner ℂ v v=inner ℂ w w+inner ℂ (v-w) w+inner ℂ v (v-w) := by
    simp only [inner_sub_left,inner_sub_right]; abel
  have hF : (fun ξ : ℝ => inner ℂ (𝓕 u ξ) (𝓕 u ξ)) =
      (fun ξ => inner ℂ (𝓕 b ξ) (𝓕 b ξ)+inner ℂ (𝓕 c ξ) (𝓕 b ξ)+inner ℂ (𝓕 u ξ) (𝓕 c ξ)) := by
    funext ξ
    rw [show 𝓕 c ξ=𝓕 u ξ-𝓕 b ξ from fourier_sub_integrable u b hu hb ξ]
    exact expand _ _
  have hsF := integral_add (hbu.add hcbf) hcf
  have hsF2 := integral_add hbu hcbf
  simp only [Pi.add_apply] at hsF hsF2
  rw [hF,hsF,hsF2,hebase,hcb,hcu]
  have hT : (fun t : ℝ => inner ℂ (u t) (u t)) =
      (fun t => inner ℂ (b t) (b t)+inner ℂ (c t) (b t)+inner ℂ (u t) (c t)) := by
    funext t
    exact expand _ _
  have hsT := integral_add (hbt.add hub) huc
  have hsT2 := integral_add hbt hub
  simp only [Pi.add_apply] at hsT hsT2
  rw [hT,hsT,hsT2]


private theorem baseline_square_mass {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (x : E) (μ : ℝ) (hμ : 0 < μ) :
    (∫ξ : ℝ,‖𝓕 (causalWave μ (fun _ => x)) ξ‖^2) = ‖x‖^2/(2*μ) ∧
      (∫t : ℝ,‖causalWave μ (fun _ => x) t‖^2)=‖x‖^2/(2*μ) := by
  have hf (ξ : ℝ) : ‖𝓕 (causalWave μ (fun _ => x)) ξ‖^2 =
      SourceResolventLorentzian.kernel μ 0 (-2*Real.pi*ξ)*‖x‖^2 := by
    rw [constant_wave_fourier μ hμ,norm_smul,mul_pow]
    congr 1
    have h := SourceResolventLorentzian.inverse_norm_square μ 0 (-2*Real.pi*ξ)
    simpa only [norm_div,Complex.norm_I,one_div,Complex.ofReal_zero,zero_sub,norm_inv,norm_neg,
      SourceResolventBandLimit.line,mul_comm (μ:ℂ) Complex.I] using h
  have ht (t : ℝ) : ‖causalWave μ (fun _ => x) t‖^2 =
      (Ioi 0).indicator (fun t : ℝ => Real.exp ((-2*μ)*t)*‖x‖^2) t := by
    by_cases ht : t∈Ioi (0:ℝ)
    · simp only [causalWave,indicator_of_mem ht,norm_smul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _),mul_pow]
      rw [←Real.exp_nat_mul]
      congr 2
      ring
    · simp only [causalWave,indicator_of_notMem ht,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0)]
  constructor
  · simp_rw [hf]
    rw [integral_mul_const,show (fun ξ : ℝ => SourceResolventLorentzian.kernel μ 0 (-2*Real.pi*ξ)) =
      (fun ξ : ℝ => SourceResolventLorentzian.kernel μ 0 ((-2*Real.pi)*ξ)) from rfl,
      MeasureTheory.Measure.integral_comp_mul_left,SourceResolventLorentzian.kernel_integral μ 0 hμ]
    simp only [smul_eq_mul,abs_inv,abs_mul,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<2),abs_of_pos Real.pi_pos]
    field_simp [hμ.ne',Real.pi_ne_zero]
  · simp_rw [ht]
    rw [integral_indicator measurableSet_Ioi,integral_mul_const,
      integral_exp_mul_Ioi (by nlinarith : -2*μ<0) 0]
    simp only [mul_zero,Real.exp_zero]
    field_simp [hμ.ne']


private theorem square_pair_integrable {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (u v : ℝ → E) (hu : AEStronglyMeasurable u)
    (hv : AEStronglyMeasurable v) (hu2 : Integrable (fun t => ‖u t‖^2))
    (hv2 : Integrable (fun t => ‖v t‖^2)) :
    Integrable (fun t => inner ℂ (u t) (v t)) := by
  apply ((hu2.add hv2).div_const 2).mono' (hu.inner hv)
  apply Eventually.of_forall
  intro t
  have h := norm_inner_le_norm (𝕜:=ℂ) (u t) (v t)
  simp only [Pi.add_apply]
  nlinarith only [h,sq_nonneg (‖u t‖-‖v t‖)]

private theorem fourier_reader {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (P : E →L[ℂ] E) (u : ℝ → E) (hu : Integrable u) (ξ : ℝ) :
    𝓕 (fun t => P (u t)) ξ = P (𝓕 u ξ) := by
  rw [Real.fourier_eq,Real.fourier_eq]
  rw [←ContinuousLinearMap.integral_comp_comm P (Real.fourierIntegral_convergent_iff ξ |>.mpr hu)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun t => (map_smul P _ _).symm)

private theorem baseline_time_square_integrable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (x : E) (μ : ℝ) (hμ : 0 < μ) :
    Integrable (fun t => ‖causalWave μ (fun _ => x) t‖^2) := by
  have hu := constant_wave_integrable μ hμ x
  apply (hu.norm.const_mul ‖x‖).mono' (hu.aestronglyMeasurable.norm.pow 2)
  apply Eventually.of_forall
  intro t
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),pow_two]
  apply mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  by_cases ht : t∈Ioi (0:ℝ)
  · simp only [causalWave,indicator_of_mem ht,norm_smul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr (by
      change 0<t at ht
      simpa only [neg_mul] using neg_nonpos.mpr (mul_nonneg hμ.le ht.le)))
  · simp only [causalWave,indicator_of_notMem ht,norm_zero]
    exact norm_nonneg _

private theorem baseline_frequency_square_integrable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (x : E) (μ : ℝ) (hμ : 0 < μ) :
    Integrable (fun ξ => ‖𝓕 (causalWave μ (fun _ => x)) ξ‖^2) := by
  have he (ξ : ℝ) : ‖𝓕 (causalWave μ (fun _ => x)) ξ‖^2 =
      SourceResolventLorentzian.kernel μ 0 (-2*Real.pi*ξ)*‖x‖^2 := by
    rw [constant_wave_fourier μ hμ,norm_smul,mul_pow]
    congr 1
    have h := SourceResolventLorentzian.inverse_norm_square μ 0 (-2*Real.pi*ξ)
    simpa only [norm_div,Complex.norm_I,one_div,Complex.ofReal_zero,zero_sub,norm_inv,norm_neg,
      SourceResolventBandLimit.line,mul_comm (μ:ℂ) Complex.I] using h
  simp_rw [he]
  exact ((SourceResolventLorentzian.kernel_integrable μ 0 hμ).comp_mul_left'
    (by positivity : -2*Real.pi≠0)).mul_const _

open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussUnitaryHistory GaussDiagonalHistory
open FullYDynamicSource GaussDensityCore ThreeParticleRetardedTime
local instance : SecondCountableTopologyEither ℝ H := secondCountableTopologyEither_of_left ℝ H

private theorem reader_square_integrable (P : H →L[ℂ] H) (u : ℝ → H)
    (hu : AEStronglyMeasurable u) (hu2 : Integrable (fun t => ‖u t‖^2)) :
    Integrable (fun t => ‖P (u t)‖^2) := by
  apply (hu2.const_mul (‖P‖^2)).mono'
    ((P.continuous.comp_aestronglyMeasurable hu).norm.pow 2)
  apply Eventually.of_forall
  intro t
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact (pow_le_pow_left₀ (norm_nonneg _) (P.le_opNorm _) 2).trans_eq (mul_pow _ _ _)

/-- The original two-jet correction pays the positive Parseval mass of every bounded output of the complete primal source. -/
theorem actual_source_output_parseval (F : Index) (g : QuantumTest) (advanced : Bool)
    (μ : ℝ) (hμ : 0 < μ) (P : H →L[ℂ] H) :
    (∫ξ : ℝ,‖𝓕 (fun t => P (sourceWave F false g advanced μ t)) ξ‖^2) =
      ∫t : ℝ,‖P (sourceWave F false g advanced μ t)‖^2 := by
  let u := fun t => P (sourceWave F false g advanced μ t)
  let b := causalWave μ (fun _ => P (embed g))
  have hu : Integrable u := P.integrable_comp (actual_source_wave_integrable F false g advanced μ hμ)
  have hb : Integrable b := constant_wave_integrable μ hμ _
  have he : u-b = fun t => P (waveCorrection F false g advanced μ t) := by
    funext t
    simp only [u,b,waveCorrection,Pi.sub_apply,map_sub]
    congr 1
    by_cases ht : t∈Ioi (0:ℝ)
    · simp only [causalWave,indicator_of_mem ht,map_smul]
    · simp only [causalWave,indicator_of_notMem ht,map_zero]
  have hc : Continuous (u-b) := by
    rw [he]
    exact P.continuous.comp (actual_wave_correction_continuous F false g advanced μ)
  have hFc : Integrable (𝓕 (u-b)) := by
    rw [he]
    have h := P.integrable_comp (actual_wave_correction_fourier_integrable F false g advanced μ hμ)
    exact h.congr (Eventually.of_forall (fun ξ =>
      (fourier_reader P _ (actual_wave_correction_integrable F false g advanced μ hμ) ξ).symm))
  have hu2 : Integrable (fun t => ‖u t‖^2) := reader_square_integrable P _
    (actual_source_wave_integrable F false g advanced μ hμ).aestronglyMeasurable
    (actual_source_time_square_integrable F g advanced μ hμ)
  have hb2 : Integrable (fun t => ‖b t‖^2) := baseline_time_square_integrable _ μ hμ
  have hbF2 : Integrable (fun ξ => ‖𝓕 b ξ‖^2) := baseline_frequency_square_integrable _ μ hμ
  have hc2 : Integrable (fun t => ‖(u-b) t‖^2) := by
    have h := ((memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mpr hu2).sub
      ((memLp_two_iff_integrable_sq_norm hb.aestronglyMeasurable).mpr hb2)
    exact (memLp_two_iff_integrable_sq_norm (hu.sub hb).aestronglyMeasurable).mp h
  have hbu : Integrable (fun ξ => inner ℂ (𝓕 b ξ) (𝓕 b ξ)) := by
    simp only [inner_self_eq_norm_sq_to_K,←RCLike.ofReal_pow]
    exact hbF2.ofReal
  have hbt : Integrable (fun t => inner ℂ (b t) (b t)) := by
    simp only [inner_self_eq_norm_sq_to_K,←RCLike.ofReal_pow]
    exact hb2.ofReal
  have hebase : (∫ξ : ℝ,inner ℂ (𝓕 b ξ) (𝓕 b ξ)) = ∫t : ℝ,inner ℂ (b t) (b t) := by
    simp only [inner_self_eq_norm_sq_to_K,←RCLike.ofReal_pow]
    rw [integral_ofReal,integral_ofReal]
    exact congrArg (fun x : ℝ => (x:ℂ))
      ((baseline_square_mass (P (embed g)) μ hμ).1.trans (baseline_square_mass (P (embed g)) μ hμ).2.symm)
  have h := positive_output_parseval u b hu hb hc hFc hbu hbt
    (square_pair_integrable _ _ (hu.sub hb).aestronglyMeasurable hb.aestronglyMeasurable hc2 hb2)
    (square_pair_integrable _ _ hu.aestronglyMeasurable (hu.sub hb).aestronglyMeasurable hu2 hc2) hebase
  simp only [inner_self_eq_norm_sq_to_K,←RCLike.ofReal_pow] at h
  rw [integral_ofReal,integral_ofReal] at h
  exact Complex.ofReal_injective h

end LowEnergy.FourGradeOutputParseval
