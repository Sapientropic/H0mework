import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualFourBlockCausalMass
import Lean.Elab.Term
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
noncomputable section
namespace LowEnergy.ActualFourBlockSharpCausalMass
open MeasureTheory Filter Set FullYPairedParseval CompositeFullYBorn
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussUnitaryHistory GaussDiagonalHistory GaussFockPair
open FullYDynamicSource FullYDynamicSourceNext FullYDynamicResponse GaussDensityCore SourceResolventBandLimit
open ActualFourBlockSource ActualFourBlockRetarded
open scoped FourierTransform InnerProductSpace BigOperators Topology ENNReal
attribute [local irreducible] embed literalCoreResolvent literalSharpResolvent sourceOrbit sourceSpace
local instance : SecondCountableTopologyEither ℝ H := secondCountableTopologyEither_of_left ℝ H

section PaidParseval
open Lean Meta Elab Term
/-- Keep the exact paid Parseval constants rather than reconstructing their analytic proof. -/
elab "paid_output_parseval%" helper:ident : term => do
  let ns := Name.str (Name.str (Name.num
    (`_private.H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceFullYPositiveOutputParseval) 0) "LowEnergy") "FourGradeOutputParseval"
  let name := Name.str ns helper.getId.toString
  unless (← getEnv).contains name do throwError "Missing paid Parseval helper: {name}"
  mkConstWithFreshMVarLevels name
end PaidParseval

private theorem exp_polynomial_square_integrable (μ C : ℝ) (hμ : 0 < μ) :
    IntegrableOn (fun t : ℝ => Real.exp (-(2*μ)*t)*
      (∑j∈Finset.range 57,(|t| * C)^j)^2) (Ioi 0) := by
  have hterm (j k : ℕ) : IntegrableOn
      (fun t : ℝ => C^(j+k)*(t^(j+k)*Real.exp (-(2*μ)*t))) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := ((j+k : ℕ) : ℝ)) (p := 1) (b := 2*μ)
      (by have h : (0 : ℝ) ≤ (j+k : ℕ) := Nat.cast_nonneg _; linarith) one_pos (by positivity)
    simpa only [Real.rpow_natCast,Real.rpow_one] using! h.const_mul (C^(j+k))
  have hi := integrable_finsetSum (Finset.range 57) (fun j _ =>
    integrable_finsetSum (Finset.range 57) (fun k _ => hterm j k))
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change 0 < t at ht
  simp only [abs_of_pos ht,pow_two,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  simp only [pow_add,mul_pow]
  ring

private theorem polynomial_wave_square_integrable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (μ C D : ℝ) (hμ : 0 < μ) (u : ℝ → E) (hu : Continuous u)
    (hb : ∀t : ℝ,‖u t‖ ≤ (∑j∈Finset.range 57,(|t| * C)^j)*D) :
    Integrable (fun t : ℝ => ‖causalWave μ u t‖^2) := by
  have he : (fun t : ℝ => ‖causalWave μ u t‖^2) =
      (Ioi 0).indicator (fun t : ℝ => Real.exp (-(2*μ)*t)*‖u t‖^2) := by
    funext t
    by_cases ht : t∈Ioi (0:ℝ)
    · simp only [causalWave,indicator_of_mem ht,norm_smul,Complex.norm_real,
        Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),mul_pow]
      rw [←Real.exp_nat_mul]
      congr 2
      ring
    · simp [causalWave,indicator_of_notMem ht]
  rw [he]
  apply (integrable_indicator_iff measurableSet_Ioi).mpr
  apply ((exp_polynomial_square_integrable μ C hμ).mul_const (D^2)).mono'
    (((by fun_prop : Continuous (fun t : ℝ => Real.exp (-(2*μ)*t))).mul
      (hu.norm.pow 2)).aestronglyMeasurable.restrict)
  filter_upwards [] with t
  simp only [Pi.mul_apply,Pi.pow_apply]
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
  have h := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (hb t) 2) (Real.exp_pos (-(2*μ)*t)).le
  exact h.trans_eq (by ring)

/-- The original finite source generator's degree-56 polynomial bound pays
absolute L2 time mass on both independent branches, without a conservation premise. -/
theorem actual_source_wave_square_integrable (F : Index) (sharp : Bool) (q : QuantumTest)
    (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) :
    Integrable (fun t : ℝ => ‖sourceWave F sharp q advanced μ t‖^2) := by
  obtain ⟨C,_hC,hC⟩ := actual_source_time_polynomial_bound F sharp q
  have hb (t : ℝ) : ‖embed (literalCoreTime F sharp q t)‖ ≤
      (∑j∈Finset.range 57,(|t| * C)^j)*‖embed q‖ := by
    let x := sourceEquiv F sharp q ⟨q,sourceOrbit_input F sharp q⟩
    have he : embed (literalCoreTime F sharp q t) =
        (SourceFiniteUnitary.time (sourceGenerator F sharp q) t x : H) :=
      congrArg Subtype.val ((sourceEquiv F sharp q).apply_symm_apply _)
    rw [he]
    exact ((SourceFiniteUnitary.time (sourceGenerator F sharp q) t).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (hC t) (norm_nonneg x))
  let u : ℝ → H := fun t => embed (literalCoreTime F sharp q (FullYPairedParseval.direction advanced*t))
  have hu : Continuous u :=
    (continuous_iff_continuousAt.mpr (fun t =>
      (literal_core_time_derivative F sharp q t).continuousAt)).comp
      (continuous_const.mul continuous_id)
  have hbound (t : ℝ) : ‖u t‖ ≤
      (∑j∈Finset.range 57,(|t| * C)^j)*‖embed q‖ := by
    have h := hb (FullYPairedParseval.direction advanced*t)
    cases advanced <;> simpa only [u,FullYPairedParseval.direction,ite_true,
      Bool.false_eq_true,ite_false,one_mul,neg_one_mul,abs_neg] using h
  change Integrable (fun t : ℝ => ‖causalWave μ u t‖^2)
  exact polynomial_wave_square_integrable μ C ‖embed q‖ hμ u hu hbound


theorem actual_source_output_parseval (F : Index) (sharp : Bool) (g : QuantumTest) (advanced : Bool)
    (μ : ℝ) (hμ : 0 < μ) (P : H →L[ℂ] H) :
    (∫ξ : ℝ,‖𝓕 (fun t => P (sourceWave F sharp g advanced μ t)) ξ‖^2) =
      ∫t : ℝ,‖P (sourceWave F sharp g advanced μ t)‖^2 := by
  let u := fun t => P (sourceWave F sharp g advanced μ t)
  let b := causalWave μ (fun _ => P (embed g))
  have hu : Integrable u := P.integrable_comp (actual_source_wave_integrable F sharp g advanced μ hμ)
  have hb : Integrable b := constant_wave_integrable μ hμ _
  have he : u-b = fun t => P (waveCorrection F sharp g advanced μ t) := by
    funext t
    simp only [u,b,waveCorrection,Pi.sub_apply,map_sub]
    congr 1
    by_cases ht : t∈Ioi (0:ℝ)
    · simp only [causalWave,indicator_of_mem ht,map_smul]
    · simp only [causalWave,indicator_of_notMem ht,map_zero]
  have hc : Continuous (u-b) := by
    rw [he]
    exact P.continuous.comp (actual_wave_correction_continuous F sharp g advanced μ)
  have hFc : Integrable (𝓕 (u-b)) := by
    rw [he]
    have h := P.integrable_comp (actual_wave_correction_fourier_integrable F sharp g advanced μ hμ)
    exact h.congr (Eventually.of_forall (fun ξ =>
      ((paid_output_parseval% fourier_reader) P _ (actual_wave_correction_integrable F sharp g advanced μ hμ) ξ).symm))
  have hu2 : Integrable (fun t => ‖u t‖^2) := (paid_output_parseval% reader_square_integrable) P _
    (actual_source_wave_integrable F sharp g advanced μ hμ).aestronglyMeasurable
    (actual_source_wave_square_integrable F sharp g advanced μ hμ)
  have hb2 : Integrable (fun t => ‖b t‖^2) := (paid_output_parseval% baseline_time_square_integrable) _ μ hμ
  have hbF2 : Integrable (fun ξ => ‖𝓕 b ξ‖^2) := (paid_output_parseval% baseline_frequency_square_integrable) _ μ hμ
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
      (((paid_output_parseval% baseline_square_mass) (P (embed g)) μ hμ).1.trans ((paid_output_parseval% baseline_square_mass) (P (embed g)) μ hμ).2.symm)
  have h := (paid_output_parseval% positive_output_parseval) u b hu hb hc hFc hbu hbt
    ((paid_output_parseval% square_pair_integrable) _ _ (hu.sub hb).aestronglyMeasurable hb.aestronglyMeasurable hc2 hb2)
    ((paid_output_parseval% square_pair_integrable) _ _ hu.aestronglyMeasurable (hu.sub hb).aestronglyMeasurable hu2 hc2) hebase
  simp only [inner_self_eq_norm_sq_to_K,←RCLike.ofReal_pow] at h
  rw [integral_ofReal,integral_ofReal] at h
  exact Complex.ofReal_injective h


private def frequencyScale (advanced : Bool) : ℝ := -FullYPairedParseval.direction advanced*(2*Real.pi)
private theorem scale_ne (advanced : Bool) : frequencyScale advanced≠0 := by
  cases advanced <;> simp [frequencyScale,FullYPairedParseval.direction,Real.pi_ne_zero]
private theorem scale_abs (advanced : Bool) : |frequencyScale advanced|=2*Real.pi := by
  cases advanced <;> simp [frequencyScale,FullYPairedParseval.direction,abs_of_pos Real.pi_pos]
private theorem line_scale (advanced : Bool) (μ ξ : ℝ) :
    line (FullYPairedParseval.direction advanced*μ) (frequencyScale advanced*ξ)=sourceLine advanced μ ξ := by
  cases advanced <;> simp only [line,frequencyScale,sourceLine,FullYPairedParseval.direction,ite_true,
    Bool.false_eq_true,ite_false,Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_one,Complex.ofReal_ofNat]
  all_goals ring
private theorem fourier_reader (P : H →L[ℂ] H) (u : ℝ → H) (hu : Integrable u) (ξ : ℝ) :
    𝓕 (fun t => P (u t)) ξ=P (𝓕 u ξ) := by
  rw [Real.fourier_eq,Real.fourier_eq]
  rw [←ContinuousLinearMap.integral_comp_comm P (Real.fourierIntegral_convergent_iff ξ |>.mpr hu)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun t => (map_smul P _ _).symm)

/-- Every bounded output reads the same complete source inverse and causal Fourier history, with the original 2π frequency convention. -/
theorem actual_output_fourier_mass_return (F : Index) (sharp : Bool) (g : QuantumTest) (advanced : Bool)
    (μ : ℝ) (hμ : 0 < μ) (P : H →L[ℂ] H) (ξ : ℝ) :
    ‖P (embed (literalResponse F sharp g advanced μ hμ (frequencyScale advanced*ξ)))‖^2=
      ‖𝓕 (fun t => P (sourceWave F sharp g advanced μ t)) ξ‖^2 := by
  have he : embed (literalResponse F sharp g advanced μ hμ (frequencyScale advanced*ξ))=
      ((FullYPairedParseval.direction advanced:ℂ)*Complex.I) • 𝓕 (sourceWave F sharp g advanced μ) ξ := by
    simp only [literalResponse,line_scale]
    exact (actual_source_wave_fourier F sharp g advanced μ hμ ξ).symm
  rw [he,map_smul,fourier_reader P _ (actual_source_wave_integrable F sharp g advanced μ hμ),norm_smul]
  cases advanced <;> simp [FullYPairedParseval.direction]

private theorem scale_mass_return (a b s : ℝ) (hs : s≠0) (h : s⁻¹*a=b) : a=s*b := by
  have he := congrArg (fun x : ℝ => s*x) h
  simpa only [←mul_assoc,mul_inv_cancel₀ hs,one_mul] using he

/-- Original source norm, its two jets and the positive baseline generate both positive output masses; no fullY norm conservation or output budget is supplied. -/
theorem actual_output_positive_mass (F : Index) (sharp : Bool) (g : QuantumTest) (advanced : Bool)
    (μ : ℝ) (hμ : 0 < μ) (P : H →L[ℂ] H) :
    Integrable (fun w : ℝ => ‖P (embed (literalResponse F sharp g advanced μ hμ w))‖^2) ∧
      Integrable (fun t : ℝ => ‖P (sourceWave F sharp g advanced μ t)‖^2) ∧
      (∫w : ℝ,‖P (embed (literalResponse F sharp g advanced μ hμ w))‖^2)=
        (2*Real.pi)*(∫t : ℝ,‖P (sourceWave F sharp g advanced μ t)‖^2) := by
  have hF : Integrable (fun w : ℝ => ‖P (embed (literalResponse F sharp g advanced μ hμ w))‖^2) := by
    apply ((actual_response_square_integrable F sharp g advanced μ hμ).const_mul (‖P‖^2)).mono'
      ((P.continuous.comp (actual_response_continuous F sharp g advanced μ hμ)).norm.pow 2).aestronglyMeasurable
    apply Eventually.of_forall
    intro w
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact (pow_le_pow_left₀ (norm_nonneg _) (P.le_opNorm _) 2).trans_eq (mul_pow _ _ _)
  have hT : Integrable (fun t : ℝ => ‖P (sourceWave F sharp g advanced μ t)‖^2) := by
    apply ((actual_source_wave_square_integrable F sharp g advanced μ hμ).const_mul (‖P‖^2)).mono'
      ((P.continuous.comp_aestronglyMeasurable
        (actual_source_wave_integrable F sharp g advanced μ hμ).aestronglyMeasurable).norm.pow 2)
    apply Eventually.of_forall
    intro t
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact (pow_le_pow_left₀ (norm_nonneg _) (P.le_opNorm _) 2).trans_eq (mul_pow _ _ _)
  refine ⟨hF,hT,?_⟩
  have h := (integral_congr_ae (Eventually.of_forall (actual_output_fourier_mass_return F sharp g advanced μ hμ P))).trans
    (actual_source_output_parseval F sharp g advanced μ hμ P)
  have hs := MeasureTheory.Measure.integral_comp_mul_left
    (fun w : ℝ => ‖P (embed (literalResponse F sharp g advanced μ hμ w))‖^2) (frequencyScale advanced)
  have h0 := hs.symm.trans h
  clear h
  simp only [abs_inv,scale_abs,smul_eq_mul] at h0
  exact scale_mass_return _ _ _ (by positivity : 2*Real.pi≠0) h0


theorem actual_absolute_output_mass (F : Index) (sharp : Bool) (q : QuantumTest) (p : Kinematics)
    (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) :
    Integrable (fun w : ℝ => density F sharp q p advanced μ hμ w) ∧
      Integrable (fun t : ℝ => ‖causalOutput F sharp q p advanced μ t‖^2) ∧
      (∫w : ℝ,density F sharp q p advanced μ hμ w) =
        (2*Real.pi)*(∫t : ℝ,‖causalOutput F sharp q p advanced μ t‖^2) := by
  have h := actual_output_positive_mass F sharp q advanced μ hμ
    (sourceReader F sharp q (coherentSource p))
  have hw (w : ℝ) :
      sourceReader F sharp q (coherentSource p)
        (embed (literalResponse F sharp q advanced μ hμ w)) =
        output F sharp q p advanced μ hμ w := by
    exact source_reader_return F sharp q _ (coherentSource p)
      (actual_response_orbit F sharp q advanced μ hμ w)
  simp_rw [hw] at h
  simpa only [ActualFourBlockRetarded.density,actual_causal_readout] using h

theorem actual_causal_spectrum_mass (F : Index) (sharp : Bool) (q : QuantumTest) (p : Kinematics)
    (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) :
    spectrum F sharp q p advanced μ hμ Set.univ =
      ENNReal.ofReal ((2*Real.pi)*(∫t : ℝ,‖causalOutput F sharp q p advanced μ t‖^2)) := by
  rw [(actual_spectrum_bands F sharp q p advanced μ hμ).1 Set.univ MeasurableSet.univ,
    Measure.restrict_univ,(actual_absolute_output_mass F sharp q p advanced μ hμ).2.2]


end LowEnergy.ActualFourBlockSharpCausalMass
