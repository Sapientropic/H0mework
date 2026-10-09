import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceFullYRetardedMomentMeasure
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.FullYDynamicCausalJets
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussUnitaryHistory
open FullYDynamicSource FullYDynamicResponse FullYPairedParseval MeasureTheory SourceResolventBandLimit
open Filter Set CompositeFullYBorn
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
open scoped FourierTransform ENNReal
attribute [local irreducible] embed literalCoreResolvent literalSharpResolvent sourceWave

private def frequencyScale (advanced : Bool) : ℝ :=
  -FullYPairedParseval.direction advanced*(2*Real.pi)
private theorem scale_ne (advanced : Bool) : frequencyScale advanced ≠ 0 := by
  cases advanced <;> simp [frequencyScale,FullYPairedParseval.direction,Real.pi_ne_zero]
private theorem scale_abs (advanced : Bool) : |frequencyScale advanced|=2*Real.pi := by
  cases advanced <;> simp [frequencyScale,FullYPairedParseval.direction,abs_of_pos Real.pi_pos]
private theorem line_scale (advanced : Bool) (μ ξ : ℝ) :
    line (FullYPairedParseval.direction advanced*μ) (frequencyScale advanced*ξ)=sourceLine advanced μ ξ := by
  cases advanced <;> simp only [line,frequencyScale,sourceLine,FullYPairedParseval.direction,
    ite_true,Bool.false_eq_true,ite_false,Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_one,Complex.ofReal_ofNat]
  all_goals ring
private theorem source_fourier (F : Index) (sharp : Bool) (q : QuantumTest)
    (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (ξ : ℝ) :
    embed (literalResponse F sharp q advanced μ hμ (frequencyScale advanced*ξ))=
      ((FullYPairedParseval.direction advanced:ℂ)*Complex.I) • 𝓕 (sourceWave F sharp q advanced μ) ξ := by
  simp only [literalResponse,line_scale]
  exact (actual_source_wave_fourier F sharp q advanced μ hμ ξ).symm
private theorem causal_scalar_norm (advanced : Bool) :
    ‖((FullYPairedParseval.direction advanced:ℂ)*Complex.I)‖=1 := by
  cases advanced <;> simp [FullYPairedParseval.direction]
private theorem time_orbit(F:Index)(sharp:Bool)(q:QuantumTest)(t:ℝ):
    literalCoreTime F sharp q t∈sourceOrbit F sharp q := by
  unfold literalCoreTime
  exact ((sourceEquiv F sharp q).symm
    (SourceFiniteUnitary.time (sourceGenerator F sharp q) t
      (sourceEquiv F sharp q ⟨q,sourceOrbit_input F sharp q⟩))).property
private def wordWave(F:Index)(sharp:Bool)(q:QuantumTest)(A:End)(advanced:Bool)(μ:ℝ):ℝ→H:=
  fun t => sourceReader F sharp q A (sourceWave F sharp q advanced μ t)
private theorem relative_word_wave(F G:Index)(sharp:Bool)(q:QuantumTest)(A:End)(advanced:Bool)(μ:ℝ):
    causalRelativeJet F G sharp q A advanced μ 0=wordWave F sharp q A advanced μ-wordWave G sharp q A advanced μ:=by
  funext t
  by_cases ht:t∈Ioi (0:ℝ)
  · simp only [causalRelativeJet,dampedTimeJet,pow_zero,Module.End.one_apply,
      wordWave,sourceWave,causalWave,Pi.sub_apply,indicator_of_mem ht,map_smul]
    rw [source_reader_return F sharp q _ A (time_orbit F sharp q (direction advanced*t)),
      source_reader_return G sharp q _ A (time_orbit G sharp q (direction advanced*t))]
  · simp only [causalRelativeJet,wordWave,sourceWave,causalWave,Pi.sub_apply,
      indicator_of_notMem ht,map_zero,sub_self]
private theorem fourier_reader(P:H→L[ℂ]H)(u:ℝ→H)(hu:Integrable u)(ξ:ℝ):
    𝓕 (fun t=>P (u t)) ξ=P (𝓕 u ξ):=by
  rw [Real.fourier_eq,Real.fourier_eq]
  rw [←ContinuousLinearMap.integral_comp_comm P (Real.fourierIntegral_convergent_iff ξ |>.mpr hu)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun t=>(map_smul P _ _).symm)
private theorem word_integrable(F:Index)(sharp:Bool)(q:QuantumTest)(A:End)
    (advanced:Bool)(μ:ℝ)(hμ:0<μ):Integrable (wordWave F sharp q A advanced μ):=
  (sourceReader F sharp q A).integrable_comp (actual_source_wave_integrable F sharp q advanced μ hμ)
private theorem word_fourier(F:Index)(sharp:Bool)(q:QuantumTest)(A:End)
    (advanced:Bool)(μ:ℝ)(hμ:0<μ)(ξ:ℝ):
    embed (A (literalResponse F sharp q advanced μ hμ (frequencyScale advanced*ξ)))=
      ((FullYPairedParseval.direction advanced:ℂ)*Complex.I) • 𝓕 (wordWave F sharp q A advanced μ) ξ:=by
  rw [←source_reader_return F sharp q _ A
    (actual_response_orbit F sharp q advanced μ hμ (frequencyScale advanced*ξ)),source_fourier,map_smul]
  rw [show wordWave F sharp q A advanced μ=(fun t=>sourceReader F sharp q A (sourceWave F sharp q advanced μ t)) from rfl,
    fourier_reader _ _ (actual_source_wave_integrable F sharp q advanced μ hμ)]
private theorem word_difference_norm(F G:Index)(sharp:Bool)(q:QuantumTest)(A:End)
    (advanced:Bool)(μ:ℝ)(hμ:0<μ)(ξ:ℝ):
    ‖embed (A (literalResponse F sharp q advanced μ hμ (frequencyScale advanced*ξ)))-
      embed (A (literalResponse G sharp q advanced μ hμ (frequencyScale advanced*ξ)))‖=
      ‖𝓕 (causalRelativeJet F G sharp q A advanced μ 0) ξ‖:=by
  rw [word_fourier,word_fourier,←smul_sub,norm_smul,causal_scalar_norm,one_mul,relative_word_wave]
  congr 1
  exact (fourier_sub_integrable _ _ (word_integrable F sharp q A advanced μ hμ)
    (word_integrable G sharp q A advanced μ hμ) ξ).symm
private theorem frequency_norm (ξ : ℝ) (n : ℕ) :
    ‖(2*Real.pi*Complex.I*(ξ:ℂ))^n‖=(2*Real.pi*|ξ|)^n := by
  simp only [norm_pow,norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
    Complex.norm_I,mul_one,abs_of_pos Real.pi_pos]

def retardedWordMomentDensity (F G : Index) (sharp : Bool) (q : QuantumTest) (A : End)
    (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (m : ℕ) (ω : ℝ) : ℝ :=
  |ω|^(2*m)*‖embed (A (literalResponse F sharp q advanced μ hμ ω))-
    embed (A (literalResponse G sharp q advanced μ hμ ω))‖^2
def retardedWordMomentMeasure (F G : Index) (sharp : Bool) (q : QuantumTest) (A : End)
    (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (m : ℕ) : Measure ℝ :=
  volume.withDensity (fun ω => ENNReal.ofReal (retardedWordMomentDensity F G sharp q A advanced μ hμ m ω))
private theorem density_nonnegative (F G : Index) (sharp : Bool) (q : QuantumTest) (A : End)
    (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (m : ℕ) (ω : ℝ) :
    0 ≤ retardedWordMomentDensity F G sharp q A advanced μ hμ m ω := by
  unfold retardedWordMomentDensity
  positivity
private theorem density_mass_return (F G : Index) (sharp : Bool) (q : QuantumTest) (A : End)
    (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (m : ℕ)
    (hi : Integrable (retardedWordMomentDensity F G sharp q A advanced μ hμ m)) :
    (∀S : Set ℝ, MeasurableSet S → retardedWordMomentMeasure F G sharp q A advanced μ hμ m S=
      ENNReal.ofReal (∫ω in S, retardedWordMomentDensity F G sharp q A advanced μ hμ m ω)) ∧
    retardedWordMomentMeasure F G sharp q A advanced μ hμ m Set.univ < ∞ := by
  have hS(S : Set ℝ)(hS : MeasurableSet S) : retardedWordMomentMeasure F G sharp q A advanced μ hμ m S=
      ENNReal.ofReal (∫ω in S, retardedWordMomentDensity F G sharp q A advanced μ hμ m ω) := by
    rw [retardedWordMomentMeasure,withDensity_apply _ hS]
    exact (ofReal_integral_eq_lintegral_ofReal hi.restrict
      (Filter.Eventually.of_forall (density_nonnegative F G sharp q A advanced μ hμ m))).symm
  exact ⟨hS,by rw [hS Set.univ MeasurableSet.univ];exact ENNReal.ofReal_lt_top⟩
private theorem physical_word_moment_mass (F G : Index) (sharp : Bool) (q : QuantumTest) (A : End)
    (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (m : ℕ)
    (hi : Integrable (fun ξ : ℝ => ‖𝓕 (iteratedDeriv m
      (causalRelativeJet F G sharp q A advanced μ 0)) ξ‖^2))
    (he : ∀ξ : ℝ, 𝓕 (iteratedDeriv m
      (causalRelativeJet F G sharp q A advanced μ 0)) ξ=
      (2*Real.pi*Complex.I*(ξ:ℂ))^m •
        𝓕 (causalRelativeJet F G sharp q A advanced μ 0) ξ) :
    Integrable (retardedWordMomentDensity F G sharp q A advanced μ hμ m) ∧
    (∫ω : ℝ, retardedWordMomentDensity F G sharp q A advanced μ hμ m ω)=
      (2*Real.pi)*(∫ξ : ℝ, ‖𝓕 (iteratedDeriv m
        (causalRelativeJet F G sharp q A advanced μ 0)) ξ‖^2) := by
  have hs(ξ : ℝ) : retardedWordMomentDensity F G sharp q A advanced μ hμ m (frequencyScale advanced*ξ)=
      ‖𝓕 (iteratedDeriv m (causalRelativeJet F G sharp q A advanced μ 0)) ξ‖^2 := by
    rw [retardedWordMomentDensity,word_difference_norm,he,norm_smul,frequency_norm,mul_pow,
      abs_mul,scale_abs]
    rw [←pow_mul]
    congr 2
    omega
  have hf : Integrable (retardedWordMomentDensity F G sharp q A advanced μ hμ m) :=
    (integrable_comp_mul_left_iff _ (scale_ne advanced)).mp
      (hi.congr (Filter.Eventually.of_forall (fun ξ => (hs ξ).symm)))
  refine ⟨hf,?_⟩
  have ht := MeasureTheory.Measure.integral_comp_mul_left
    (retardedWordMomentDensity F G sharp q A advanced μ hμ m) (frequencyScale advanced)
  have hh := (integral_congr_ae (Filter.Eventually.of_forall hs)).symm.trans ht
  simp only [abs_inv,scale_abs,smul_eq_mul] at hh
  have h := congrArg (fun x : ℝ => (2*Real.pi)*x) hh
  simpa only [←mul_assoc,mul_inv_cancel₀ (by positivity : 2*Real.pi ≠ 0),one_mul] using h.symm

/-- Every original core output word generates its own finite positive
retarded moment measure, including unbounded composite words. The two
source-carrier restrictions pay the Fourier return before their difference. -/
theorem actual_cofinal_retarded_word_moment_measure (B : Index) (q : QuantumTest) (N : ℕ) :
    ∃K₀ : Index, B⊆K₀ ∧ ∀F : Index, K₀⊆F → ∀G : Index, K₀⊆G →
      ∀sharp advanced : Bool, ∀μ : ℝ, ∀hμ : 0 < μ, ∀A : End, ∀m : ℕ, m ≤ N →
      let u := causalRelativeJet F G sharp q A advanced μ 0
      Integrable (retardedWordMomentDensity F G sharp q A advanced μ hμ m) ∧
      (∫ω : ℝ, retardedWordMomentDensity F G sharp q A advanced μ hμ m ω)=
        (2*Real.pi)*(∫t : ℝ, ‖iteratedDeriv m u t‖^2) ∧
      (∀S : Set ℝ, MeasurableSet S → retardedWordMomentMeasure F G sharp q A advanced μ hμ m S=
        ENNReal.ofReal (∫ω in S, retardedWordMomentDensity F G sharp q A advanced μ hμ m ω)) ∧
      retardedWordMomentMeasure F G sharp q A advanced μ hμ m Set.univ < ∞ := by
  obtain ⟨K₁,hB,hK₁⟩ := actual_cofinal_causal_jet_positive_parseval B q N
  obtain ⟨K₂,h₁₂,hK₂⟩ := actual_cofinal_causal_fourier_derivatives K₁ q N
  refine ⟨K₂,Finset.Subset.trans hB h₁₂,fun F hF G hG sharp advanced μ hμ A m hm => ?_⟩
  have hp := hK₁ F (Finset.Subset.trans h₁₂ hF) G (Finset.Subset.trans h₁₂ hG)
    sharp advanced μ hμ A m hm
  have h := physical_word_moment_mass F G sharp q A advanced μ hμ m hp.2.2.1
    (hK₂ F hF G hG sharp advanced μ hμ A m hm)
  exact ⟨h.1,h.2.trans (congrArg (fun x : ℝ => (2*Real.pi)*x) hp.2.2.2),
    density_mass_return F G sharp q A advanced μ hμ m h.1⟩

end LowEnergy.FullYDynamicCausalJets
