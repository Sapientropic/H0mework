import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.MixedSpectatorFourBlockSource
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.MixedSpectatorDynamicResponse
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceFullYCompositeContactOptical
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceFullYRetardedWordMomentMeasure

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualFourBlockRetarded
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussUnitaryHistory GaussFockPair
open FullYDynamicSource FullYDynamicResponse FullYPairedParseval CompositeFullYBorn
open SourceResolventBandLimit ActualFourBlockSource MixedSpectatorCandidate
open MeasureTheory Filter Set
open scoped BigOperators Topology FourierTransform InnerProductSpace ENNReal
attribute [local irreducible] embed sourcePair literalCoreResolvent literalSharpResolvent
  sourceOrbit sourceSpace sourceWave coherentSource blockSource

/-- External transfer and the two independent matter momenta are fixed while
the original unforced response runs along its full frequency line. -/
def output (F : Index) (sharp : Bool) (q : QuantumTest) (p : Kinematics)
    (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (ω : ℝ) : H :=
  embed (coherentSource p (literalResponse F sharp q advanced μ hμ ω))

def blockOutput (F : Index) (sharp : Bool) (q : QuantumTest) (p : Kinematics) (b : Fin 4)
    (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (ω : ℝ) : H :=
  embed (blockSource p b (literalResponse F sharp q advanced μ hμ ω))

def density (F : Index) (sharp : Bool) (q : QuantumTest) (p : Kinematics)
    (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (ω : ℝ) : ℝ :=
  ‖output F sharp q p advanced μ hμ ω‖^2

def spectrum (F : Index) (sharp : Bool) (q : QuantumTest) (p : Kinematics)
    (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) : Measure ℝ :=
  volume.withDensity (fun ω => ENNReal.ofReal (density F sharp q p advanced μ hμ ω))

theorem actual_coherent_output (F : Index) (sharp : Bool) (q : QuantumTest) (p : Kinematics)
    (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (ω : ℝ) :
    output F sharp q p advanced μ hμ ω =
      ∑b : Fin 4,blockOutput F sharp q p b advanced μ hμ ω := by
  simp only [output,blockOutput,coherentSource,LinearMap.sum_apply,map_sum]

/-- All sixteen complex Gram entries survive before taking the real positive
diagonal. In particular the four departments are not added as intensities. -/
theorem actual_coherent_gram (F : Index) (sharp : Bool) (q : QuantumTest) (p : Kinematics)
    (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (ω : ℝ) :
    density F sharp q p advanced μ hμ ω =
      (∑a : Fin 4,∑b : Fin 4,
        inner ℂ (blockOutput F sharp q p a advanced μ hμ ω)
          (blockOutput F sharp q p b advanced μ hμ ω)).re := by
  have h : inner ℂ (output F sharp q p advanced μ hμ ω)
      (output F sharp q p advanced μ hμ ω) = (∑a : Fin 4,∑b : Fin 4,
      inner ℂ (blockOutput F sharp q p a advanced μ hμ ω)
        (blockOutput F sharp q p b advanced μ hμ ω)) := by
    rw [actual_coherent_output]
    simp only [sum_inner,inner_sum]
    rw [Finset.sum_comm]
  change ‖output F sharp q p advanced μ hμ ω‖^2 = _
  rw [←inner_self_eq_norm_sq (𝕜 := ℂ)]
  exact congrArg Complex.re h

theorem actual_gram_integrable (F : Index) (sharp : Bool) (q : QuantumTest) (p : Kinematics)
    (a b : Fin 4) (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) :
    Integrable (fun ω : ℝ => inner ℂ (blockOutput F sharp q p a advanced μ hμ ω)
      (blockOutput F sharp q p b advanced μ hμ ω)) := by
  simpa only [sourcePair,blockOutput] using
    CompositeChannelOptical.actual_word_pair_integrable F sharp q advanced μ hμ
      (blockSource p a) (blockSource p b)

theorem actual_density_integrable (F : Index) (sharp : Bool) (q : QuantumTest) (p : Kinematics)
    (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) :
    Integrable (density F sharp q p advanced μ hμ) :=
  actual_core_word_square_integrable F sharp q advanced μ hμ (coherentSource p)

/-- The complete actual exchange generates a positive finite output measure
on every frequency band, with its coherent interference retained. -/
theorem actual_spectrum_bands (F : Index) (sharp : Bool) (q : QuantumTest) (p : Kinematics)
    (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) :
    (∀S : Set ℝ,MeasurableSet S → spectrum F sharp q p advanced μ hμ S =
      ENNReal.ofReal (∫ω in S,density F sharp q p advanced μ hμ ω)) ∧
    spectrum F sharp q p advanced μ hμ Set.univ < ∞ := by
  have mass (S : Set ℝ) (hS : MeasurableSet S) :
      spectrum F sharp q p advanced μ hμ S =
        ENNReal.ofReal (∫ω in S,density F sharp q p advanced μ hμ ω) := by
    rw [spectrum,withDensity_apply _ hS]
    exact (ofReal_integral_eq_lintegral_ofReal
      (actual_density_integrable F sharp q p advanced μ hμ).restrict
      (Eventually.of_forall (fun _ => sq_nonneg _))).symm
  exact ⟨mass,by rw [mass Set.univ MeasurableSet.univ];exact ENNReal.ofReal_lt_top⟩

def causalOutput (F : Index) (sharp : Bool) (q : QuantumTest) (p : Kinematics)
    (advanced : Bool) (μ : ℝ) : ℝ → H :=
  causalWave μ (fun t => embed (coherentSource p
    (literalCoreTime F sharp q (direction advanced*t))))

private theorem time_orbit (F : Index) (sharp : Bool) (q : QuantumTest) (t : ℝ) :
    literalCoreTime F sharp q t ∈ sourceOrbit F sharp q := by
  unfold literalCoreTime
  exact ((sourceEquiv F sharp q).symm
    (SourceFiniteUnitary.time (sourceGenerator F sharp q) t
      (sourceEquiv F sharp q ⟨q,sourceOrbit_input F sharp q⟩))).property

theorem actual_causal_readout (F : Index) (sharp : Bool) (q : QuantumTest) (p : Kinematics)
    (advanced : Bool) (μ : ℝ) :
    causalOutput F sharp q p advanced μ =
      fun t => sourceReader F sharp q (coherentSource p) (sourceWave F sharp q advanced μ t) := by
  funext t
  by_cases ht : t ∈ Ioi (0 : ℝ)
  · simp only [causalOutput,sourceWave,causalWave,indicator_of_mem ht,map_smul]
    rw [source_reader_return F sharp q _ (coherentSource p)
      (time_orbit F sharp q (direction advanced*t))]
  · simp only [causalOutput,sourceWave,causalWave,indicator_of_notMem ht,map_zero]

theorem actual_causal_integrable (F : Index) (sharp : Bool) (q : QuantumTest) (p : Kinematics)
    (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) :
    Integrable (causalOutput F sharp q p advanced μ) := by
  rw [actual_causal_readout]
  exact (sourceReader F sharp q (coherentSource p)).integrable_comp
    (actual_source_wave_integrable F sharp q advanced μ hμ)

def frequencyScale (advanced : Bool) : ℝ := -direction advanced*(2*Real.pi)

private theorem line_scale (advanced : Bool) (μ ξ : ℝ) :
    line (direction advanced*μ) (frequencyScale advanced*ξ) = sourceLine advanced μ ξ := by
  cases advanced <;> simp only [line,frequencyScale,sourceLine,FullYPairedParseval.direction,ite_true,
    Bool.false_eq_true,ite_false,Complex.ofReal_mul,Complex.ofReal_neg,
    Complex.ofReal_one,Complex.ofReal_ofNat]
  all_goals ring

private theorem fourier_reader (P : H →L[ℂ] H) (u : ℝ → H) (hu : Integrable u) (ξ : ℝ) :
    𝓕 (fun t => P (u t)) ξ = P (𝓕 u ξ) := by
  rw [Real.fourier_eq,Real.fourier_eq]
  rw [←ContinuousLinearMap.integral_comp_comm P (Real.fourierIntegral_convergent_iff ξ |>.mpr hu)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun t => (map_smul P _ _).symm)

/-- The actual coherent four-block frequency output is the Fourier transform
of its own original causal history, on either independent sharp/cause branch. -/
theorem actual_output_fourier (F : Index) (sharp : Bool) (q : QuantumTest) (p : Kinematics)
    (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (ξ : ℝ) :
    output F sharp q p advanced μ hμ (frequencyScale advanced*ξ) =
      ((direction advanced : ℂ)*Complex.I) • 𝓕 (causalOutput F sharp q p advanced μ) ξ := by
  have hs : embed (literalResponse F sharp q advanced μ hμ (frequencyScale advanced*ξ)) =
      ((direction advanced : ℂ)*Complex.I) • 𝓕 (sourceWave F sharp q advanced μ) ξ := by
    simp only [literalResponse,line_scale]
    exact (actual_source_wave_fourier F sharp q advanced μ hμ ξ).symm
  rw [output,←source_reader_return F sharp q _ (coherentSource p)
    (actual_response_orbit F sharp q advanced μ hμ (frequencyScale advanced*ξ)),hs,map_smul,
    actual_causal_readout,fourier_reader _ _ (actual_source_wave_integrable F sharp q advanced μ hμ)]

/-- One original source event, selected before all regular transfer and
independent matter momenta, pays every prescribed relative retarded moment
of the complete coherent four-block exchange. -/
theorem actual_cofinal_four_block_moment_measure (B : Index) (dual : Bool) (f : GaussDensityCore.ScalarTest)
    (N : ℕ) :
    ∃K₀ : Index,B ⊆ K₀ ∧ ∀F : Index,K₀ ⊆ F → ∀G : Index,K₀ ⊆ G →
      ∀sharp advanced : Bool,∀μ : ℝ,∀hμ : 0 < μ,∀p : Kinematics,∀m : ℕ,m ≤ N →
      let q := candidateTest dual f
      let A := coherentSource p
      let u := FullYDynamicCausalJets.causalRelativeJet F G sharp q A advanced μ 0
      Integrable (FullYDynamicCausalJets.retardedWordMomentDensity F G sharp q A advanced μ hμ m) ∧
      (∫ω : ℝ,FullYDynamicCausalJets.retardedWordMomentDensity F G sharp q A advanced μ hμ m ω) =
        (2*Real.pi)*(∫t : ℝ,‖iteratedDeriv m u t‖^2) ∧
      (∀S : Set ℝ,MeasurableSet S →
        FullYDynamicCausalJets.retardedWordMomentMeasure F G sharp q A advanced μ hμ m S =
          ENNReal.ofReal (∫ω in S,
            FullYDynamicCausalJets.retardedWordMomentDensity F G sharp q A advanced μ hμ m ω)) ∧
      FullYDynamicCausalJets.retardedWordMomentMeasure F G sharp q A advanced μ hμ m Set.univ < ∞ := by
  obtain ⟨K₀,hB,hK⟩ := FullYDynamicCausalJets.actual_cofinal_retarded_word_moment_measure
    B (candidateTest dual f) N
  exact ⟨K₀,hB,fun F hF G hG sharp advanced μ hμ p m hm =>
    hK F hF G hG sharp advanced μ hμ (coherentSource p) m hm⟩

end LowEnergy.ActualFourBlockRetarded
