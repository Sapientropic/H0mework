import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualThreeParticleCutoffPrice
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceFiniteTimeIntegral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualThreeParticleCutoffFamily
open GaussCoreHilbert GaussCoreDifferential GaussUnitaryHistory GaussCoreLabel
open ActualThreeParticleCutoffGram ActualCutoffFrequencyBase
open SourceFamilyHilbert FullYSourceFiniteTimeIntegral
open FullYSourceResolventGraphSplice FullYSourceCutoffVolterra MeasureTheory Filter
open scoped Topology InnerProductSpace
private abbrev L2H := Lp H 2 (volume : Measure ℝ)

private theorem toLp_inner_integral {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (f g : ℝ → E)
    (hf : MemLp f 2 (volume : Measure ℝ)) (hg : MemLp g 2 (volume : Measure ℝ)) :
    inner ℂ (hf.toLp f) (hg.toLp g) = ∫w : ℝ,inner ℂ (f w) (g w) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with w hwf hwg
  rw [hwf,hwg]

def finiteResponse (F : Index) (n : ℕ) (advanced : Bool) (μ : ℝ) (hμ : 0 < μ)
    (q : QuantumTest) (hq : project (3,0) q = q) : L2H :=
  (actual_response_memLp F n advanced μ hμ q hq).toLp
    (fun w => inverse F n (frequency advanced μ w) (embed q))

theorem actual_finite_response_read (F : Index) (n : ℕ) (advanced : Bool)
    (μ : ℝ) (hμ : 0 < μ) (q : QuantumTest) (hq : project (3,0) q = q) :
    (fun w : ℝ => finiteResponse F n advanced μ hμ q hq w) =ᵐ[volume]
      (fun w => inverse F n (frequency advanced μ w) (embed q)) :=
  (actual_response_memLp F n advanced μ hμ q hq).coeFn_toLp

theorem actual_finite_response_inner (F : Index) (n : ℕ) (advanced : Bool)
    (μ : ℝ) (hμ : 0 < μ) (q r : QuantumTest)
    (hq : project (3,0) q = q) (hr : project (3,0) r = r) :
    inner ℂ (finiteResponse F n advanced μ hμ q hq) (finiteResponse F n advanced μ hμ r hr) =
      ∫w : ℝ,inner ℂ (inverse F n (frequency advanced μ w) (embed q))
        (inverse F n (frequency advanced μ w) (embed r)) :=
  toLp_inner_integral _ _ (actual_response_memLp F n advanced μ hμ q hq)
    (actual_response_memLp F n advanced μ hμ r hr)

theorem actual_finite_response_bound (F : Index) (n : ℕ) (advanced : Bool)
    (μ : ℝ) (hμ : 0 < μ) (q : QuantumTest) (hq : project (3,0) q = q) :
    ‖finiteResponse F n advanced μ hμ q hq‖ ≤
      responsePrice n μ*Real.sqrt (Real.pi/μ*‖embed q‖^2) := by
  have hb : ‖finiteResponse F n advanced μ hμ q hq‖ ≤
      responsePrice n μ*‖finiteBase F advanced μ hμ (embed q)‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [actual_finite_response_read F n advanced μ hμ q hq,
      actual_finite_base_read F advanced μ hμ (embed q)] with w hw hr
    rw [hw,hr]
    exact actual_response_price F n advanced μ hμ q hq w
  exact hb.trans (mul_le_mul_of_nonneg_left
    (actual_finite_base_bound F advanced μ hμ (embed q)) (actual_response_price_nonnegative n μ hμ))

/-- The original 57-term inverse is admitted to the existing full-frequency
source-family Hilbert space using its internally generated Number-three price. -/
def responseFamily (n : ℕ) (advanced : Bool) (μ : ℝ) (hμ : 0 < μ)
    (q : QuantumTest) (hq : project (3,0) q = q) : Family L2H sourceFilter where
  val F := finiteResponse F n advanced μ hμ q hq
  property := ⟨responsePrice n μ*Real.sqrt (Real.pi/μ*‖embed q‖^2),
    mul_nonneg (actual_response_price_nonnegative n μ hμ) (Real.sqrt_nonneg _),
    fun F => actual_finite_response_bound F n advanced μ hμ q hq⟩

theorem actual_response_family_value (n : ℕ) (advanced : Bool) (μ : ℝ) (hμ : 0 < μ)
    (q : QuantumTest) (hq : project (3,0) q = q) (F : Index) :
    value (responseFamily n advanced μ hμ q hq) F = finiteResponse F n advanced μ hμ q hq := rfl

def sourceFrequency (n : ℕ) (advanced : Bool) (μ : ℝ) (hμ : 0 < μ)
    (q : QuantumTest) (hq : project (3,0) q = q) : TimeSpace (volume : Measure ℝ) :=
  (responseFamily n advanced μ hμ q hq : TimeSpace (volume : Measure ℝ))

theorem actual_source_frequency_norm (n : ℕ) (advanced : Bool) (μ : ℝ) (hμ : 0 < μ)
    (q : QuantumTest) (hq : project (3,0) q = q) :
    ‖sourceFrequency n advanced μ hμ q hq‖ = ‖responseFamily n advanced μ hμ q hq‖ :=
  UniformSpace.Completion.norm_coe _

theorem actual_finite_response_square (F : Index) (n : ℕ) (advanced : Bool)
    (μ : ℝ) (hμ : 0 < μ) (q : QuantumTest) (hq : project (3,0) q = q) :
    ‖finiteResponse F n advanced μ hμ q hq‖^2 =
      ∫w : ℝ,‖inverse F n (frequency advanced μ w) (embed q)‖^2 := by
  rw [FullYSourceCutoffTimeGraph.square_integral]
  apply integral_congr_ae
  filter_upwards [actual_finite_response_read F n advanced μ hμ q hq] with w hw
  rw [hw]

/-- Frequency integration precedes the unchanged sourceFilter; its full mass
returns in the original TimeSpace without claiming descent back to H. -/
theorem actual_frequency_energy_limit (n : ℕ) (advanced : Bool) (μ : ℝ) (hμ : 0 < μ)
    (q : QuantumTest) (hq : project (3,0) q = q) :
    Tendsto (fun F : Index => ∫w : ℝ,‖inverse F n (frequency advanced μ w) (embed q)‖^2)
      sourceFilter (𝓝 (‖sourceFrequency n advanced μ hμ q hq‖^2)) := by
  have he (F : Index) : ‖value (responseFamily n advanced μ hμ q hq) F‖^2 =
      ∫w : ℝ,‖inverse F n (frequency advanced μ w) (embed q)‖^2 := by
    rw [actual_response_family_value]
    exact actual_finite_response_square F n advanced μ hμ q hq
  have h := (square_tendsto sourceFilter (responseFamily n advanced μ hμ q hq)).congr'
    (Eventually.of_forall he)
  simpa only [actual_source_frequency_norm] using h

theorem actual_frequency_complex_gram_limit (n : ℕ) (advanced : Bool) (μ : ℝ) (hμ : 0 < μ)
    (q r : QuantumTest) (hq : project (3,0) q = q) (hr : project (3,0) r = r) :
    Tendsto (fun F : Index => ∫w : ℝ,
      inner ℂ (inverse F n (frequency advanced μ w) (embed q))
        (inverse F n (frequency advanced μ w) (embed r))) sourceFilter
      (𝓝 (inner ℂ (sourceFrequency n advanced μ hμ q hq)
        (sourceFrequency n advanced μ hμ r hr))) := by
  have he (F : Index) :
      inner ℂ (value (responseFamily n advanced μ hμ q hq) F)
        (value (responseFamily n advanced μ hμ r hr) F) = ∫w : ℝ,
      inner ℂ (inverse F n (frequency advanced μ w) (embed q))
        (inverse F n (frequency advanced μ w) (embed r)) := by
    exact (congrArg₂ (inner ℂ)
      (actual_response_family_value n advanced μ hμ q hq F)
      (actual_response_family_value n advanced μ hμ r hr F)).trans
      (actual_finite_response_inner F n advanced μ hμ q r hq hr)
  have h := (pair_tendsto sourceFilter (responseFamily n advanced μ hμ q hq)
    (responseFamily n advanced μ hμ r hr)).congr' (Eventually.of_forall he)
  have ht : inner ℂ (sourceFrequency n advanced μ hμ q hq)
      (sourceFrequency n advanced μ hμ r hr) =
      pair sourceFilter (responseFamily n advanced μ hμ q hq) (responseFamily n advanced μ hμ r hr) :=
    SourceFamilyHilbert.inner_coe _ _ _
  simpa only [ht] using h

/-- Pointwise K and integrated TimeSpace retain restrictions of the same
actual F-indexed cutoff response, rather than a replacement propagator. -/
def pointFamily (n : ℕ) (advanced : Bool) (μ : ℝ) (hμ : 0 < μ)
    (q : QuantumTest) (hq : project (3,0) q = q) (w : ℝ) : Family H sourceFilter where
  val F := inverse F n (frequency advanced μ w) (embed q)
  property := by
    refine ⟨responsePrice n μ*(μ⁻¹*‖embed q‖),
      mul_nonneg (actual_response_price_nonnegative n μ hμ)
        (mul_nonneg (inv_nonneg.mpr hμ.le) (norm_nonneg _)),?_⟩
    intro F
    apply (actual_response_price F n advanced μ hμ q hq w).trans
    apply mul_le_mul_of_nonneg_left _ (actual_response_price_nonnegative n μ hμ)
    exact ((finiteResolvent F (frequency advanced μ w)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (actual_frequency_resolvent_norm F advanced μ hμ w) (norm_nonneg _))

theorem actual_point_family_value (n : ℕ) (advanced : Bool) (μ : ℝ) (hμ : 0 < μ)
    (q : QuantumTest) (hq : project (3,0) q = q) (w : ℝ) (F : Index) :
    value (pointFamily n advanced μ hμ q hq w) F =
      inverse F n (frequency advanced μ w) (embed q) := rfl

def sourcePoint (n : ℕ) (advanced : Bool) (μ : ℝ) (hμ : 0 < μ)
    (q : QuantumTest) (hq : project (3,0) q = q) (w : ℝ) : HistorySpace :=
  (pointFamily n advanced μ hμ q hq w : HistorySpace)

theorem actual_source_point_norm (n : ℕ) (advanced : Bool) (μ : ℝ) (hμ : 0 < μ)
    (q : QuantumTest) (hq : project (3,0) q = q) (w : ℝ) :
    ‖sourcePoint n advanced μ hμ q hq w‖ = ‖pointFamily n advanced μ hμ q hq w‖ :=
  UniformSpace.Completion.norm_coe _

theorem actual_point_energy_limit (n : ℕ) (advanced : Bool) (μ : ℝ) (hμ : 0 < μ)
    (q : QuantumTest) (hq : project (3,0) q = q) (w : ℝ) :
    Tendsto (fun F : Index => ‖inverse F n (frequency advanced μ w) (embed q)‖^2)
      sourceFilter (𝓝 (‖sourcePoint n advanced μ hμ q hq w‖^2)) := by
  have h := (square_tendsto sourceFilter (pointFamily n advanced μ hμ q hq w)).congr'
    (Eventually.of_forall (fun F => congrArg (fun v : H => ‖v‖^2)
      (actual_point_family_value n advanced μ hμ q hq w F)))
  simpa only [actual_source_point_norm] using h

end LowEnergy.ActualThreeParticleCutoffFamily
