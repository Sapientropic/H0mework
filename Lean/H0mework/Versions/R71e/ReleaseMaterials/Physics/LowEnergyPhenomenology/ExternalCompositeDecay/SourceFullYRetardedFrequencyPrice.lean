import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceFullYCausalFrequencyPrice
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.FullYDynamicCausalJets
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussUnitaryHistory
open FullYDynamicSource FullYDynamicResponse FullYPairedParseval MeasureTheory SourceResolventBandLimit
open scoped FourierTransform
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
private theorem response_difference_norm (F G : Index) (sharp : Bool) (q : QuantumTest)
    (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (ξ : ℝ) :
    ‖embed (literalResponse F sharp q advanced μ hμ (frequencyScale advanced*ξ))-
      embed (literalResponse G sharp q advanced μ hμ (frequencyScale advanced*ξ))‖=
      ‖𝓕 (fun t : ℝ => sourceWave F sharp q advanced μ t-sourceWave G sharp q advanced μ t) ξ‖ := by
  rw [source_fourier,source_fourier,←smul_sub,norm_smul,causal_scalar_norm,one_mul]
  congr 1
  exact (fourier_sub_integrable _ _ (actual_source_wave_integrable F sharp q advanced μ hμ)
    (actual_source_wave_integrable G sharp q advanced μ hμ) ξ).symm

/-- Every prescribed frequency power of the original physical response
is paid by its own causal derivative, on one source-generated event. -/
theorem actual_cofinal_retarded_response_frequency_price (B : Index) (q : QuantumTest) (N : ℕ) :
    ∃K₀ : Index, B⊆K₀ ∧ ∀F : Index, K₀⊆F → ∀G : Index, K₀⊆G →
      ∀sharp advanced : Bool, ∀μ : ℝ, ∀hμ : 0 < μ, ∀m : ℕ, m ≤ N →
      let u := fun t : ℝ => sourceWave F sharp q advanced μ t-sourceWave G sharp q advanced μ t
      Integrable (iteratedDeriv m u) ∧ ∀ω : ℝ,
        |ω|^m*‖embed (literalResponse F sharp q advanced μ hμ ω)-
          embed (literalResponse G sharp q advanced μ hμ ω)‖ ≤ ∫t : ℝ, ‖iteratedDeriv m u t‖ := by
  obtain ⟨K₀,hB,hK₀⟩ := actual_cofinal_original_wave_frequency_price B q N
  refine ⟨K₀,hB,fun F hF G hG sharp advanced μ hμ m hm => ?_⟩
  have h := hK₀ F hF G hG sharp advanced μ hμ m hm
  refine ⟨h.1,fun ω => ?_⟩
  let ξ := (frequencyScale advanced)⁻¹*ω
  have he : frequencyScale advanced*ξ=ω := by
    dsimp only [ξ]
    rw [←mul_assoc,mul_inv_cancel₀ (scale_ne advanced),one_mul]
  have ha : 2*Real.pi*|ξ|=|ω| := by
    rw [←scale_abs advanced,←abs_mul,he]
  have hb := h.2 ξ
  rw [←response_difference_norm F G sharp q advanced μ hμ ξ,he,ha] at hb
  exact hb

end LowEnergy.FullYDynamicCausalJets
