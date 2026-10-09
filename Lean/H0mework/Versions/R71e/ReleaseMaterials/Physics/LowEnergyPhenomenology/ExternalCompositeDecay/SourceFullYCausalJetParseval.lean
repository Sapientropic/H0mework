import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceFullYRetardedFrequencyPrice
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.FullYDynamicCausalJets
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussUnitaryHistory
open FullYDynamicSource FullYPairedParseval MeasureTheory Filter
open scoped FourierTransform InnerProductSpace Topology
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] causalRelativeJet embed sourceWave
local instance : SecondCountableTopologyEither ℝ H := secondCountableTopologyEither_of_left ℝ H

private theorem frequency_norm (ξ : ℝ) (n : ℕ) :
    ‖(2*Real.pi*Complex.I*(ξ:ℂ))^n‖=(2*Real.pi*|ξ|)^n := by
  simp only [norm_pow,norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
    Complex.norm_I,mul_one,abs_of_pos Real.pi_pos]

private theorem priced_fourier_integrable (u : ℝ → H) (hu : Integrable u) (a b : ℝ)
    (h0 : ∀ξ : ℝ, ‖𝓕 u ξ‖ ≤ a)
    (h2 : ∀ξ : ℝ, (2*Real.pi*|ξ|)^2*‖𝓕 u ξ‖ ≤ b) : Integrable (𝓕 u) := by
  let C := a+b/(2*Real.pi)^2
  apply ((SourceResolventLorentzian.kernel_integrable 1 0 (by norm_num)).const_mul C).mono'
    (fourier_continuous_of_integrable u hu).aestronglyMeasurable
  apply Eventually.of_forall
  intro ξ
  have hp : 0 < (2*Real.pi)^2 := by positivity
  have hsq : ξ^2*‖𝓕 u ξ‖ ≤ b/(2*Real.pi)^2 := by
    apply (le_div_iff₀ hp).mpr
    have h := h2 ξ
    simp only [mul_pow,sq_abs] at h
    nlinarith only [h]
  have ht : (1+ξ^2)*‖𝓕 u ξ‖ ≤ C := by
    dsimp only [C]
    nlinarith only [h0 ξ,hsq]
  have hden : 0 < 1+ξ^2 := by positivity
  change ‖𝓕 u ξ‖ ≤ C*((0-ξ)^2+1^2)⁻¹
  have he : (0-ξ)^2+1^2=1+ξ^2 := by ring
  rw [he,←div_eq_mul_inv]
  exact (le_div_iff₀ hden).mpr (by simpa only [mul_comm] using ht)

private theorem square_integrable (u : ℝ → H) (hu : Integrable u)
    (hbound : ∀t : ℝ, ‖u t‖ ≤ ∫s : ℝ, ‖𝓕 u s‖) : Integrable (fun t => ‖u t‖^2) := by
  apply (hu.norm.const_mul (∫s : ℝ, ‖𝓕 u s‖)).mono' (hu.aestronglyMeasurable.norm.pow 2)
  apply Eventually.of_forall
  intro t
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),pow_two]
  exact mul_le_mul_of_nonneg_right (hbound t) (norm_nonneg _)

private theorem positive_parseval (u : ℝ → H) (hu : Integrable u) (hc : Continuous u)
    (hF : Integrable (𝓕 u)) :
    Integrable (fun t => ‖u t‖^2) ∧ Integrable (fun ξ => ‖𝓕 u ξ‖^2) ∧
      (∫ξ : ℝ, ‖𝓕 u ξ‖^2)=(∫t : ℝ, ‖u t‖^2) := by
  have h_inv := hc.fourierInv_fourier_eq hu hF
  have ht2 := square_integrable u hu (fun t => by
    rw [←congrFun h_inv t,Real.fourierInv_eq_fourier_neg]
    exact fourier_bound (𝓕 u) (-t))
  have hf2 : Integrable (fun ξ => ‖𝓕 u ξ‖^2) := by
    apply (hF.norm.const_mul (∫t : ℝ, ‖u t‖)).mono'
      ((fourier_continuous_of_integrable u hu).aestronglyMeasurable.norm.pow 2)
    apply Eventually.of_forall
    intro ξ
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),pow_two]
    exact mul_le_mul_of_nonneg_right (fourier_bound u ξ) (norm_nonneg _)
  refine ⟨ht2,hf2,?_⟩
  have h := VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip (innerSL ℂ)
    (L:=innerₗ ℝ) Real.continuous_fourierChar continuous_inner hu hF
  have he : (innerₗ ℝ).flip=innerₗ ℝ := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    exact real_inner_comm x y
  rw [he] at h
  change (∫ξ : ℝ, inner ℂ (𝓕 u ξ) (𝓕 u ξ))=(∫t : ℝ, inner ℂ (u t) (𝓕⁻ (𝓕 u) t)) at h
  rw [h_inv] at h
  simp only [inner_self_eq_norm_sq_to_K,←RCLike.ofReal_pow,integral_ofReal] at h
  exact RCLike.ofReal_injective h

private theorem derivative_parseval (u : ℝ → H) (N m : ℕ) (hm : m ≤ N)
    (hc : ContDiff ℝ (N+2 : ℕ) u)
    (hi : ∀j : ℕ, j ≤ N+2 → Integrable (iteratedDeriv j u))
    (he : ∀j : ℕ, j ≤ N+2 → ∀ξ : ℝ, 𝓕 (iteratedDeriv j u) ξ=
      (2*Real.pi*Complex.I*(ξ:ℂ))^j • 𝓕 u ξ) :
    Integrable (𝓕 (iteratedDeriv m u)) ∧
    Integrable (fun t => ‖iteratedDeriv m u t‖^2) ∧
    Integrable (fun ξ => ‖𝓕 (iteratedDeriv m u) ξ‖^2) ∧
    (∫ξ : ℝ, ‖𝓕 (iteratedDeriv m u) ξ‖^2)=(∫t : ℝ, ‖iteratedDeriv m u t‖^2) := by
  have hn : m ≤ N+2 := by omega
  have hn2 : m+2 ≤ N+2 := by omega
  have hm_cont := (contDiff_nat_iff_iteratedDeriv.mp hc).1 m hn
  have hp(ξ : ℝ) : 𝓕 (iteratedDeriv (m+2) u) ξ=
      (2*Real.pi*Complex.I*(ξ:ℂ))^2 • 𝓕 (iteratedDeriv m u) ξ := by
    rw [he (m+2) hn2,he m hn,pow_add,smul_smul]
    congr 1
    exact mul_comm _ _
  have h2(ξ : ℝ) : (2*Real.pi*|ξ|)^2*‖𝓕 (iteratedDeriv m u) ξ‖ ≤
      ∫t : ℝ, ‖iteratedDeriv (m+2) u t‖ := by
    have h := fourier_bound (iteratedDeriv (m+2) u) ξ
    rw [hp,norm_smul,frequency_norm] at h
    exact h
  have hF := priced_fourier_integrable (iteratedDeriv m u) (hi m hn) _ _
    (fourier_bound (iteratedDeriv m u)) h2
  exact ⟨hF,positive_parseval (iteratedDeriv m u) (hi m hn) hm_cont hF⟩

/-- Prescribed derivatives of the original causal correction generate
their own absolute Fourier price and exact positive time/frequency mass. -/
theorem actual_cofinal_causal_jet_positive_parseval (B : Index) (q : QuantumTest) (N : ℕ) :
    ∃K₀ : Index, B⊆K₀ ∧ ∀F : Index, K₀⊆F → ∀G : Index, K₀⊆G →
      ∀sharp advanced : Bool, ∀μ : ℝ, ∀hμ : 0 < μ, ∀A : End, ∀m : ℕ, m ≤ N →
      let u := causalRelativeJet F G sharp q A advanced μ 0
      Integrable (𝓕 (iteratedDeriv m u)) ∧
      Integrable (fun t => ‖iteratedDeriv m u t‖^2) ∧
      Integrable (fun ξ => ‖𝓕 (iteratedDeriv m u) ξ‖^2) ∧
      (∫ξ : ℝ, ‖𝓕 (iteratedDeriv m u) ξ‖^2)=(∫t : ℝ, ‖iteratedDeriv m u t‖^2) := by
  obtain ⟨K₁,hB,hK₁⟩ := actual_cofinal_causal_derivatives_integrable B q (N+2)
  obtain ⟨K₂,h₁₂,hK₂⟩ := actual_cofinal_causal_fourier_derivatives K₁ q (N+2)
  refine ⟨K₂,Finset.Subset.trans hB h₁₂,fun F hF G hG sharp advanced μ hμ A m hm => ?_⟩
  have hd := hK₁ F (Finset.Subset.trans h₁₂ hF) G (Finset.Subset.trans h₁₂ hG) sharp advanced μ hμ A
  exact derivative_parseval _ N m hm hd.1 hd.2 (hK₂ F hF G hG sharp advanced μ hμ A)

end LowEnergy.FullYDynamicCausalJets
