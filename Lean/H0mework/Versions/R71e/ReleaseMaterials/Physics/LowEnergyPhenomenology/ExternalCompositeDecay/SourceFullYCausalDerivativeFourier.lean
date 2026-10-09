import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceFullYCausalJetIntegrability
import Mathlib.Analysis.Fourier.FourierTransformDeriv
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.FullYDynamicCausalJets
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussUnitaryHistory
open FullYDynamicSource FullYPairedParseval MeasureTheory
open scoped FourierTransform
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] sourceWave embed literalCoreTime

/-- The actual retarded correction generates its frequency powers from
source-paid causal derivatives, including all endpoint cancellations. -/
theorem actual_cofinal_causal_fourier_derivatives(B:Index)(q:QuantumTest)(N:ℕ):
    ∃K₀:Index,B⊆K₀ ∧ ∀F:Index,K₀⊆F → ∀G:Index,K₀⊆G →
      ∀sharp advanced:Bool,∀μ:ℝ,∀_hμ:0<μ,∀A:End,∀m:ℕ,m ≤ N →
      ∀ξ:ℝ,𝓕 (iteratedDeriv m (causalRelativeJet F G sharp q A advanced μ 0)) ξ=
        (2*Real.pi*Complex.I*(ξ:ℂ))^m • 𝓕 (causalRelativeJet F G sharp q A advanced μ 0) ξ := by
  obtain ⟨K₀,hB,hK₀⟩ := actual_cofinal_causal_derivatives_integrable B q N
  refine ⟨K₀,hB,fun F hF G hG sharp advanced μ hμ A m hm ξ=>?_⟩
  have h := hK₀ F hF G hG sharp advanced μ hμ A
  have hi(j:ℕ)(hj:(j:ℕ∞) ≤ (N:ℕ∞)):
      Integrable (iteratedDeriv j (causalRelativeJet F G sharp q A advanced μ 0)) := by
    apply h.2 j
    exact_mod_cast hj
  have hn:(m:ℕ∞) ≤ (N:ℕ∞) := by exact_mod_cast hm
  exact congrFun (Real.fourier_iteratedDeriv (N:=(N:ℕ∞)) h.1 hi hn) ξ

/-- The physical zero-output word reads the very same original source-wave
history; its Fourier derivative law uses the source-generated event. -/
theorem actual_cofinal_original_wave_fourier_derivatives(B:Index)(q:QuantumTest)(N:ℕ):
    ∃K₀:Index,B⊆K₀ ∧ ∀F:Index,K₀⊆F → ∀G:Index,K₀⊆G →
      ∀sharp advanced:Bool,∀μ:ℝ,∀_hμ:0<μ,∀m:ℕ,m ≤ N →
      let u:=fun t:ℝ=>sourceWave F sharp q advanced μ t-sourceWave G sharp q advanced μ t
      ∀ξ:ℝ,𝓕 (iteratedDeriv m u) ξ=(2*Real.pi*Complex.I*(ξ:ℂ))^m • 𝓕 u ξ := by
  obtain ⟨K₀,hB,hK₀⟩ := actual_cofinal_causal_fourier_derivatives B q N
  refine ⟨K₀,hB,fun F hF G hG sharp advanced μ hμ m hm=>?_⟩
  have h := hK₀ F hF G hG sharp advanced μ hμ (1:End) m hm
  rw [actual_causal_relative_wave] at h
  exact h

end LowEnergy.FullYDynamicCausalJets
