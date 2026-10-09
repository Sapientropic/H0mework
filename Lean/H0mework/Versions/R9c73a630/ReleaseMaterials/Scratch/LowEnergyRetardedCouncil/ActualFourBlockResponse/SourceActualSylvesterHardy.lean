import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualTwoResolventSylvester
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualVectorJointTail

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.ActualSylvesterHardy
open GaussCoreHilbert GaussDiagonalHistory GaussUnitaryHistory
open FullYSourceResolventGraphSplice SourceResolventBandLimit SourceHardyRetardedTail
open ActualTwoResolventSylvester ActualVectorJointCost MeasureTheory Filter
open scoped InnerProductSpace Topology

/-- The original Hardy price pays both positive Sylvester terms together. -/
theorem actual_hardy_sylvester_price (advanced sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0 < μ) (g : H) :
    Real.pi/μ * ‖sourceL advanced F μ
        (GaussGradedCompression.compression F * cutoffSolver sharp m ell) g‖^2 +
      (∫w : ℝ,‖sourceL advanced F μ
        (GaussGradedCompression.compression F * cutoffSolver sharp m ell)
          (finiteResolvent F (causalFrequency advanced μ w) g)‖^2) =
      hardyPrice advanced sharp m ell F μ g := by
  have h := actual_two_resolvent_price advanced F μ hμ
    (GaussGradedCompression.compression F * cutoffSolver sharp m ell) g
  rw [actual_vector_causal_energy F advanced μ hμ] at h
  exact h.symm

/-- The paid source jet supplies one cutoff tail before both causal orientations. -/
theorem actual_hardy_sylvester_causal_tail (sharp : Bool) (μ : ℝ) (hμ : 0 < μ)
    (g : diagonal.domain) :
    ∀ε : ℝ,0 < ε → ∃N : ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),∀advanced : Bool,
      Real.pi/μ * ‖sourceL advanced F μ
          (GaussGradedCompression.compression F * cutoffSolver sharp m ell) (g : H)‖^2 +
        (∫w : ℝ,‖sourceL advanced F μ
          (GaussGradedCompression.compression F * cutoffSolver sharp m ell)
            (finiteResolvent F (causalFrequency advanced μ w) (g : H))‖^2) ≤ ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := actual_hardy_price_causal_tail sharp μ hμ g ε hε
  refine ⟨N,fun m hm ell hell => ?_⟩
  filter_upwards [hN m hm ell hell] with F hF
  intro advanced
  rw [actual_hardy_sylvester_price advanced sharp m ell F μ hμ]
  exact hF advanced

/-- Both prices descend from the same internally paid tail event. -/
theorem actual_hardy_sylvester_components_causal_tail (sharp : Bool) (μ : ℝ) (hμ : 0 < μ)
    (g : diagonal.domain) :
    ∀ε : ℝ,0 < ε → ∃N : ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),∀advanced : Bool,
      Real.pi/μ * ‖sourceL advanced F μ
          (GaussGradedCompression.compression F * cutoffSolver sharp m ell) (g : H)‖^2 ≤ ε ∧
        (∫w : ℝ,‖sourceL advanced F μ
          (GaussGradedCompression.compression F * cutoffSolver sharp m ell)
            (finiteResolvent F (causalFrequency advanced μ w) (g : H))‖^2) ≤ ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := actual_hardy_sylvester_causal_tail sharp μ hμ g ε hε
  refine ⟨N,fun m hm ell hell => ?_⟩
  filter_upwards [hN m hm ell hell] with F hF
  intro advanced
  have hp : 0 ≤ Real.pi/μ * ‖sourceL advanced F μ
      (GaussGradedCompression.compression F * cutoffSolver sharp m ell) (g : H)‖^2 :=
    mul_nonneg (div_nonneg Real.pi_pos.le hμ.le) (sq_nonneg _)
  have hi : 0 ≤ (∫w : ℝ,‖sourceL advanced F μ
      (GaussGradedCompression.compression F * cutoffSolver sharp m ell)
        (finiteResolvent F (causalFrequency advanced μ w) (g : H))‖^2) :=
    integral_nonneg (fun _ => sq_nonneg _)
  have h := hF advanced
  constructor <;> linarith

end LowEnergy.ActualSylvesterHardy
