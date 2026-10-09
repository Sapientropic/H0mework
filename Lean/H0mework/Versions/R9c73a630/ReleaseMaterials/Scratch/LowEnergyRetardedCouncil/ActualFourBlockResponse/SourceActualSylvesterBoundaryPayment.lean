import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualSylvesterCore
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceScalarDoubleEndpoint

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.ActualSylvesterBoundaryPayment
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open ActualSylvesterCore SourceScalarPairedTransport SourceCutoffDilationWard
open scoped BigOperators InnerProductSpace

private theorem forcing_young {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (μ : ℝ) (hμ : 0 < μ) (u v : V) :
    (inner ℂ u v).re ≤ μ*‖u‖^2+‖v‖^2/(4*μ) := by
  have hc := mul_le_mul_of_nonneg_right (re_inner_le_norm (𝕜 := ℂ) u v)
    (show 0 ≤ 4*μ by positivity)
  change (inner ℂ u v).re*(4*μ) ≤ ‖u‖*‖v‖*(4*μ) at hc
  have hs := sq_nonneg (2*μ*‖u‖-‖v‖)
  have he := div_mul_cancel₀ (‖v‖^2) (show 4*μ ≠ 0 by positivity)
  apply (mul_le_mul_iff_right₀ (show 0 < 4*μ by positivity)).mp
  nlinarith only [hc,hs,he]

/-- A single original fixed-source tail pays the exact smoothing forcing before both causes and every F.
The surviving current uses CF on the fixed input, without dropping a moving-input defect. -/
theorem actual_fixed_source_boundary_payment (sharp : Bool) (μ : ℝ) (hμ : 0 < μ)
    (f : QuantumTest) :
    ∀ ε : ℝ,0 < ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ F : Index,∀ advanced : Bool,
      μ*‖embed (sourceLCore advanced sharp F μ m ell f)‖^2 ≤ ε+
        (if advanced then -1 else 1 : ℝ) *
          (sourcePair (sourceLCore advanced sharp F μ m ell f)
            (sourceLCore advanced sharp F μ m ell (compressionCore F f))).im := by
  intro ε hε
  obtain ⟨N,hN⟩ := SourceScalarDoubleEndpoint.actual_full_fixed_tail sharp f
    (Real.sqrt (4*μ*ε)) (Real.sqrt_pos.mpr (by positivity))
  refine ⟨N,fun m hm ell hell F advanced => ?_⟩
  have hd := hN m hm ell hell
  rw [literal_increment_core] at hd
  have hd2 : ‖embed (literalIncrementAction sharp m ell f)‖^2 ≤ 4*μ*ε := by
    have hs := Real.sq_sqrt (show 0 ≤ 4*μ*ε by positivity)
    nlinarith only [hd,hs,Real.sqrt_nonneg (4*μ*ε),norm_nonneg (embed (literalIncrementAction sharp m ell f))]
  have hp : ‖embed (literalIncrementAction sharp m ell f)‖^2/(4*μ) ≤ ε := by
    exact (div_le_iff₀ (by positivity)).mpr (by nlinarith only [hd2])
  have hy := forcing_young μ hμ (embed (sourceLCore advanced sharp F μ m ell f))
    (embed (literalIncrementAction sharp m ell f))
  have hb := actual_boundary_forcing_balance advanced sharp F μ hμ m ell f
  change (sourcePair (sourceLCore advanced sharp F μ m ell f) (literalIncrementAction sharp m ell f)).re ≤ _ at hy
  linarith only [hy,hb,hp]

/-- Only the fixed input is transported to its original H0 jet, on the original source filter. -/
theorem actual_fixed_source_original_boundary_payment (sharp : Bool) (μ : ℝ) (hμ : 0 < μ)
    (f : QuantumTest) :
    ∀ ε : ℝ,0 < ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),∀ advanced : Bool,
      μ*‖embed (sourceLCore advanced sharp F μ m ell f)‖^2 ≤ ε+
        (if advanced then -1 else 1 : ℝ) *
          (sourcePair (sourceLCore advanced sharp F μ m ell f)
            (sourceLCore advanced sharp F μ m ell (diagonalAction f))).im := by
  intro ε hε
  obtain ⟨N,hN⟩ := actual_fixed_source_boundary_payment sharp μ hμ f ε hε
  refine ⟨N,fun m hm ell hell => ?_⟩
  filter_upwards [GaussGradedCompression.eventually_exact (coreEquiv f)] with F hF
  have hc : compressionCore F f = diagonalAction f := by
    apply embed_injective
    have he : embed (compressionCore F f) = GaussGradedCompression.compression F (embed f) :=
      congrArg Subtype.val (coreEquiv.apply_symm_apply _)
    rw [he]
    change GaussGradedCompression.compression F (embed f) =
      embed (diagonalAction (coreEquiv.symm (coreEquiv f))) at hF
    simpa only [coreEquiv.symm_apply_apply] using hF
  intro advanced
  simpa only [hc] using hN m hm ell hell F advanced

end LowEnergy.ActualSylvesterBoundaryPayment
