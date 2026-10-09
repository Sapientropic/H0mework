import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.Spectral.Residual

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.Spectral
open LAlanine40K2025.UnifiedOrbitals.Frame
open BasinRefinement SourceFiniteData
open scoped Matrix Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
attribute [local irreducible] Occupation.gamma Factor.projector24

private theorem entry_norm_le (A : Matrix Basis Basis ℂ) (i j : Basis) :
    ‖A i j‖ ≤ ‖A‖ := by
  let e : EuclideanSpace ℂ Basis := PiLp.single 2 j 1
  let T := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Basis) A
  have entry : (T e).ofLp i = A i j := by
    change (A *ᵥ Pi.single j 1) i = A i j
    simp only [Matrix.mulVec_single_one,Matrix.col_apply]
  calc
    _ = ‖(T e).ofLp i‖ := congrArg norm entry.symm
    _ ≤ ‖T e‖ := PiLp.norm_apply_le _ _
    _ ≤ ‖T‖ * ‖e‖ := T.le_opNorm e
    _ = ‖A‖ := by simp only [e,PiLp.norm_single,norm_one,mul_one]; rfl

private theorem trace_norm_le (A : Matrix Basis Basis ℂ) :
    ‖A.trace‖ ≤ 98 * ‖A‖ := by
  rw [Matrix.trace]
  calc
    ‖∑ i : Basis, A i i‖ ≤ ∑ i : Basis, ‖A i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Basis, ‖A‖ := Finset.sum_le_sum (fun i _ => entry_norm_le A i i)
    _ = 98 * ‖A‖ := by norm_num [Fintype.card_fin]

private theorem two_projector_trace :
    ((2 : ℂ) • projector24).trace = (48 : ℂ) := by
  rw [Matrix.trace_smul,projector24_trace]
  norm_num

private theorem gamma_trace_near_48 :
    ‖Occupation.gamma.trace - (48 : ℂ)‖ < (98 / 10^5 : ℝ) := by
  have h := trace_norm_le (Occupation.gamma - (2 : ℂ) • projector24)
  rw [Matrix.trace_sub,two_projector_trace] at h
  have gap := actual_U_gamma_projection_error
  nlinarith

private theorem residual_trace_small :
    ‖Occupation.residual.trace‖ < (98 / 1000 : ℝ) := by
  have h := trace_norm_le Occupation.residual
  have gap := actual_spectral_residual_small
  nlinarith

theorem actual_occupied_count : Occupation.occupiedCount = 24 := by
  have traceAccount := Occupation.gamma_trace_account
  have difference :
      (2 : ℂ) * (Occupation.occupiedCount : ℂ) - 48 =
        (Occupation.gamma.trace - 48) - Occupation.residual.trace := by
    rw [traceAccount]
    ring
  have integerGap :
      ‖(2 : ℂ) * (Occupation.occupiedCount : ℂ) - 48‖ < 1 := by
    rw [difference]
    have triangle := norm_sub_le (Occupation.gamma.trace - (48 : ℂ))
      Occupation.residual.trace
    linarith [gamma_trace_near_48,residual_trace_small]
  have realGap : |(2 : ℝ) * (Occupation.occupiedCount : ℝ) - 48| < 1 := by
    convert integerGap using 1
    norm_cast
  rcases abs_lt.mp realGap with ⟨lower,upper⟩
  have atLeast : 47 < 2 * Occupation.occupiedCount := by exact_mod_cast (show (47 : ℝ) < 2 * Occupation.occupiedCount by linarith)
  have atMost : 2 * Occupation.occupiedCount < 49 := by exact_mod_cast (show (2 : ℝ) * Occupation.occupiedCount < 49 by linarith)
  omega

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.Spectral
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
