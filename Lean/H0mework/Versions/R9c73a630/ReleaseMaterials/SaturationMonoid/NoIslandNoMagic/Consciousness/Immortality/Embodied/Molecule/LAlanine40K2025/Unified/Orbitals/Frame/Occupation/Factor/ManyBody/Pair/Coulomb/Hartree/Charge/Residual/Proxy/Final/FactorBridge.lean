import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Proxy.Correction.Runtime.Consumers

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Proxy.Final
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor
open BasinRefinement SourceFiniteData
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

private theorem matrix_entry_norm_le (A : Matrix Basis Basis ℂ) (i j : Basis) :
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

theorem original_gamma_real_entry (i j : Basis) :
    (rawGamma i j).re =
      (Reentry.Source.targetRealNumerator i j : ℝ) / (gammaScale : ℝ) := by
  rw [raw_gamma_entry]
  simp

theorem original_gamma_projector_entry (i j : Basis) :
    |(rawGamma i j).re - 2 * (projector24 i j).re| < (1 / (2 * 10^9) : ℝ) := by
  have bound : ‖rawGamma - (2 : ℂ) • projector24‖ < (1 / (2 * 10^9) : ℝ) :=
    source_projection_error.trans_lt (by
      norm_num [gammaEntryBound,gammaScale,gramEntryBound,factorScale])
  have entry := (Complex.abs_re_le_norm ((rawGamma - (2 : ℂ) • projector24) i j)).trans
    (matrix_entry_norm_le _ i j)
  have realPart : ((rawGamma - (2 : ℂ) • projector24) i j).re =
      (rawGamma i j).re - 2 * (projector24 i j).re := by
    simp [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  rw [realPart] at entry
  exact entry.trans_lt bound

theorem proxy_projector_entry (i j : Basis) (value : ℝ)
    (registered : |value - (rawGamma i j).re| < (1 / 10^12 : ℝ)) :
    |value - 2 * (projector24 i j).re| < (1 / 10^9 : ℝ) := by
  have parent := original_gamma_projector_entry i j
  have triangle := abs_add_le (value - (rawGamma i j).re)
    ((rawGamma i j).re - 2 * (projector24 i j).re)
  have identity : value - 2 * (projector24 i j).re =
      (value - (rawGamma i j).re) +
        ((rawGamma i j).re - 2 * (projector24 i j).re) := by ring
  rw [identity]
  linarith

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Proxy.Final
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
