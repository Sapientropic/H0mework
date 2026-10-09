import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Proxy.Correction.Norm

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Proxy.Correction
open LAlanine40K2025.UnifiedOrbitals.Frame
open BasinRefinement SourceFiniteData
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

private theorem complex_add (A B : Matrix Basis Basis ℝ) :
    complexMatrix (A + B) = complexMatrix A + complexMatrix B := by
  ext i j
  simp [complexMatrix]

private theorem complex_sub (A B : Matrix Basis Basis ℝ) :
    complexMatrix (A - B) = complexMatrix A - complexMatrix B := by
  ext i j
  simp [complexMatrix]

private theorem triple_norm (A B C : Matrix Basis Basis ℂ) :
    ‖A * B * C‖ ≤ ‖A‖ * ‖B‖ * ‖C‖ := by
  exact (Matrix.l2_opNorm_mul _ _).trans
    (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul A B) (norm_nonneg _))

theorem raw_D3_complex_operator_bound :
    ‖complexMatrix (trueD3 - recordedD3)‖ ≤
      (392 / 10^11 : ℝ) * ‖complexMatrix d3AO‖ * ‖complexMatrix trueFirst‖ +
        ‖complexMatrix recordedFirst‖ * ‖complexMatrix d3AO‖ * (392 / 10^11 : ℝ) := by
  rw [raw_D3_difference,complex_add]
  simp only [complexMatrix_mul, ← complexMatrix_star]
  have hfirst := first_defect_complex_norm_error
  calc
    ‖star (complexMatrix firstDefect) * complexMatrix d3AO * complexMatrix trueFirst +
        star (complexMatrix recordedFirst) * complexMatrix d3AO * complexMatrix firstDefect‖ ≤
      ‖star (complexMatrix firstDefect) * complexMatrix d3AO * complexMatrix trueFirst‖ +
        ‖star (complexMatrix recordedFirst) * complexMatrix d3AO * complexMatrix firstDefect‖ :=
      norm_add_le _ _
    _ ≤ ‖complexMatrix firstDefect‖ * ‖complexMatrix d3AO‖ *
          ‖complexMatrix trueFirst‖ +
        ‖complexMatrix recordedFirst‖ * ‖complexMatrix d3AO‖ *
          ‖complexMatrix firstDefect‖ := by
      simpa only [norm_star] using
        add_le_add (triple_norm (star (complexMatrix firstDefect))
          (complexMatrix d3AO) (complexMatrix trueFirst))
          (triple_norm (star (complexMatrix recordedFirst))
            (complexMatrix d3AO) (complexMatrix firstDefect))
    _ ≤ _ := by
      gcongr

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Proxy.Correction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
