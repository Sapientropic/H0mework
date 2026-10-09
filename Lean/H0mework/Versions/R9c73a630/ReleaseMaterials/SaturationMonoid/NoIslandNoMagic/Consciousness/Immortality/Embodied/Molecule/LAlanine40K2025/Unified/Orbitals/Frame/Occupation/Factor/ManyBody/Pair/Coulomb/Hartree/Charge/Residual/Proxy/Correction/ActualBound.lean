import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Proxy.Correction.OperatorBound

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

private theorem conjugate_difference (A T : Matrix Basis Basis ℂ) :
    star A * T * A - T = (star A - 1) * T * A + T * (A - 1) := by
  noncomm_ring

private theorem conjugation_difference_norm (A T : Matrix Basis Basis ℂ) (δ : ℝ)
    (h : ‖A - 1‖ ≤ δ) :
    ‖star A * T * A - T‖ ≤ δ * ‖T‖ * (2 + δ) := by
  have hA : ‖A‖ ≤ 1 + δ := by
    calc
      ‖A‖ = ‖(A - 1) + 1‖ := by rw [sub_add_cancel]
      _ ≤ ‖A - 1‖ + ‖(1 : Matrix Basis Basis ℂ)‖ := norm_add_le _ _
      _ ≤ 1 + δ := by simpa only [norm_one, add_comm] using add_le_add_right h 1
  have hstar : ‖star A - 1‖ = ‖A - 1‖ := by
    have hs : star A - 1 = star (A - 1) := by simp only [star_sub, star_one]
    rw [hs, norm_star]
  have δnonneg : 0 ≤ δ := (norm_nonneg _).trans h
  calc
    ‖star A * T * A - T‖ = ‖(star A - 1) * T * A + T * (A - 1)‖ :=
      congrArg norm (conjugate_difference A T)
    _ ≤ ‖(star A - 1) * T * A‖ + ‖T * (A - 1)‖ := norm_add_le _ _
    _ ≤ ‖star A - 1‖ * ‖T‖ * ‖A‖ + ‖T‖ * ‖A - 1‖ :=
      add_le_add (triple_norm _ _ _) (Matrix.l2_opNorm_mul _ _)
    _ ≤ δ * ‖T‖ * (1 + δ) + ‖T‖ * δ := by
      rw [hstar]
      gcongr
    _ = δ * ‖T‖ * (2 + δ) := by ring

theorem actual_D3_complex_operator_bound :
    ‖complexMatrix (normalizedDensityMatrix - recordedD3)‖ ≤
      (392 / 10^9 : ℝ) * ‖complexMatrix trueD3‖ * (2 + 392 / 10^9 : ℝ) +
        ((392 / 10^11 : ℝ) * ‖complexMatrix d3AO‖ * ‖complexMatrix trueFirst‖ +
          ‖complexMatrix recordedFirst‖ * ‖complexMatrix d3AO‖ * (392 / 10^11 : ℝ)) := by
  have hsplit : complexMatrix (normalizedDensityMatrix - recordedD3) =
      (star (complexMatrix actualCorrection) * complexMatrix trueD3 *
        complexMatrix actualCorrection - complexMatrix trueD3) +
        complexMatrix (trueD3 - recordedD3) := by
    rw [actual_recorded_D3_difference,complex_add,← raw_D3_difference]
    rw [complex_sub (actualCorrection.transpose * trueD3 * actualCorrection) trueD3,
      complexMatrix_mul,complexMatrix_mul,← complexMatrix_star]
  rw [hsplit]
  calc
    ‖(star (complexMatrix actualCorrection) * complexMatrix trueD3 *
        complexMatrix actualCorrection - complexMatrix trueD3) +
        complexMatrix (trueD3 - recordedD3)‖ ≤
      ‖star (complexMatrix actualCorrection) * complexMatrix trueD3 *
        complexMatrix actualCorrection - complexMatrix trueD3‖ +
        ‖complexMatrix (trueD3 - recordedD3)‖ := norm_add_le _ _
    _ ≤ _ := add_le_add
      (conjugation_difference_norm _ _ _ correction_complex_norm_error)
      raw_D3_complex_operator_bound

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Proxy.Correction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
