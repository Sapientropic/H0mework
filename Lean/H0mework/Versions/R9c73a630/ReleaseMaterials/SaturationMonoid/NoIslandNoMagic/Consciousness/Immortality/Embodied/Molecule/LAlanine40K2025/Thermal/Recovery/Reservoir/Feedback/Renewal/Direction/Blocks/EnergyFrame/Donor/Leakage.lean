import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Donor.Gap

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Donor
open Propagation.Interface
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def calculatedTopProjector : Matrix Basis Basis ℂ := Spectrum.basisPure calculatedTop

theorem gap_inverse_product : gapInverse*(E-(Preparation.sourceEnergies originalTop : ℂ) • 1) =
    1-calculatedTopProjector := by
  have diagonal : E-(Preparation.sourceEnergies originalTop : ℂ) • 1 =
      Matrix.diagonal (fun i => ((calculatedEnergy i-Preparation.sourceEnergies originalTop : ℝ) : ℂ)) := by
    ext i j
    simp only [E,calculatedEnergy,Matrix.sub_apply,Matrix.smul_apply,Matrix.one_apply,Matrix.diagonal_apply,smul_eq_mul]
    by_cases same : i=j
    · subst j; simp
    · simp [same]
  rw [diagonal,gapInverse,Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases same : i=j
  · subst j
    by_cases top : i=calculatedTop
    · simp [calculatedTopProjector,Spectrum.basisPure,Matrix.diagonal,top]
    · have gap := original_top_gap i top
      have nonzero : ((calculatedEnergy i-Preparation.sourceEnergies originalTop : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (by linarith)
      have nonzeroC : (calculatedEnergy i : ℂ)-(Preparation.sourceEnergies originalTop : ℂ) ≠ 0 := by
        simpa only [Complex.ofReal_sub] using nonzero
      simp [calculatedTopProjector,Spectrum.basisPure,Matrix.diagonal,top,nonzeroC]
  · simp [calculatedTopProjector,Spectrum.basisPure,Matrix.diagonal,same]

theorem original_top_projector_norm : ‖originalTopProjector‖ ≤ 1 := by
  rw [originalTopProjector,Spectrum.basisPure,Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
  intro i
  split_ifs <;> simp

def leakage : Matrix Basis Basis ℂ :=
  (1-calculatedTopProjector)*(originalToCalculated : Matrix Basis Basis ℂ)*originalTopProjector

theorem source_leakage_factor : leakage = gapInverse*
    (E*(originalToCalculated : Matrix Basis Basis ℂ)-
      (originalToCalculated : Matrix Basis Basis ℂ)*Thermal.Source.energyHamiltonian)*originalTopProjector := by
  rw [leakage,← gap_inverse_product]
  simp only [Matrix.mul_assoc]
  rw [← original_projected_intertwining]
  simp only [Matrix.mul_assoc]

theorem actual_source_leakage : ‖leakage‖ ≤ (21/10^11 : ℝ) := by
  rw [source_leakage_factor]
  calc
    _ ≤ (‖gapInverse‖*‖E*(originalToCalculated : Matrix Basis Basis ℂ)-
      (originalToCalculated : Matrix Basis Basis ℂ)*Thermal.Source.energyHamiltonian‖)*‖originalTopProjector‖ :=
      (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
    _ ≤ (10*(21/10^12))*1 := by gcongr; exact gap_inverse_norm; exact actual_intertwining_error; exact original_top_projector_norm
    _ = _ := by norm_num

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Donor
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
