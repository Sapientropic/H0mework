import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Donor.Intertwining

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Donor
open Propagation.Interface
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def calculatedTop : Basis := 97
def calculatedEnergy (i : Basis) : ℝ := (energies[i.val]! : ℝ)/10^15

theorem recorded_non_top (i : Fin 97) : energies[i.val]! < 3*10^15 := by
  fin_cases i <;> decide +kernel

theorem calculated_non_top (i : Basis) (different : i ≠ calculatedTop) : calculatedEnergy i < 3 := by
  have range : i.val < 97 := by
    have last : i.val ≠ 97 := by intro same; exact different (Fin.ext same)
    omega
  have integer := recorded_non_top ⟨i.val,range⟩
  have realBound : (energies[i.val]! : ℝ) < 3*10^15 := by exact_mod_cast integer
  unfold calculatedEnergy
  exact (div_lt_iff₀ (by positivity : (0 : ℝ) < 10^15)).mpr (by nlinarith)

theorem original_top_gap (i : Basis) (different : i ≠ calculatedTop) :
    (1/10 : ℝ) < Preparation.sourceEnergies originalTop-calculatedEnergy i := by
  have lower := Spectral.Producer.source_top_lower
  change (31/10 : ℝ) < Preparation.sourceEnergies originalTop at lower
  linarith [calculated_non_top i different]

def gapInverse : Matrix Basis Basis ℂ := Matrix.diagonal (fun i =>
  if i=calculatedTop then 0 else ((calculatedEnergy i-Preparation.sourceEnergies originalTop : ℝ) : ℂ)⁻¹)

theorem gap_inverse_norm : ‖gapInverse‖ ≤ 10 := by
  rw [gapInverse,Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
  intro i
  by_cases same : i=calculatedTop
  · simp [same]
  · simp only [if_neg same,norm_inv,Complex.norm_real,Real.norm_eq_abs]
    have gap := original_top_gap i same
    rw [abs_of_neg (by linarith : calculatedEnergy i-Preparation.sourceEnergies originalTop < 0)]
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (by linarith : 0 < -(calculatedEnergy i-Preparation.sourceEnergies originalTop))).mpr
    linarith

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Donor
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
