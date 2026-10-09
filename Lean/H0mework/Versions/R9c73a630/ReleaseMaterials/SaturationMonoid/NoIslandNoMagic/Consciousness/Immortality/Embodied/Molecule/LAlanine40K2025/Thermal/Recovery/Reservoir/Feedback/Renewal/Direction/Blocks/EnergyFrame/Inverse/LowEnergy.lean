import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.ExchangeNorm

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
open Propagation.Interface
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
attribute [local irreducible] transformedOriginal E originalToCalculated

theorem original_low_energy : ∃ i : Basis, Preparation.sourceEnergies i < -18 := by
  by_contra missing
  push Not at missing
  have positive : (Thermal.Source.energyHamiltonian+(18 : ℂ) • 1).PosSemidef := by
    have equal : Thermal.Source.energyHamiltonian+(18 : ℂ) • 1 =
        Matrix.diagonal (fun i => ((Preparation.sourceEnergies i+18 : ℝ) : ℂ)) := by
      ext i j
      simp only [Thermal.Source.energyHamiltonian,Matrix.add_apply,Matrix.smul_apply,Matrix.one_apply,Matrix.diagonal_apply,smul_eq_mul]
      split_ifs <;> push_cast <;> ring
    rw [equal]
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    exact_mod_cast (show 0 ≤ Preparation.sourceEnergies i+18 by linarith [missing i])
  have rotated := Quantum.conjugation_posSemidef originalToCalculated _ positive
  have identity : Quantum.conjugation originalToCalculated (Thermal.Source.energyHamiltonian+(18 : ℂ) • 1)=
      transformedOriginal+(18 : ℂ) • 1 := by
    have one : Quantum.conjugation originalToCalculated (1 : Matrix Basis Basis ℂ)=1 :=
      map_one (Unitary.conjStarAlgAut ℂ (Matrix Basis Basis ℂ) originalToCalculated)
    simp only [map_add,map_smul,one,same_source_Hamiltonian]
  rw [identity] at rotated
  have lower := (Complex.nonneg_iff.mp (rotated.diag_nonneg (i := (0 : Basis)))).1
  have error := (Complex.abs_re_le_norm ((transformedOriginal-E) (0 : Basis) 0)).trans
    ((Load.Producer.StrictThermal.matrix_entry_norm_le (transformedOriginal-E) 0 0).trans
      (show ‖transformedOriginal-E‖ ≤ (21/10^12 : ℝ) by unfold transformedOriginal; exact actual_source_diagonal_error))
  have recorded : (E (0 : Basis) 0).re < -18.6 := by
    unfold E
    norm_num [energies]
  simp only [Matrix.sub_apply,Complex.sub_re] at error
  simp only [Matrix.add_apply,Matrix.smul_apply,Matrix.one_apply_eq,smul_eq_mul,mul_one,Complex.add_re] at lower
  norm_num only [Complex.re_ofNat] at lower
  linarith [(abs_le.mp error).2]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
