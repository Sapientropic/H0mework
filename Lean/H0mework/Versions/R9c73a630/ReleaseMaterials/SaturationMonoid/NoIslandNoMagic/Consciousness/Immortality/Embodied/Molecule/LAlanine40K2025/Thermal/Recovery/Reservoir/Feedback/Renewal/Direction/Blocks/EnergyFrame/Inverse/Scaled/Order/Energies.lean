import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Order.Slopes

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Order
open Propagation.Interface
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

theorem source_energy_increasing : StrictMono Donor.calculatedEnergy := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  have source := energy_gap i
  have strict : energies[i.val]! < energies[i.val+1]! := by linarith
  change (energies[i.val]! : ℝ)/10^15 < (energies[i.val+1]! : ℝ)/10^15
  exact div_lt_div_of_pos_right (by exact_mod_cast strict) (by norm_num)

theorem ordered_source_limits (a b : Basis) (ordered : a < b) :
    Donor.calculatedEnergy 0 ≤ Donor.calculatedEnergy a ∧ Donor.calculatedEnergy 1 ≤ Donor.calculatedEnergy b ∧ Donor.calculatedEnergy a ≤ Donor.calculatedEnergy 96 ∧ Donor.calculatedEnergy b ≤ Donor.calculatedEnergy 97 := by
  have av := a.isLt
  have bv := b.isLt
  have order : a.val < b.val := ordered
  have ma : (0 : Basis) ≤ a := Fin.zero_le a
  have mb : (1 : Basis) ≤ b := by change 1 ≤ b.val; omega
  have ua : a ≤ (96 : Basis) := by change a.val ≤ 96; omega
  have ub : b ≤ (97 : Basis) := by change b.val ≤ 97; omega
  exact ⟨source_energy_increasing.monotone ma,source_energy_increasing.monotone mb,
    source_energy_increasing.monotone ua,source_energy_increasing.monotone ub⟩

theorem all_source_packed_envelope (a b : Basis) (ordered : a < b) :
    packedHpc (Donor.calculatedEnergy 0) (Donor.calculatedEnergy 1) ≤ packedHpc (Donor.calculatedEnergy a) (Donor.calculatedEnergy b) ∧
    packedHpc (Donor.calculatedEnergy a) (Donor.calculatedEnergy b) ≤ packedHpc (Donor.calculatedEnergy 96) (Donor.calculatedEnergy 97) := by
  have bounds := ordered_source_limits a b ordered
  exact ⟨packed_monotone _ _ _ _ bounds.1 bounds.2.1,packed_monotone _ _ _ _ bounds.2.2.1 bounds.2.2.2⟩

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Order
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
