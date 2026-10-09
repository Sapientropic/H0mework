import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Data
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Upper.Assembly

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
open Spectral Propagation.Interface

theorem original_row_91 : frameRows91 = originalRows[91]! := by rfl

theorem original_column_91 : frameColumns91 = originalRows.map (fun row => row[91]!) := by rfl

theorem original_hamiltonian_91 (j : Basis) : hamiltonianRows91[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (91 : Basis) j := by
  have previous := Upper.source_entries (91 : Basis) j
  have restore : hamiltonianRows91[j.val]! = (if j=(91 : Basis) then 3150000000000000 else 0)-Upper.numerator (91 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_91 : appliedColumns91 = hamiltonianRows.map (fun row => Rows.dot row frameColumns91) := by rfl

theorem gram_row_91 : gramRows91 = frameColumns.map (Rows.dot frameColumns91) := by rfl

theorem eigen_residual_91 : residualColumns91 = (appliedColumns91.zip frameColumns91).map (fun pair => pair.1-pair.2*energies[91]!) := by rfl

theorem gram_error_91 : ((gramRows91.zip (List.ofFn (fun j : Fin 98 => if j=(91 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_91 : (residualColumns91.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_91 : hamiltonianRows91.length = 98 := by rfl
theorem frameRows_length_91 : frameRows91.length = 98 := by rfl
theorem frameColumns_length_91 : frameColumns91.length = 98 := by rfl
theorem appliedColumns_length_91 : appliedColumns91.length = 98 := by rfl
theorem gramRows_length_91 : gramRows91.length = 98 := by rfl
theorem residualColumns_length_91 : residualColumns91.length = 98 := by rfl

theorem original_row_92 : frameRows92 = originalRows[92]! := by rfl

theorem original_column_92 : frameColumns92 = originalRows.map (fun row => row[92]!) := by rfl

theorem original_hamiltonian_92 (j : Basis) : hamiltonianRows92[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (92 : Basis) j := by
  have previous := Upper.source_entries (92 : Basis) j
  have restore : hamiltonianRows92[j.val]! = (if j=(92 : Basis) then 3150000000000000 else 0)-Upper.numerator (92 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_92 : appliedColumns92 = hamiltonianRows.map (fun row => Rows.dot row frameColumns92) := by rfl

theorem gram_row_92 : gramRows92 = frameColumns.map (Rows.dot frameColumns92) := by rfl

theorem eigen_residual_92 : residualColumns92 = (appliedColumns92.zip frameColumns92).map (fun pair => pair.1-pair.2*energies[92]!) := by rfl

theorem gram_error_92 : ((gramRows92.zip (List.ofFn (fun j : Fin 98 => if j=(92 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_92 : (residualColumns92.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_92 : hamiltonianRows92.length = 98 := by rfl
theorem frameRows_length_92 : frameRows92.length = 98 := by rfl
theorem frameColumns_length_92 : frameColumns92.length = 98 := by rfl
theorem appliedColumns_length_92 : appliedColumns92.length = 98 := by rfl
theorem gramRows_length_92 : gramRows92.length = 98 := by rfl
theorem residualColumns_length_92 : residualColumns92.length = 98 := by rfl

theorem original_row_93 : frameRows93 = originalRows[93]! := by rfl

theorem original_column_93 : frameColumns93 = originalRows.map (fun row => row[93]!) := by rfl

theorem original_hamiltonian_93 (j : Basis) : hamiltonianRows93[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (93 : Basis) j := by
  have previous := Upper.source_entries (93 : Basis) j
  have restore : hamiltonianRows93[j.val]! = (if j=(93 : Basis) then 3150000000000000 else 0)-Upper.numerator (93 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_93 : appliedColumns93 = hamiltonianRows.map (fun row => Rows.dot row frameColumns93) := by rfl

theorem gram_row_93 : gramRows93 = frameColumns.map (Rows.dot frameColumns93) := by rfl

theorem eigen_residual_93 : residualColumns93 = (appliedColumns93.zip frameColumns93).map (fun pair => pair.1-pair.2*energies[93]!) := by rfl

theorem gram_error_93 : ((gramRows93.zip (List.ofFn (fun j : Fin 98 => if j=(93 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_93 : (residualColumns93.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_93 : hamiltonianRows93.length = 98 := by rfl
theorem frameRows_length_93 : frameRows93.length = 98 := by rfl
theorem frameColumns_length_93 : frameColumns93.length = 98 := by rfl
theorem appliedColumns_length_93 : appliedColumns93.length = 98 := by rfl
theorem gramRows_length_93 : gramRows93.length = 98 := by rfl
theorem residualColumns_length_93 : residualColumns93.length = 98 := by rfl

theorem original_row_94 : frameRows94 = originalRows[94]! := by rfl

theorem original_column_94 : frameColumns94 = originalRows.map (fun row => row[94]!) := by rfl

theorem original_hamiltonian_94 (j : Basis) : hamiltonianRows94[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (94 : Basis) j := by
  have previous := Upper.source_entries (94 : Basis) j
  have restore : hamiltonianRows94[j.val]! = (if j=(94 : Basis) then 3150000000000000 else 0)-Upper.numerator (94 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_94 : appliedColumns94 = hamiltonianRows.map (fun row => Rows.dot row frameColumns94) := by rfl

theorem gram_row_94 : gramRows94 = frameColumns.map (Rows.dot frameColumns94) := by rfl

theorem eigen_residual_94 : residualColumns94 = (appliedColumns94.zip frameColumns94).map (fun pair => pair.1-pair.2*energies[94]!) := by rfl

theorem gram_error_94 : ((gramRows94.zip (List.ofFn (fun j : Fin 98 => if j=(94 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_94 : (residualColumns94.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_94 : hamiltonianRows94.length = 98 := by rfl
theorem frameRows_length_94 : frameRows94.length = 98 := by rfl
theorem frameColumns_length_94 : frameColumns94.length = 98 := by rfl
theorem appliedColumns_length_94 : appliedColumns94.length = 98 := by rfl
theorem gramRows_length_94 : gramRows94.length = 98 := by rfl
theorem residualColumns_length_94 : residualColumns94.length = 98 := by rfl

theorem original_row_95 : frameRows95 = originalRows[95]! := by rfl

theorem original_column_95 : frameColumns95 = originalRows.map (fun row => row[95]!) := by rfl

theorem original_hamiltonian_95 (j : Basis) : hamiltonianRows95[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (95 : Basis) j := by
  have previous := Upper.source_entries (95 : Basis) j
  have restore : hamiltonianRows95[j.val]! = (if j=(95 : Basis) then 3150000000000000 else 0)-Upper.numerator (95 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_95 : appliedColumns95 = hamiltonianRows.map (fun row => Rows.dot row frameColumns95) := by rfl

theorem gram_row_95 : gramRows95 = frameColumns.map (Rows.dot frameColumns95) := by rfl

theorem eigen_residual_95 : residualColumns95 = (appliedColumns95.zip frameColumns95).map (fun pair => pair.1-pair.2*energies[95]!) := by rfl

theorem gram_error_95 : ((gramRows95.zip (List.ofFn (fun j : Fin 98 => if j=(95 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_95 : (residualColumns95.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_95 : hamiltonianRows95.length = 98 := by rfl
theorem frameRows_length_95 : frameRows95.length = 98 := by rfl
theorem frameColumns_length_95 : frameColumns95.length = 98 := by rfl
theorem appliedColumns_length_95 : appliedColumns95.length = 98 := by rfl
theorem gramRows_length_95 : gramRows95.length = 98 := by rfl
theorem residualColumns_length_95 : residualColumns95.length = 98 := by rfl

theorem original_row_96 : frameRows96 = originalRows[96]! := by rfl

theorem original_column_96 : frameColumns96 = originalRows.map (fun row => row[96]!) := by rfl

theorem original_hamiltonian_96 (j : Basis) : hamiltonianRows96[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (96 : Basis) j := by
  have previous := Upper.source_entries (96 : Basis) j
  have restore : hamiltonianRows96[j.val]! = (if j=(96 : Basis) then 3150000000000000 else 0)-Upper.numerator (96 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_96 : appliedColumns96 = hamiltonianRows.map (fun row => Rows.dot row frameColumns96) := by rfl

theorem gram_row_96 : gramRows96 = frameColumns.map (Rows.dot frameColumns96) := by rfl

theorem eigen_residual_96 : residualColumns96 = (appliedColumns96.zip frameColumns96).map (fun pair => pair.1-pair.2*energies[96]!) := by rfl

theorem gram_error_96 : ((gramRows96.zip (List.ofFn (fun j : Fin 98 => if j=(96 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_96 : (residualColumns96.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_96 : hamiltonianRows96.length = 98 := by rfl
theorem frameRows_length_96 : frameRows96.length = 98 := by rfl
theorem frameColumns_length_96 : frameColumns96.length = 98 := by rfl
theorem appliedColumns_length_96 : appliedColumns96.length = 98 := by rfl
theorem gramRows_length_96 : gramRows96.length = 98 := by rfl
theorem residualColumns_length_96 : residualColumns96.length = 98 := by rfl

theorem original_row_97 : frameRows97 = originalRows[97]! := by rfl

theorem original_column_97 : frameColumns97 = originalRows.map (fun row => row[97]!) := by rfl

theorem original_hamiltonian_97 (j : Basis) : hamiltonianRows97[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (97 : Basis) j := by
  have previous := Upper.source_entries (97 : Basis) j
  have restore : hamiltonianRows97[j.val]! = (if j=(97 : Basis) then 3150000000000000 else 0)-Upper.numerator (97 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_97 : appliedColumns97 = hamiltonianRows.map (fun row => Rows.dot row frameColumns97) := by rfl

theorem gram_row_97 : gramRows97 = frameColumns.map (Rows.dot frameColumns97) := by rfl

theorem eigen_residual_97 : residualColumns97 = (appliedColumns97.zip frameColumns97).map (fun pair => pair.1-pair.2*energies[97]!) := by rfl

theorem gram_error_97 : ((gramRows97.zip (List.ofFn (fun j : Fin 98 => if j=(97 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_97 : (residualColumns97.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_97 : hamiltonianRows97.length = 98 := by rfl
theorem frameRows_length_97 : frameRows97.length = 98 := by rfl
theorem frameColumns_length_97 : frameColumns97.length = 98 := by rfl
theorem appliedColumns_length_97 : appliedColumns97.length = 98 := by rfl
theorem gramRows_length_97 : gramRows97.length = 98 := by rfl
theorem residualColumns_length_97 : residualColumns97.length = 98 := by rfl

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
