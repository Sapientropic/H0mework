import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Data
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Upper.Assembly

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
open Spectral Propagation.Interface

theorem original_row_63 : frameRows63 = originalRows[63]! := by rfl

theorem original_column_63 : frameColumns63 = originalRows.map (fun row => row[63]!) := by rfl

theorem original_hamiltonian_63 (j : Basis) : hamiltonianRows63[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (63 : Basis) j := by
  have previous := Upper.source_entries (63 : Basis) j
  have restore : hamiltonianRows63[j.val]! = (if j=(63 : Basis) then 3150000000000000 else 0)-Upper.numerator (63 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_63 : appliedColumns63 = hamiltonianRows.map (fun row => Rows.dot row frameColumns63) := by rfl

theorem gram_row_63 : gramRows63 = frameColumns.map (Rows.dot frameColumns63) := by rfl

theorem eigen_residual_63 : residualColumns63 = (appliedColumns63.zip frameColumns63).map (fun pair => pair.1-pair.2*energies[63]!) := by rfl

theorem gram_error_63 : ((gramRows63.zip (List.ofFn (fun j : Fin 98 => if j=(63 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_63 : (residualColumns63.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_63 : hamiltonianRows63.length = 98 := by rfl
theorem frameRows_length_63 : frameRows63.length = 98 := by rfl
theorem frameColumns_length_63 : frameColumns63.length = 98 := by rfl
theorem appliedColumns_length_63 : appliedColumns63.length = 98 := by rfl
theorem gramRows_length_63 : gramRows63.length = 98 := by rfl
theorem residualColumns_length_63 : residualColumns63.length = 98 := by rfl

theorem original_row_64 : frameRows64 = originalRows[64]! := by rfl

theorem original_column_64 : frameColumns64 = originalRows.map (fun row => row[64]!) := by rfl

theorem original_hamiltonian_64 (j : Basis) : hamiltonianRows64[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (64 : Basis) j := by
  have previous := Upper.source_entries (64 : Basis) j
  have restore : hamiltonianRows64[j.val]! = (if j=(64 : Basis) then 3150000000000000 else 0)-Upper.numerator (64 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_64 : appliedColumns64 = hamiltonianRows.map (fun row => Rows.dot row frameColumns64) := by rfl

theorem gram_row_64 : gramRows64 = frameColumns.map (Rows.dot frameColumns64) := by rfl

theorem eigen_residual_64 : residualColumns64 = (appliedColumns64.zip frameColumns64).map (fun pair => pair.1-pair.2*energies[64]!) := by rfl

theorem gram_error_64 : ((gramRows64.zip (List.ofFn (fun j : Fin 98 => if j=(64 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_64 : (residualColumns64.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_64 : hamiltonianRows64.length = 98 := by rfl
theorem frameRows_length_64 : frameRows64.length = 98 := by rfl
theorem frameColumns_length_64 : frameColumns64.length = 98 := by rfl
theorem appliedColumns_length_64 : appliedColumns64.length = 98 := by rfl
theorem gramRows_length_64 : gramRows64.length = 98 := by rfl
theorem residualColumns_length_64 : residualColumns64.length = 98 := by rfl

theorem original_row_65 : frameRows65 = originalRows[65]! := by rfl

theorem original_column_65 : frameColumns65 = originalRows.map (fun row => row[65]!) := by rfl

theorem original_hamiltonian_65 (j : Basis) : hamiltonianRows65[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (65 : Basis) j := by
  have previous := Upper.source_entries (65 : Basis) j
  have restore : hamiltonianRows65[j.val]! = (if j=(65 : Basis) then 3150000000000000 else 0)-Upper.numerator (65 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_65 : appliedColumns65 = hamiltonianRows.map (fun row => Rows.dot row frameColumns65) := by rfl

theorem gram_row_65 : gramRows65 = frameColumns.map (Rows.dot frameColumns65) := by rfl

theorem eigen_residual_65 : residualColumns65 = (appliedColumns65.zip frameColumns65).map (fun pair => pair.1-pair.2*energies[65]!) := by rfl

theorem gram_error_65 : ((gramRows65.zip (List.ofFn (fun j : Fin 98 => if j=(65 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_65 : (residualColumns65.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_65 : hamiltonianRows65.length = 98 := by rfl
theorem frameRows_length_65 : frameRows65.length = 98 := by rfl
theorem frameColumns_length_65 : frameColumns65.length = 98 := by rfl
theorem appliedColumns_length_65 : appliedColumns65.length = 98 := by rfl
theorem gramRows_length_65 : gramRows65.length = 98 := by rfl
theorem residualColumns_length_65 : residualColumns65.length = 98 := by rfl

theorem original_row_66 : frameRows66 = originalRows[66]! := by rfl

theorem original_column_66 : frameColumns66 = originalRows.map (fun row => row[66]!) := by rfl

theorem original_hamiltonian_66 (j : Basis) : hamiltonianRows66[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (66 : Basis) j := by
  have previous := Upper.source_entries (66 : Basis) j
  have restore : hamiltonianRows66[j.val]! = (if j=(66 : Basis) then 3150000000000000 else 0)-Upper.numerator (66 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_66 : appliedColumns66 = hamiltonianRows.map (fun row => Rows.dot row frameColumns66) := by rfl

theorem gram_row_66 : gramRows66 = frameColumns.map (Rows.dot frameColumns66) := by rfl

theorem eigen_residual_66 : residualColumns66 = (appliedColumns66.zip frameColumns66).map (fun pair => pair.1-pair.2*energies[66]!) := by rfl

theorem gram_error_66 : ((gramRows66.zip (List.ofFn (fun j : Fin 98 => if j=(66 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_66 : (residualColumns66.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_66 : hamiltonianRows66.length = 98 := by rfl
theorem frameRows_length_66 : frameRows66.length = 98 := by rfl
theorem frameColumns_length_66 : frameColumns66.length = 98 := by rfl
theorem appliedColumns_length_66 : appliedColumns66.length = 98 := by rfl
theorem gramRows_length_66 : gramRows66.length = 98 := by rfl
theorem residualColumns_length_66 : residualColumns66.length = 98 := by rfl

theorem original_row_67 : frameRows67 = originalRows[67]! := by rfl

theorem original_column_67 : frameColumns67 = originalRows.map (fun row => row[67]!) := by rfl

theorem original_hamiltonian_67 (j : Basis) : hamiltonianRows67[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (67 : Basis) j := by
  have previous := Upper.source_entries (67 : Basis) j
  have restore : hamiltonianRows67[j.val]! = (if j=(67 : Basis) then 3150000000000000 else 0)-Upper.numerator (67 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_67 : appliedColumns67 = hamiltonianRows.map (fun row => Rows.dot row frameColumns67) := by rfl

theorem gram_row_67 : gramRows67 = frameColumns.map (Rows.dot frameColumns67) := by rfl

theorem eigen_residual_67 : residualColumns67 = (appliedColumns67.zip frameColumns67).map (fun pair => pair.1-pair.2*energies[67]!) := by rfl

theorem gram_error_67 : ((gramRows67.zip (List.ofFn (fun j : Fin 98 => if j=(67 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_67 : (residualColumns67.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_67 : hamiltonianRows67.length = 98 := by rfl
theorem frameRows_length_67 : frameRows67.length = 98 := by rfl
theorem frameColumns_length_67 : frameColumns67.length = 98 := by rfl
theorem appliedColumns_length_67 : appliedColumns67.length = 98 := by rfl
theorem gramRows_length_67 : gramRows67.length = 98 := by rfl
theorem residualColumns_length_67 : residualColumns67.length = 98 := by rfl

theorem original_row_68 : frameRows68 = originalRows[68]! := by rfl

theorem original_column_68 : frameColumns68 = originalRows.map (fun row => row[68]!) := by rfl

theorem original_hamiltonian_68 (j : Basis) : hamiltonianRows68[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (68 : Basis) j := by
  have previous := Upper.source_entries (68 : Basis) j
  have restore : hamiltonianRows68[j.val]! = (if j=(68 : Basis) then 3150000000000000 else 0)-Upper.numerator (68 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_68 : appliedColumns68 = hamiltonianRows.map (fun row => Rows.dot row frameColumns68) := by rfl

theorem gram_row_68 : gramRows68 = frameColumns.map (Rows.dot frameColumns68) := by rfl

theorem eigen_residual_68 : residualColumns68 = (appliedColumns68.zip frameColumns68).map (fun pair => pair.1-pair.2*energies[68]!) := by rfl

theorem gram_error_68 : ((gramRows68.zip (List.ofFn (fun j : Fin 98 => if j=(68 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_68 : (residualColumns68.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_68 : hamiltonianRows68.length = 98 := by rfl
theorem frameRows_length_68 : frameRows68.length = 98 := by rfl
theorem frameColumns_length_68 : frameColumns68.length = 98 := by rfl
theorem appliedColumns_length_68 : appliedColumns68.length = 98 := by rfl
theorem gramRows_length_68 : gramRows68.length = 98 := by rfl
theorem residualColumns_length_68 : residualColumns68.length = 98 := by rfl

theorem original_row_69 : frameRows69 = originalRows[69]! := by rfl

theorem original_column_69 : frameColumns69 = originalRows.map (fun row => row[69]!) := by rfl

theorem original_hamiltonian_69 (j : Basis) : hamiltonianRows69[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (69 : Basis) j := by
  have previous := Upper.source_entries (69 : Basis) j
  have restore : hamiltonianRows69[j.val]! = (if j=(69 : Basis) then 3150000000000000 else 0)-Upper.numerator (69 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_69 : appliedColumns69 = hamiltonianRows.map (fun row => Rows.dot row frameColumns69) := by rfl

theorem gram_row_69 : gramRows69 = frameColumns.map (Rows.dot frameColumns69) := by rfl

theorem eigen_residual_69 : residualColumns69 = (appliedColumns69.zip frameColumns69).map (fun pair => pair.1-pair.2*energies[69]!) := by rfl

theorem gram_error_69 : ((gramRows69.zip (List.ofFn (fun j : Fin 98 => if j=(69 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_69 : (residualColumns69.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_69 : hamiltonianRows69.length = 98 := by rfl
theorem frameRows_length_69 : frameRows69.length = 98 := by rfl
theorem frameColumns_length_69 : frameColumns69.length = 98 := by rfl
theorem appliedColumns_length_69 : appliedColumns69.length = 98 := by rfl
theorem gramRows_length_69 : gramRows69.length = 98 := by rfl
theorem residualColumns_length_69 : residualColumns69.length = 98 := by rfl

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
