import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Data
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Upper.Assembly

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
open Spectral Propagation.Interface

theorem original_row_21 : frameRows21 = originalRows[21]! := by rfl

theorem original_column_21 : frameColumns21 = originalRows.map (fun row => row[21]!) := by rfl

theorem original_hamiltonian_21 (j : Basis) : hamiltonianRows21[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (21 : Basis) j := by
  have previous := Upper.source_entries (21 : Basis) j
  have restore : hamiltonianRows21[j.val]! = (if j=(21 : Basis) then 3150000000000000 else 0)-Upper.numerator (21 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_21 : appliedColumns21 = hamiltonianRows.map (fun row => Rows.dot row frameColumns21) := by rfl

theorem gram_row_21 : gramRows21 = frameColumns.map (Rows.dot frameColumns21) := by rfl

theorem eigen_residual_21 : residualColumns21 = (appliedColumns21.zip frameColumns21).map (fun pair => pair.1-pair.2*energies[21]!) := by rfl

theorem gram_error_21 : ((gramRows21.zip (List.ofFn (fun j : Fin 98 => if j=(21 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_21 : (residualColumns21.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_21 : hamiltonianRows21.length = 98 := by rfl
theorem frameRows_length_21 : frameRows21.length = 98 := by rfl
theorem frameColumns_length_21 : frameColumns21.length = 98 := by rfl
theorem appliedColumns_length_21 : appliedColumns21.length = 98 := by rfl
theorem gramRows_length_21 : gramRows21.length = 98 := by rfl
theorem residualColumns_length_21 : residualColumns21.length = 98 := by rfl

theorem original_row_22 : frameRows22 = originalRows[22]! := by rfl

theorem original_column_22 : frameColumns22 = originalRows.map (fun row => row[22]!) := by rfl

theorem original_hamiltonian_22 (j : Basis) : hamiltonianRows22[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (22 : Basis) j := by
  have previous := Upper.source_entries (22 : Basis) j
  have restore : hamiltonianRows22[j.val]! = (if j=(22 : Basis) then 3150000000000000 else 0)-Upper.numerator (22 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_22 : appliedColumns22 = hamiltonianRows.map (fun row => Rows.dot row frameColumns22) := by rfl

theorem gram_row_22 : gramRows22 = frameColumns.map (Rows.dot frameColumns22) := by rfl

theorem eigen_residual_22 : residualColumns22 = (appliedColumns22.zip frameColumns22).map (fun pair => pair.1-pair.2*energies[22]!) := by rfl

theorem gram_error_22 : ((gramRows22.zip (List.ofFn (fun j : Fin 98 => if j=(22 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_22 : (residualColumns22.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_22 : hamiltonianRows22.length = 98 := by rfl
theorem frameRows_length_22 : frameRows22.length = 98 := by rfl
theorem frameColumns_length_22 : frameColumns22.length = 98 := by rfl
theorem appliedColumns_length_22 : appliedColumns22.length = 98 := by rfl
theorem gramRows_length_22 : gramRows22.length = 98 := by rfl
theorem residualColumns_length_22 : residualColumns22.length = 98 := by rfl

theorem original_row_23 : frameRows23 = originalRows[23]! := by rfl

theorem original_column_23 : frameColumns23 = originalRows.map (fun row => row[23]!) := by rfl

theorem original_hamiltonian_23 (j : Basis) : hamiltonianRows23[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (23 : Basis) j := by
  have previous := Upper.source_entries (23 : Basis) j
  have restore : hamiltonianRows23[j.val]! = (if j=(23 : Basis) then 3150000000000000 else 0)-Upper.numerator (23 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_23 : appliedColumns23 = hamiltonianRows.map (fun row => Rows.dot row frameColumns23) := by rfl

theorem gram_row_23 : gramRows23 = frameColumns.map (Rows.dot frameColumns23) := by rfl

theorem eigen_residual_23 : residualColumns23 = (appliedColumns23.zip frameColumns23).map (fun pair => pair.1-pair.2*energies[23]!) := by rfl

theorem gram_error_23 : ((gramRows23.zip (List.ofFn (fun j : Fin 98 => if j=(23 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_23 : (residualColumns23.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_23 : hamiltonianRows23.length = 98 := by rfl
theorem frameRows_length_23 : frameRows23.length = 98 := by rfl
theorem frameColumns_length_23 : frameColumns23.length = 98 := by rfl
theorem appliedColumns_length_23 : appliedColumns23.length = 98 := by rfl
theorem gramRows_length_23 : gramRows23.length = 98 := by rfl
theorem residualColumns_length_23 : residualColumns23.length = 98 := by rfl

theorem original_row_24 : frameRows24 = originalRows[24]! := by rfl

theorem original_column_24 : frameColumns24 = originalRows.map (fun row => row[24]!) := by rfl

theorem original_hamiltonian_24 (j : Basis) : hamiltonianRows24[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (24 : Basis) j := by
  have previous := Upper.source_entries (24 : Basis) j
  have restore : hamiltonianRows24[j.val]! = (if j=(24 : Basis) then 3150000000000000 else 0)-Upper.numerator (24 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_24 : appliedColumns24 = hamiltonianRows.map (fun row => Rows.dot row frameColumns24) := by rfl

theorem gram_row_24 : gramRows24 = frameColumns.map (Rows.dot frameColumns24) := by rfl

theorem eigen_residual_24 : residualColumns24 = (appliedColumns24.zip frameColumns24).map (fun pair => pair.1-pair.2*energies[24]!) := by rfl

theorem gram_error_24 : ((gramRows24.zip (List.ofFn (fun j : Fin 98 => if j=(24 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_24 : (residualColumns24.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_24 : hamiltonianRows24.length = 98 := by rfl
theorem frameRows_length_24 : frameRows24.length = 98 := by rfl
theorem frameColumns_length_24 : frameColumns24.length = 98 := by rfl
theorem appliedColumns_length_24 : appliedColumns24.length = 98 := by rfl
theorem gramRows_length_24 : gramRows24.length = 98 := by rfl
theorem residualColumns_length_24 : residualColumns24.length = 98 := by rfl

theorem original_row_25 : frameRows25 = originalRows[25]! := by rfl

theorem original_column_25 : frameColumns25 = originalRows.map (fun row => row[25]!) := by rfl

theorem original_hamiltonian_25 (j : Basis) : hamiltonianRows25[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (25 : Basis) j := by
  have previous := Upper.source_entries (25 : Basis) j
  have restore : hamiltonianRows25[j.val]! = (if j=(25 : Basis) then 3150000000000000 else 0)-Upper.numerator (25 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_25 : appliedColumns25 = hamiltonianRows.map (fun row => Rows.dot row frameColumns25) := by rfl

theorem gram_row_25 : gramRows25 = frameColumns.map (Rows.dot frameColumns25) := by rfl

theorem eigen_residual_25 : residualColumns25 = (appliedColumns25.zip frameColumns25).map (fun pair => pair.1-pair.2*energies[25]!) := by rfl

theorem gram_error_25 : ((gramRows25.zip (List.ofFn (fun j : Fin 98 => if j=(25 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_25 : (residualColumns25.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_25 : hamiltonianRows25.length = 98 := by rfl
theorem frameRows_length_25 : frameRows25.length = 98 := by rfl
theorem frameColumns_length_25 : frameColumns25.length = 98 := by rfl
theorem appliedColumns_length_25 : appliedColumns25.length = 98 := by rfl
theorem gramRows_length_25 : gramRows25.length = 98 := by rfl
theorem residualColumns_length_25 : residualColumns25.length = 98 := by rfl

theorem original_row_26 : frameRows26 = originalRows[26]! := by rfl

theorem original_column_26 : frameColumns26 = originalRows.map (fun row => row[26]!) := by rfl

theorem original_hamiltonian_26 (j : Basis) : hamiltonianRows26[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (26 : Basis) j := by
  have previous := Upper.source_entries (26 : Basis) j
  have restore : hamiltonianRows26[j.val]! = (if j=(26 : Basis) then 3150000000000000 else 0)-Upper.numerator (26 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_26 : appliedColumns26 = hamiltonianRows.map (fun row => Rows.dot row frameColumns26) := by rfl

theorem gram_row_26 : gramRows26 = frameColumns.map (Rows.dot frameColumns26) := by rfl

theorem eigen_residual_26 : residualColumns26 = (appliedColumns26.zip frameColumns26).map (fun pair => pair.1-pair.2*energies[26]!) := by rfl

theorem gram_error_26 : ((gramRows26.zip (List.ofFn (fun j : Fin 98 => if j=(26 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_26 : (residualColumns26.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_26 : hamiltonianRows26.length = 98 := by rfl
theorem frameRows_length_26 : frameRows26.length = 98 := by rfl
theorem frameColumns_length_26 : frameColumns26.length = 98 := by rfl
theorem appliedColumns_length_26 : appliedColumns26.length = 98 := by rfl
theorem gramRows_length_26 : gramRows26.length = 98 := by rfl
theorem residualColumns_length_26 : residualColumns26.length = 98 := by rfl

theorem original_row_27 : frameRows27 = originalRows[27]! := by rfl

theorem original_column_27 : frameColumns27 = originalRows.map (fun row => row[27]!) := by rfl

theorem original_hamiltonian_27 (j : Basis) : hamiltonianRows27[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (27 : Basis) j := by
  have previous := Upper.source_entries (27 : Basis) j
  have restore : hamiltonianRows27[j.val]! = (if j=(27 : Basis) then 3150000000000000 else 0)-Upper.numerator (27 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_27 : appliedColumns27 = hamiltonianRows.map (fun row => Rows.dot row frameColumns27) := by rfl

theorem gram_row_27 : gramRows27 = frameColumns.map (Rows.dot frameColumns27) := by rfl

theorem eigen_residual_27 : residualColumns27 = (appliedColumns27.zip frameColumns27).map (fun pair => pair.1-pair.2*energies[27]!) := by rfl

theorem gram_error_27 : ((gramRows27.zip (List.ofFn (fun j : Fin 98 => if j=(27 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_27 : (residualColumns27.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_27 : hamiltonianRows27.length = 98 := by rfl
theorem frameRows_length_27 : frameRows27.length = 98 := by rfl
theorem frameColumns_length_27 : frameColumns27.length = 98 := by rfl
theorem appliedColumns_length_27 : appliedColumns27.length = 98 := by rfl
theorem gramRows_length_27 : gramRows27.length = 98 := by rfl
theorem residualColumns_length_27 : residualColumns27.length = 98 := by rfl

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
