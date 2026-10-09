import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Data
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Upper.Assembly

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
open Spectral Propagation.Interface

theorem original_row_7 : frameRows7 = originalRows[7]! := by rfl

theorem original_column_7 : frameColumns7 = originalRows.map (fun row => row[7]!) := by rfl

theorem original_hamiltonian_7 (j : Basis) : hamiltonianRows7[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (7 : Basis) j := by
  have previous := Upper.source_entries (7 : Basis) j
  have restore : hamiltonianRows7[j.val]! = (if j=(7 : Basis) then 3150000000000000 else 0)-Upper.numerator (7 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_7 : appliedColumns7 = hamiltonianRows.map (fun row => Rows.dot row frameColumns7) := by rfl

theorem gram_row_7 : gramRows7 = frameColumns.map (Rows.dot frameColumns7) := by rfl

theorem eigen_residual_7 : residualColumns7 = (appliedColumns7.zip frameColumns7).map (fun pair => pair.1-pair.2*energies[7]!) := by rfl

theorem gram_error_7 : ((gramRows7.zip (List.ofFn (fun j : Fin 98 => if j=(7 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_7 : (residualColumns7.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_7 : hamiltonianRows7.length = 98 := by rfl
theorem frameRows_length_7 : frameRows7.length = 98 := by rfl
theorem frameColumns_length_7 : frameColumns7.length = 98 := by rfl
theorem appliedColumns_length_7 : appliedColumns7.length = 98 := by rfl
theorem gramRows_length_7 : gramRows7.length = 98 := by rfl
theorem residualColumns_length_7 : residualColumns7.length = 98 := by rfl

theorem original_row_8 : frameRows8 = originalRows[8]! := by rfl

theorem original_column_8 : frameColumns8 = originalRows.map (fun row => row[8]!) := by rfl

theorem original_hamiltonian_8 (j : Basis) : hamiltonianRows8[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (8 : Basis) j := by
  have previous := Upper.source_entries (8 : Basis) j
  have restore : hamiltonianRows8[j.val]! = (if j=(8 : Basis) then 3150000000000000 else 0)-Upper.numerator (8 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_8 : appliedColumns8 = hamiltonianRows.map (fun row => Rows.dot row frameColumns8) := by rfl

theorem gram_row_8 : gramRows8 = frameColumns.map (Rows.dot frameColumns8) := by rfl

theorem eigen_residual_8 : residualColumns8 = (appliedColumns8.zip frameColumns8).map (fun pair => pair.1-pair.2*energies[8]!) := by rfl

theorem gram_error_8 : ((gramRows8.zip (List.ofFn (fun j : Fin 98 => if j=(8 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_8 : (residualColumns8.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_8 : hamiltonianRows8.length = 98 := by rfl
theorem frameRows_length_8 : frameRows8.length = 98 := by rfl
theorem frameColumns_length_8 : frameColumns8.length = 98 := by rfl
theorem appliedColumns_length_8 : appliedColumns8.length = 98 := by rfl
theorem gramRows_length_8 : gramRows8.length = 98 := by rfl
theorem residualColumns_length_8 : residualColumns8.length = 98 := by rfl

theorem original_row_9 : frameRows9 = originalRows[9]! := by rfl

theorem original_column_9 : frameColumns9 = originalRows.map (fun row => row[9]!) := by rfl

theorem original_hamiltonian_9 (j : Basis) : hamiltonianRows9[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (9 : Basis) j := by
  have previous := Upper.source_entries (9 : Basis) j
  have restore : hamiltonianRows9[j.val]! = (if j=(9 : Basis) then 3150000000000000 else 0)-Upper.numerator (9 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_9 : appliedColumns9 = hamiltonianRows.map (fun row => Rows.dot row frameColumns9) := by rfl

theorem gram_row_9 : gramRows9 = frameColumns.map (Rows.dot frameColumns9) := by rfl

theorem eigen_residual_9 : residualColumns9 = (appliedColumns9.zip frameColumns9).map (fun pair => pair.1-pair.2*energies[9]!) := by rfl

theorem gram_error_9 : ((gramRows9.zip (List.ofFn (fun j : Fin 98 => if j=(9 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_9 : (residualColumns9.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_9 : hamiltonianRows9.length = 98 := by rfl
theorem frameRows_length_9 : frameRows9.length = 98 := by rfl
theorem frameColumns_length_9 : frameColumns9.length = 98 := by rfl
theorem appliedColumns_length_9 : appliedColumns9.length = 98 := by rfl
theorem gramRows_length_9 : gramRows9.length = 98 := by rfl
theorem residualColumns_length_9 : residualColumns9.length = 98 := by rfl

theorem original_row_10 : frameRows10 = originalRows[10]! := by rfl

theorem original_column_10 : frameColumns10 = originalRows.map (fun row => row[10]!) := by rfl

theorem original_hamiltonian_10 (j : Basis) : hamiltonianRows10[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (10 : Basis) j := by
  have previous := Upper.source_entries (10 : Basis) j
  have restore : hamiltonianRows10[j.val]! = (if j=(10 : Basis) then 3150000000000000 else 0)-Upper.numerator (10 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_10 : appliedColumns10 = hamiltonianRows.map (fun row => Rows.dot row frameColumns10) := by rfl

theorem gram_row_10 : gramRows10 = frameColumns.map (Rows.dot frameColumns10) := by rfl

theorem eigen_residual_10 : residualColumns10 = (appliedColumns10.zip frameColumns10).map (fun pair => pair.1-pair.2*energies[10]!) := by rfl

theorem gram_error_10 : ((gramRows10.zip (List.ofFn (fun j : Fin 98 => if j=(10 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_10 : (residualColumns10.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_10 : hamiltonianRows10.length = 98 := by rfl
theorem frameRows_length_10 : frameRows10.length = 98 := by rfl
theorem frameColumns_length_10 : frameColumns10.length = 98 := by rfl
theorem appliedColumns_length_10 : appliedColumns10.length = 98 := by rfl
theorem gramRows_length_10 : gramRows10.length = 98 := by rfl
theorem residualColumns_length_10 : residualColumns10.length = 98 := by rfl

theorem original_row_11 : frameRows11 = originalRows[11]! := by rfl

theorem original_column_11 : frameColumns11 = originalRows.map (fun row => row[11]!) := by rfl

theorem original_hamiltonian_11 (j : Basis) : hamiltonianRows11[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (11 : Basis) j := by
  have previous := Upper.source_entries (11 : Basis) j
  have restore : hamiltonianRows11[j.val]! = (if j=(11 : Basis) then 3150000000000000 else 0)-Upper.numerator (11 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_11 : appliedColumns11 = hamiltonianRows.map (fun row => Rows.dot row frameColumns11) := by rfl

theorem gram_row_11 : gramRows11 = frameColumns.map (Rows.dot frameColumns11) := by rfl

theorem eigen_residual_11 : residualColumns11 = (appliedColumns11.zip frameColumns11).map (fun pair => pair.1-pair.2*energies[11]!) := by rfl

theorem gram_error_11 : ((gramRows11.zip (List.ofFn (fun j : Fin 98 => if j=(11 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_11 : (residualColumns11.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_11 : hamiltonianRows11.length = 98 := by rfl
theorem frameRows_length_11 : frameRows11.length = 98 := by rfl
theorem frameColumns_length_11 : frameColumns11.length = 98 := by rfl
theorem appliedColumns_length_11 : appliedColumns11.length = 98 := by rfl
theorem gramRows_length_11 : gramRows11.length = 98 := by rfl
theorem residualColumns_length_11 : residualColumns11.length = 98 := by rfl

theorem original_row_12 : frameRows12 = originalRows[12]! := by rfl

theorem original_column_12 : frameColumns12 = originalRows.map (fun row => row[12]!) := by rfl

theorem original_hamiltonian_12 (j : Basis) : hamiltonianRows12[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (12 : Basis) j := by
  have previous := Upper.source_entries (12 : Basis) j
  have restore : hamiltonianRows12[j.val]! = (if j=(12 : Basis) then 3150000000000000 else 0)-Upper.numerator (12 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_12 : appliedColumns12 = hamiltonianRows.map (fun row => Rows.dot row frameColumns12) := by rfl

theorem gram_row_12 : gramRows12 = frameColumns.map (Rows.dot frameColumns12) := by rfl

theorem eigen_residual_12 : residualColumns12 = (appliedColumns12.zip frameColumns12).map (fun pair => pair.1-pair.2*energies[12]!) := by rfl

theorem gram_error_12 : ((gramRows12.zip (List.ofFn (fun j : Fin 98 => if j=(12 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_12 : (residualColumns12.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_12 : hamiltonianRows12.length = 98 := by rfl
theorem frameRows_length_12 : frameRows12.length = 98 := by rfl
theorem frameColumns_length_12 : frameColumns12.length = 98 := by rfl
theorem appliedColumns_length_12 : appliedColumns12.length = 98 := by rfl
theorem gramRows_length_12 : gramRows12.length = 98 := by rfl
theorem residualColumns_length_12 : residualColumns12.length = 98 := by rfl

theorem original_row_13 : frameRows13 = originalRows[13]! := by rfl

theorem original_column_13 : frameColumns13 = originalRows.map (fun row => row[13]!) := by rfl

theorem original_hamiltonian_13 (j : Basis) : hamiltonianRows13[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (13 : Basis) j := by
  have previous := Upper.source_entries (13 : Basis) j
  have restore : hamiltonianRows13[j.val]! = (if j=(13 : Basis) then 3150000000000000 else 0)-Upper.numerator (13 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_13 : appliedColumns13 = hamiltonianRows.map (fun row => Rows.dot row frameColumns13) := by rfl

theorem gram_row_13 : gramRows13 = frameColumns.map (Rows.dot frameColumns13) := by rfl

theorem eigen_residual_13 : residualColumns13 = (appliedColumns13.zip frameColumns13).map (fun pair => pair.1-pair.2*energies[13]!) := by rfl

theorem gram_error_13 : ((gramRows13.zip (List.ofFn (fun j : Fin 98 => if j=(13 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_13 : (residualColumns13.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_13 : hamiltonianRows13.length = 98 := by rfl
theorem frameRows_length_13 : frameRows13.length = 98 := by rfl
theorem frameColumns_length_13 : frameColumns13.length = 98 := by rfl
theorem appliedColumns_length_13 : appliedColumns13.length = 98 := by rfl
theorem gramRows_length_13 : gramRows13.length = 98 := by rfl
theorem residualColumns_length_13 : residualColumns13.length = 98 := by rfl

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
