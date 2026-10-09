import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Data
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Upper.Assembly

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
open Spectral Propagation.Interface

theorem original_row_0 : frameRows0 = originalRows[0]! := by rfl

theorem original_column_0 : frameColumns0 = originalRows.map (fun row => row[0]!) := by rfl

theorem original_hamiltonian_0 (j : Basis) : hamiltonianRows0[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (0 : Basis) j := by
  have previous := Upper.source_entries (0 : Basis) j
  have restore : hamiltonianRows0[j.val]! = (if j=(0 : Basis) then 3150000000000000 else 0)-Upper.numerator (0 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_0 : appliedColumns0 = hamiltonianRows.map (fun row => Rows.dot row frameColumns0) := by rfl

theorem gram_row_0 : gramRows0 = frameColumns.map (Rows.dot frameColumns0) := by rfl

theorem eigen_residual_0 : residualColumns0 = (appliedColumns0.zip frameColumns0).map (fun pair => pair.1-pair.2*energies[0]!) := by rfl

theorem gram_error_0 : ((gramRows0.zip (List.ofFn (fun j : Fin 98 => if j=(0 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_0 : (residualColumns0.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_0 : hamiltonianRows0.length = 98 := by rfl
theorem frameRows_length_0 : frameRows0.length = 98 := by rfl
theorem frameColumns_length_0 : frameColumns0.length = 98 := by rfl
theorem appliedColumns_length_0 : appliedColumns0.length = 98 := by rfl
theorem gramRows_length_0 : gramRows0.length = 98 := by rfl
theorem residualColumns_length_0 : residualColumns0.length = 98 := by rfl

theorem original_row_1 : frameRows1 = originalRows[1]! := by rfl

theorem original_column_1 : frameColumns1 = originalRows.map (fun row => row[1]!) := by rfl

theorem original_hamiltonian_1 (j : Basis) : hamiltonianRows1[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (1 : Basis) j := by
  have previous := Upper.source_entries (1 : Basis) j
  have restore : hamiltonianRows1[j.val]! = (if j=(1 : Basis) then 3150000000000000 else 0)-Upper.numerator (1 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_1 : appliedColumns1 = hamiltonianRows.map (fun row => Rows.dot row frameColumns1) := by rfl

theorem gram_row_1 : gramRows1 = frameColumns.map (Rows.dot frameColumns1) := by rfl

theorem eigen_residual_1 : residualColumns1 = (appliedColumns1.zip frameColumns1).map (fun pair => pair.1-pair.2*energies[1]!) := by rfl

theorem gram_error_1 : ((gramRows1.zip (List.ofFn (fun j : Fin 98 => if j=(1 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_1 : (residualColumns1.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_1 : hamiltonianRows1.length = 98 := by rfl
theorem frameRows_length_1 : frameRows1.length = 98 := by rfl
theorem frameColumns_length_1 : frameColumns1.length = 98 := by rfl
theorem appliedColumns_length_1 : appliedColumns1.length = 98 := by rfl
theorem gramRows_length_1 : gramRows1.length = 98 := by rfl
theorem residualColumns_length_1 : residualColumns1.length = 98 := by rfl

theorem original_row_2 : frameRows2 = originalRows[2]! := by rfl

theorem original_column_2 : frameColumns2 = originalRows.map (fun row => row[2]!) := by rfl

theorem original_hamiltonian_2 (j : Basis) : hamiltonianRows2[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (2 : Basis) j := by
  have previous := Upper.source_entries (2 : Basis) j
  have restore : hamiltonianRows2[j.val]! = (if j=(2 : Basis) then 3150000000000000 else 0)-Upper.numerator (2 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_2 : appliedColumns2 = hamiltonianRows.map (fun row => Rows.dot row frameColumns2) := by rfl

theorem gram_row_2 : gramRows2 = frameColumns.map (Rows.dot frameColumns2) := by rfl

theorem eigen_residual_2 : residualColumns2 = (appliedColumns2.zip frameColumns2).map (fun pair => pair.1-pair.2*energies[2]!) := by rfl

theorem gram_error_2 : ((gramRows2.zip (List.ofFn (fun j : Fin 98 => if j=(2 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_2 : (residualColumns2.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_2 : hamiltonianRows2.length = 98 := by rfl
theorem frameRows_length_2 : frameRows2.length = 98 := by rfl
theorem frameColumns_length_2 : frameColumns2.length = 98 := by rfl
theorem appliedColumns_length_2 : appliedColumns2.length = 98 := by rfl
theorem gramRows_length_2 : gramRows2.length = 98 := by rfl
theorem residualColumns_length_2 : residualColumns2.length = 98 := by rfl

theorem original_row_3 : frameRows3 = originalRows[3]! := by rfl

theorem original_column_3 : frameColumns3 = originalRows.map (fun row => row[3]!) := by rfl

theorem original_hamiltonian_3 (j : Basis) : hamiltonianRows3[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (3 : Basis) j := by
  have previous := Upper.source_entries (3 : Basis) j
  have restore : hamiltonianRows3[j.val]! = (if j=(3 : Basis) then 3150000000000000 else 0)-Upper.numerator (3 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_3 : appliedColumns3 = hamiltonianRows.map (fun row => Rows.dot row frameColumns3) := by rfl

theorem gram_row_3 : gramRows3 = frameColumns.map (Rows.dot frameColumns3) := by rfl

theorem eigen_residual_3 : residualColumns3 = (appliedColumns3.zip frameColumns3).map (fun pair => pair.1-pair.2*energies[3]!) := by rfl

theorem gram_error_3 : ((gramRows3.zip (List.ofFn (fun j : Fin 98 => if j=(3 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_3 : (residualColumns3.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_3 : hamiltonianRows3.length = 98 := by rfl
theorem frameRows_length_3 : frameRows3.length = 98 := by rfl
theorem frameColumns_length_3 : frameColumns3.length = 98 := by rfl
theorem appliedColumns_length_3 : appliedColumns3.length = 98 := by rfl
theorem gramRows_length_3 : gramRows3.length = 98 := by rfl
theorem residualColumns_length_3 : residualColumns3.length = 98 := by rfl

theorem original_row_4 : frameRows4 = originalRows[4]! := by rfl

theorem original_column_4 : frameColumns4 = originalRows.map (fun row => row[4]!) := by rfl

theorem original_hamiltonian_4 (j : Basis) : hamiltonianRows4[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (4 : Basis) j := by
  have previous := Upper.source_entries (4 : Basis) j
  have restore : hamiltonianRows4[j.val]! = (if j=(4 : Basis) then 3150000000000000 else 0)-Upper.numerator (4 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_4 : appliedColumns4 = hamiltonianRows.map (fun row => Rows.dot row frameColumns4) := by rfl

theorem gram_row_4 : gramRows4 = frameColumns.map (Rows.dot frameColumns4) := by rfl

theorem eigen_residual_4 : residualColumns4 = (appliedColumns4.zip frameColumns4).map (fun pair => pair.1-pair.2*energies[4]!) := by rfl

theorem gram_error_4 : ((gramRows4.zip (List.ofFn (fun j : Fin 98 => if j=(4 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_4 : (residualColumns4.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_4 : hamiltonianRows4.length = 98 := by rfl
theorem frameRows_length_4 : frameRows4.length = 98 := by rfl
theorem frameColumns_length_4 : frameColumns4.length = 98 := by rfl
theorem appliedColumns_length_4 : appliedColumns4.length = 98 := by rfl
theorem gramRows_length_4 : gramRows4.length = 98 := by rfl
theorem residualColumns_length_4 : residualColumns4.length = 98 := by rfl

theorem original_row_5 : frameRows5 = originalRows[5]! := by rfl

theorem original_column_5 : frameColumns5 = originalRows.map (fun row => row[5]!) := by rfl

theorem original_hamiltonian_5 (j : Basis) : hamiltonianRows5[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (5 : Basis) j := by
  have previous := Upper.source_entries (5 : Basis) j
  have restore : hamiltonianRows5[j.val]! = (if j=(5 : Basis) then 3150000000000000 else 0)-Upper.numerator (5 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_5 : appliedColumns5 = hamiltonianRows.map (fun row => Rows.dot row frameColumns5) := by rfl

theorem gram_row_5 : gramRows5 = frameColumns.map (Rows.dot frameColumns5) := by rfl

theorem eigen_residual_5 : residualColumns5 = (appliedColumns5.zip frameColumns5).map (fun pair => pair.1-pair.2*energies[5]!) := by rfl

theorem gram_error_5 : ((gramRows5.zip (List.ofFn (fun j : Fin 98 => if j=(5 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_5 : (residualColumns5.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_5 : hamiltonianRows5.length = 98 := by rfl
theorem frameRows_length_5 : frameRows5.length = 98 := by rfl
theorem frameColumns_length_5 : frameColumns5.length = 98 := by rfl
theorem appliedColumns_length_5 : appliedColumns5.length = 98 := by rfl
theorem gramRows_length_5 : gramRows5.length = 98 := by rfl
theorem residualColumns_length_5 : residualColumns5.length = 98 := by rfl

theorem original_row_6 : frameRows6 = originalRows[6]! := by rfl

theorem original_column_6 : frameColumns6 = originalRows.map (fun row => row[6]!) := by rfl

theorem original_hamiltonian_6 (j : Basis) : hamiltonianRows6[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (6 : Basis) j := by
  have previous := Upper.source_entries (6 : Basis) j
  have restore : hamiltonianRows6[j.val]! = (if j=(6 : Basis) then 3150000000000000 else 0)-Upper.numerator (6 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_6 : appliedColumns6 = hamiltonianRows.map (fun row => Rows.dot row frameColumns6) := by rfl

theorem gram_row_6 : gramRows6 = frameColumns.map (Rows.dot frameColumns6) := by rfl

theorem eigen_residual_6 : residualColumns6 = (appliedColumns6.zip frameColumns6).map (fun pair => pair.1-pair.2*energies[6]!) := by rfl

theorem gram_error_6 : ((gramRows6.zip (List.ofFn (fun j : Fin 98 => if j=(6 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_6 : (residualColumns6.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_6 : hamiltonianRows6.length = 98 := by rfl
theorem frameRows_length_6 : frameRows6.length = 98 := by rfl
theorem frameColumns_length_6 : frameColumns6.length = 98 := by rfl
theorem appliedColumns_length_6 : appliedColumns6.length = 98 := by rfl
theorem gramRows_length_6 : gramRows6.length = 98 := by rfl
theorem residualColumns_length_6 : residualColumns6.length = 98 := by rfl

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
