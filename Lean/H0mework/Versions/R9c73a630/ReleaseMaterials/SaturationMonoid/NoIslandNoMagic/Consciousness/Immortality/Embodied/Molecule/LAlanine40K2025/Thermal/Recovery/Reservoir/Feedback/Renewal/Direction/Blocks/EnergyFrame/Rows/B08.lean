import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Data
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Upper.Assembly

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
open Spectral Propagation.Interface

theorem original_row_56 : frameRows56 = originalRows[56]! := by rfl

theorem original_column_56 : frameColumns56 = originalRows.map (fun row => row[56]!) := by rfl

theorem original_hamiltonian_56 (j : Basis) : hamiltonianRows56[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (56 : Basis) j := by
  have previous := Upper.source_entries (56 : Basis) j
  have restore : hamiltonianRows56[j.val]! = (if j=(56 : Basis) then 3150000000000000 else 0)-Upper.numerator (56 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_56 : appliedColumns56 = hamiltonianRows.map (fun row => Rows.dot row frameColumns56) := by rfl

theorem gram_row_56 : gramRows56 = frameColumns.map (Rows.dot frameColumns56) := by rfl

theorem eigen_residual_56 : residualColumns56 = (appliedColumns56.zip frameColumns56).map (fun pair => pair.1-pair.2*energies[56]!) := by rfl

theorem gram_error_56 : ((gramRows56.zip (List.ofFn (fun j : Fin 98 => if j=(56 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_56 : (residualColumns56.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_56 : hamiltonianRows56.length = 98 := by rfl
theorem frameRows_length_56 : frameRows56.length = 98 := by rfl
theorem frameColumns_length_56 : frameColumns56.length = 98 := by rfl
theorem appliedColumns_length_56 : appliedColumns56.length = 98 := by rfl
theorem gramRows_length_56 : gramRows56.length = 98 := by rfl
theorem residualColumns_length_56 : residualColumns56.length = 98 := by rfl

theorem original_row_57 : frameRows57 = originalRows[57]! := by rfl

theorem original_column_57 : frameColumns57 = originalRows.map (fun row => row[57]!) := by rfl

theorem original_hamiltonian_57 (j : Basis) : hamiltonianRows57[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (57 : Basis) j := by
  have previous := Upper.source_entries (57 : Basis) j
  have restore : hamiltonianRows57[j.val]! = (if j=(57 : Basis) then 3150000000000000 else 0)-Upper.numerator (57 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_57 : appliedColumns57 = hamiltonianRows.map (fun row => Rows.dot row frameColumns57) := by rfl

theorem gram_row_57 : gramRows57 = frameColumns.map (Rows.dot frameColumns57) := by rfl

theorem eigen_residual_57 : residualColumns57 = (appliedColumns57.zip frameColumns57).map (fun pair => pair.1-pair.2*energies[57]!) := by rfl

theorem gram_error_57 : ((gramRows57.zip (List.ofFn (fun j : Fin 98 => if j=(57 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_57 : (residualColumns57.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_57 : hamiltonianRows57.length = 98 := by rfl
theorem frameRows_length_57 : frameRows57.length = 98 := by rfl
theorem frameColumns_length_57 : frameColumns57.length = 98 := by rfl
theorem appliedColumns_length_57 : appliedColumns57.length = 98 := by rfl
theorem gramRows_length_57 : gramRows57.length = 98 := by rfl
theorem residualColumns_length_57 : residualColumns57.length = 98 := by rfl

theorem original_row_58 : frameRows58 = originalRows[58]! := by rfl

theorem original_column_58 : frameColumns58 = originalRows.map (fun row => row[58]!) := by rfl

theorem original_hamiltonian_58 (j : Basis) : hamiltonianRows58[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (58 : Basis) j := by
  have previous := Upper.source_entries (58 : Basis) j
  have restore : hamiltonianRows58[j.val]! = (if j=(58 : Basis) then 3150000000000000 else 0)-Upper.numerator (58 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_58 : appliedColumns58 = hamiltonianRows.map (fun row => Rows.dot row frameColumns58) := by rfl

theorem gram_row_58 : gramRows58 = frameColumns.map (Rows.dot frameColumns58) := by rfl

theorem eigen_residual_58 : residualColumns58 = (appliedColumns58.zip frameColumns58).map (fun pair => pair.1-pair.2*energies[58]!) := by rfl

theorem gram_error_58 : ((gramRows58.zip (List.ofFn (fun j : Fin 98 => if j=(58 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_58 : (residualColumns58.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_58 : hamiltonianRows58.length = 98 := by rfl
theorem frameRows_length_58 : frameRows58.length = 98 := by rfl
theorem frameColumns_length_58 : frameColumns58.length = 98 := by rfl
theorem appliedColumns_length_58 : appliedColumns58.length = 98 := by rfl
theorem gramRows_length_58 : gramRows58.length = 98 := by rfl
theorem residualColumns_length_58 : residualColumns58.length = 98 := by rfl

theorem original_row_59 : frameRows59 = originalRows[59]! := by rfl

theorem original_column_59 : frameColumns59 = originalRows.map (fun row => row[59]!) := by rfl

theorem original_hamiltonian_59 (j : Basis) : hamiltonianRows59[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (59 : Basis) j := by
  have previous := Upper.source_entries (59 : Basis) j
  have restore : hamiltonianRows59[j.val]! = (if j=(59 : Basis) then 3150000000000000 else 0)-Upper.numerator (59 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_59 : appliedColumns59 = hamiltonianRows.map (fun row => Rows.dot row frameColumns59) := by rfl

theorem gram_row_59 : gramRows59 = frameColumns.map (Rows.dot frameColumns59) := by rfl

theorem eigen_residual_59 : residualColumns59 = (appliedColumns59.zip frameColumns59).map (fun pair => pair.1-pair.2*energies[59]!) := by rfl

theorem gram_error_59 : ((gramRows59.zip (List.ofFn (fun j : Fin 98 => if j=(59 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_59 : (residualColumns59.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_59 : hamiltonianRows59.length = 98 := by rfl
theorem frameRows_length_59 : frameRows59.length = 98 := by rfl
theorem frameColumns_length_59 : frameColumns59.length = 98 := by rfl
theorem appliedColumns_length_59 : appliedColumns59.length = 98 := by rfl
theorem gramRows_length_59 : gramRows59.length = 98 := by rfl
theorem residualColumns_length_59 : residualColumns59.length = 98 := by rfl

theorem original_row_60 : frameRows60 = originalRows[60]! := by rfl

theorem original_column_60 : frameColumns60 = originalRows.map (fun row => row[60]!) := by rfl

theorem original_hamiltonian_60 (j : Basis) : hamiltonianRows60[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (60 : Basis) j := by
  have previous := Upper.source_entries (60 : Basis) j
  have restore : hamiltonianRows60[j.val]! = (if j=(60 : Basis) then 3150000000000000 else 0)-Upper.numerator (60 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_60 : appliedColumns60 = hamiltonianRows.map (fun row => Rows.dot row frameColumns60) := by rfl

theorem gram_row_60 : gramRows60 = frameColumns.map (Rows.dot frameColumns60) := by rfl

theorem eigen_residual_60 : residualColumns60 = (appliedColumns60.zip frameColumns60).map (fun pair => pair.1-pair.2*energies[60]!) := by rfl

theorem gram_error_60 : ((gramRows60.zip (List.ofFn (fun j : Fin 98 => if j=(60 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_60 : (residualColumns60.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_60 : hamiltonianRows60.length = 98 := by rfl
theorem frameRows_length_60 : frameRows60.length = 98 := by rfl
theorem frameColumns_length_60 : frameColumns60.length = 98 := by rfl
theorem appliedColumns_length_60 : appliedColumns60.length = 98 := by rfl
theorem gramRows_length_60 : gramRows60.length = 98 := by rfl
theorem residualColumns_length_60 : residualColumns60.length = 98 := by rfl

theorem original_row_61 : frameRows61 = originalRows[61]! := by rfl

theorem original_column_61 : frameColumns61 = originalRows.map (fun row => row[61]!) := by rfl

theorem original_hamiltonian_61 (j : Basis) : hamiltonianRows61[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (61 : Basis) j := by
  have previous := Upper.source_entries (61 : Basis) j
  have restore : hamiltonianRows61[j.val]! = (if j=(61 : Basis) then 3150000000000000 else 0)-Upper.numerator (61 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_61 : appliedColumns61 = hamiltonianRows.map (fun row => Rows.dot row frameColumns61) := by rfl

theorem gram_row_61 : gramRows61 = frameColumns.map (Rows.dot frameColumns61) := by rfl

theorem eigen_residual_61 : residualColumns61 = (appliedColumns61.zip frameColumns61).map (fun pair => pair.1-pair.2*energies[61]!) := by rfl

theorem gram_error_61 : ((gramRows61.zip (List.ofFn (fun j : Fin 98 => if j=(61 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_61 : (residualColumns61.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_61 : hamiltonianRows61.length = 98 := by rfl
theorem frameRows_length_61 : frameRows61.length = 98 := by rfl
theorem frameColumns_length_61 : frameColumns61.length = 98 := by rfl
theorem appliedColumns_length_61 : appliedColumns61.length = 98 := by rfl
theorem gramRows_length_61 : gramRows61.length = 98 := by rfl
theorem residualColumns_length_61 : residualColumns61.length = 98 := by rfl

theorem original_row_62 : frameRows62 = originalRows[62]! := by rfl

theorem original_column_62 : frameColumns62 = originalRows.map (fun row => row[62]!) := by rfl

theorem original_hamiltonian_62 (j : Basis) : hamiltonianRows62[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (62 : Basis) j := by
  have previous := Upper.source_entries (62 : Basis) j
  have restore : hamiltonianRows62[j.val]! = (if j=(62 : Basis) then 3150000000000000 else 0)-Upper.numerator (62 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_62 : appliedColumns62 = hamiltonianRows.map (fun row => Rows.dot row frameColumns62) := by rfl

theorem gram_row_62 : gramRows62 = frameColumns.map (Rows.dot frameColumns62) := by rfl

theorem eigen_residual_62 : residualColumns62 = (appliedColumns62.zip frameColumns62).map (fun pair => pair.1-pair.2*energies[62]!) := by rfl

theorem gram_error_62 : ((gramRows62.zip (List.ofFn (fun j : Fin 98 => if j=(62 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_62 : (residualColumns62.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_62 : hamiltonianRows62.length = 98 := by rfl
theorem frameRows_length_62 : frameRows62.length = 98 := by rfl
theorem frameColumns_length_62 : frameColumns62.length = 98 := by rfl
theorem appliedColumns_length_62 : appliedColumns62.length = 98 := by rfl
theorem gramRows_length_62 : gramRows62.length = 98 := by rfl
theorem residualColumns_length_62 : residualColumns62.length = 98 := by rfl

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
