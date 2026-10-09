import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Data
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Upper.Assembly

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
open Spectral Propagation.Interface

theorem original_row_77 : frameRows77 = originalRows[77]! := by rfl

theorem original_column_77 : frameColumns77 = originalRows.map (fun row => row[77]!) := by rfl

theorem original_hamiltonian_77 (j : Basis) : hamiltonianRows77[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (77 : Basis) j := by
  have previous := Upper.source_entries (77 : Basis) j
  have restore : hamiltonianRows77[j.val]! = (if j=(77 : Basis) then 3150000000000000 else 0)-Upper.numerator (77 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_77 : appliedColumns77 = hamiltonianRows.map (fun row => Rows.dot row frameColumns77) := by rfl

theorem gram_row_77 : gramRows77 = frameColumns.map (Rows.dot frameColumns77) := by rfl

theorem eigen_residual_77 : residualColumns77 = (appliedColumns77.zip frameColumns77).map (fun pair => pair.1-pair.2*energies[77]!) := by rfl

theorem gram_error_77 : ((gramRows77.zip (List.ofFn (fun j : Fin 98 => if j=(77 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_77 : (residualColumns77.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_77 : hamiltonianRows77.length = 98 := by rfl
theorem frameRows_length_77 : frameRows77.length = 98 := by rfl
theorem frameColumns_length_77 : frameColumns77.length = 98 := by rfl
theorem appliedColumns_length_77 : appliedColumns77.length = 98 := by rfl
theorem gramRows_length_77 : gramRows77.length = 98 := by rfl
theorem residualColumns_length_77 : residualColumns77.length = 98 := by rfl

theorem original_row_78 : frameRows78 = originalRows[78]! := by rfl

theorem original_column_78 : frameColumns78 = originalRows.map (fun row => row[78]!) := by rfl

theorem original_hamiltonian_78 (j : Basis) : hamiltonianRows78[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (78 : Basis) j := by
  have previous := Upper.source_entries (78 : Basis) j
  have restore : hamiltonianRows78[j.val]! = (if j=(78 : Basis) then 3150000000000000 else 0)-Upper.numerator (78 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_78 : appliedColumns78 = hamiltonianRows.map (fun row => Rows.dot row frameColumns78) := by rfl

theorem gram_row_78 : gramRows78 = frameColumns.map (Rows.dot frameColumns78) := by rfl

theorem eigen_residual_78 : residualColumns78 = (appliedColumns78.zip frameColumns78).map (fun pair => pair.1-pair.2*energies[78]!) := by rfl

theorem gram_error_78 : ((gramRows78.zip (List.ofFn (fun j : Fin 98 => if j=(78 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_78 : (residualColumns78.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_78 : hamiltonianRows78.length = 98 := by rfl
theorem frameRows_length_78 : frameRows78.length = 98 := by rfl
theorem frameColumns_length_78 : frameColumns78.length = 98 := by rfl
theorem appliedColumns_length_78 : appliedColumns78.length = 98 := by rfl
theorem gramRows_length_78 : gramRows78.length = 98 := by rfl
theorem residualColumns_length_78 : residualColumns78.length = 98 := by rfl

theorem original_row_79 : frameRows79 = originalRows[79]! := by rfl

theorem original_column_79 : frameColumns79 = originalRows.map (fun row => row[79]!) := by rfl

theorem original_hamiltonian_79 (j : Basis) : hamiltonianRows79[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (79 : Basis) j := by
  have previous := Upper.source_entries (79 : Basis) j
  have restore : hamiltonianRows79[j.val]! = (if j=(79 : Basis) then 3150000000000000 else 0)-Upper.numerator (79 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_79 : appliedColumns79 = hamiltonianRows.map (fun row => Rows.dot row frameColumns79) := by rfl

theorem gram_row_79 : gramRows79 = frameColumns.map (Rows.dot frameColumns79) := by rfl

theorem eigen_residual_79 : residualColumns79 = (appliedColumns79.zip frameColumns79).map (fun pair => pair.1-pair.2*energies[79]!) := by rfl

theorem gram_error_79 : ((gramRows79.zip (List.ofFn (fun j : Fin 98 => if j=(79 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_79 : (residualColumns79.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_79 : hamiltonianRows79.length = 98 := by rfl
theorem frameRows_length_79 : frameRows79.length = 98 := by rfl
theorem frameColumns_length_79 : frameColumns79.length = 98 := by rfl
theorem appliedColumns_length_79 : appliedColumns79.length = 98 := by rfl
theorem gramRows_length_79 : gramRows79.length = 98 := by rfl
theorem residualColumns_length_79 : residualColumns79.length = 98 := by rfl

theorem original_row_80 : frameRows80 = originalRows[80]! := by rfl

theorem original_column_80 : frameColumns80 = originalRows.map (fun row => row[80]!) := by rfl

theorem original_hamiltonian_80 (j : Basis) : hamiltonianRows80[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (80 : Basis) j := by
  have previous := Upper.source_entries (80 : Basis) j
  have restore : hamiltonianRows80[j.val]! = (if j=(80 : Basis) then 3150000000000000 else 0)-Upper.numerator (80 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_80 : appliedColumns80 = hamiltonianRows.map (fun row => Rows.dot row frameColumns80) := by rfl

theorem gram_row_80 : gramRows80 = frameColumns.map (Rows.dot frameColumns80) := by rfl

theorem eigen_residual_80 : residualColumns80 = (appliedColumns80.zip frameColumns80).map (fun pair => pair.1-pair.2*energies[80]!) := by rfl

theorem gram_error_80 : ((gramRows80.zip (List.ofFn (fun j : Fin 98 => if j=(80 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_80 : (residualColumns80.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_80 : hamiltonianRows80.length = 98 := by rfl
theorem frameRows_length_80 : frameRows80.length = 98 := by rfl
theorem frameColumns_length_80 : frameColumns80.length = 98 := by rfl
theorem appliedColumns_length_80 : appliedColumns80.length = 98 := by rfl
theorem gramRows_length_80 : gramRows80.length = 98 := by rfl
theorem residualColumns_length_80 : residualColumns80.length = 98 := by rfl

theorem original_row_81 : frameRows81 = originalRows[81]! := by rfl

theorem original_column_81 : frameColumns81 = originalRows.map (fun row => row[81]!) := by rfl

theorem original_hamiltonian_81 (j : Basis) : hamiltonianRows81[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (81 : Basis) j := by
  have previous := Upper.source_entries (81 : Basis) j
  have restore : hamiltonianRows81[j.val]! = (if j=(81 : Basis) then 3150000000000000 else 0)-Upper.numerator (81 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_81 : appliedColumns81 = hamiltonianRows.map (fun row => Rows.dot row frameColumns81) := by rfl

theorem gram_row_81 : gramRows81 = frameColumns.map (Rows.dot frameColumns81) := by rfl

theorem eigen_residual_81 : residualColumns81 = (appliedColumns81.zip frameColumns81).map (fun pair => pair.1-pair.2*energies[81]!) := by rfl

theorem gram_error_81 : ((gramRows81.zip (List.ofFn (fun j : Fin 98 => if j=(81 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_81 : (residualColumns81.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_81 : hamiltonianRows81.length = 98 := by rfl
theorem frameRows_length_81 : frameRows81.length = 98 := by rfl
theorem frameColumns_length_81 : frameColumns81.length = 98 := by rfl
theorem appliedColumns_length_81 : appliedColumns81.length = 98 := by rfl
theorem gramRows_length_81 : gramRows81.length = 98 := by rfl
theorem residualColumns_length_81 : residualColumns81.length = 98 := by rfl

theorem original_row_82 : frameRows82 = originalRows[82]! := by rfl

theorem original_column_82 : frameColumns82 = originalRows.map (fun row => row[82]!) := by rfl

theorem original_hamiltonian_82 (j : Basis) : hamiltonianRows82[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (82 : Basis) j := by
  have previous := Upper.source_entries (82 : Basis) j
  have restore : hamiltonianRows82[j.val]! = (if j=(82 : Basis) then 3150000000000000 else 0)-Upper.numerator (82 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_82 : appliedColumns82 = hamiltonianRows.map (fun row => Rows.dot row frameColumns82) := by rfl

theorem gram_row_82 : gramRows82 = frameColumns.map (Rows.dot frameColumns82) := by rfl

theorem eigen_residual_82 : residualColumns82 = (appliedColumns82.zip frameColumns82).map (fun pair => pair.1-pair.2*energies[82]!) := by rfl

theorem gram_error_82 : ((gramRows82.zip (List.ofFn (fun j : Fin 98 => if j=(82 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_82 : (residualColumns82.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_82 : hamiltonianRows82.length = 98 := by rfl
theorem frameRows_length_82 : frameRows82.length = 98 := by rfl
theorem frameColumns_length_82 : frameColumns82.length = 98 := by rfl
theorem appliedColumns_length_82 : appliedColumns82.length = 98 := by rfl
theorem gramRows_length_82 : gramRows82.length = 98 := by rfl
theorem residualColumns_length_82 : residualColumns82.length = 98 := by rfl

theorem original_row_83 : frameRows83 = originalRows[83]! := by rfl

theorem original_column_83 : frameColumns83 = originalRows.map (fun row => row[83]!) := by rfl

theorem original_hamiltonian_83 (j : Basis) : hamiltonianRows83[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (83 : Basis) j := by
  have previous := Upper.source_entries (83 : Basis) j
  have restore : hamiltonianRows83[j.val]! = (if j=(83 : Basis) then 3150000000000000 else 0)-Upper.numerator (83 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_83 : appliedColumns83 = hamiltonianRows.map (fun row => Rows.dot row frameColumns83) := by rfl

theorem gram_row_83 : gramRows83 = frameColumns.map (Rows.dot frameColumns83) := by rfl

theorem eigen_residual_83 : residualColumns83 = (appliedColumns83.zip frameColumns83).map (fun pair => pair.1-pair.2*energies[83]!) := by rfl

theorem gram_error_83 : ((gramRows83.zip (List.ofFn (fun j : Fin 98 => if j=(83 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_83 : (residualColumns83.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_83 : hamiltonianRows83.length = 98 := by rfl
theorem frameRows_length_83 : frameRows83.length = 98 := by rfl
theorem frameColumns_length_83 : frameColumns83.length = 98 := by rfl
theorem appliedColumns_length_83 : appliedColumns83.length = 98 := by rfl
theorem gramRows_length_83 : gramRows83.length = 98 := by rfl
theorem residualColumns_length_83 : residualColumns83.length = 98 := by rfl

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
