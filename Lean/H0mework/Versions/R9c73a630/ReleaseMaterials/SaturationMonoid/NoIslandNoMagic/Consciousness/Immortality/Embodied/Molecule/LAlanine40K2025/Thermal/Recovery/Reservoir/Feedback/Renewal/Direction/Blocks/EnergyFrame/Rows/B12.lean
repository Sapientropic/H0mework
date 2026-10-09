import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Data
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Upper.Assembly

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
open Spectral Propagation.Interface

theorem original_row_84 : frameRows84 = originalRows[84]! := by rfl

theorem original_column_84 : frameColumns84 = originalRows.map (fun row => row[84]!) := by rfl

theorem original_hamiltonian_84 (j : Basis) : hamiltonianRows84[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (84 : Basis) j := by
  have previous := Upper.source_entries (84 : Basis) j
  have restore : hamiltonianRows84[j.val]! = (if j=(84 : Basis) then 3150000000000000 else 0)-Upper.numerator (84 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_84 : appliedColumns84 = hamiltonianRows.map (fun row => Rows.dot row frameColumns84) := by rfl

theorem gram_row_84 : gramRows84 = frameColumns.map (Rows.dot frameColumns84) := by rfl

theorem eigen_residual_84 : residualColumns84 = (appliedColumns84.zip frameColumns84).map (fun pair => pair.1-pair.2*energies[84]!) := by rfl

theorem gram_error_84 : ((gramRows84.zip (List.ofFn (fun j : Fin 98 => if j=(84 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_84 : (residualColumns84.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_84 : hamiltonianRows84.length = 98 := by rfl
theorem frameRows_length_84 : frameRows84.length = 98 := by rfl
theorem frameColumns_length_84 : frameColumns84.length = 98 := by rfl
theorem appliedColumns_length_84 : appliedColumns84.length = 98 := by rfl
theorem gramRows_length_84 : gramRows84.length = 98 := by rfl
theorem residualColumns_length_84 : residualColumns84.length = 98 := by rfl

theorem original_row_85 : frameRows85 = originalRows[85]! := by rfl

theorem original_column_85 : frameColumns85 = originalRows.map (fun row => row[85]!) := by rfl

theorem original_hamiltonian_85 (j : Basis) : hamiltonianRows85[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (85 : Basis) j := by
  have previous := Upper.source_entries (85 : Basis) j
  have restore : hamiltonianRows85[j.val]! = (if j=(85 : Basis) then 3150000000000000 else 0)-Upper.numerator (85 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_85 : appliedColumns85 = hamiltonianRows.map (fun row => Rows.dot row frameColumns85) := by rfl

theorem gram_row_85 : gramRows85 = frameColumns.map (Rows.dot frameColumns85) := by rfl

theorem eigen_residual_85 : residualColumns85 = (appliedColumns85.zip frameColumns85).map (fun pair => pair.1-pair.2*energies[85]!) := by rfl

theorem gram_error_85 : ((gramRows85.zip (List.ofFn (fun j : Fin 98 => if j=(85 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_85 : (residualColumns85.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_85 : hamiltonianRows85.length = 98 := by rfl
theorem frameRows_length_85 : frameRows85.length = 98 := by rfl
theorem frameColumns_length_85 : frameColumns85.length = 98 := by rfl
theorem appliedColumns_length_85 : appliedColumns85.length = 98 := by rfl
theorem gramRows_length_85 : gramRows85.length = 98 := by rfl
theorem residualColumns_length_85 : residualColumns85.length = 98 := by rfl

theorem original_row_86 : frameRows86 = originalRows[86]! := by rfl

theorem original_column_86 : frameColumns86 = originalRows.map (fun row => row[86]!) := by rfl

theorem original_hamiltonian_86 (j : Basis) : hamiltonianRows86[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (86 : Basis) j := by
  have previous := Upper.source_entries (86 : Basis) j
  have restore : hamiltonianRows86[j.val]! = (if j=(86 : Basis) then 3150000000000000 else 0)-Upper.numerator (86 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_86 : appliedColumns86 = hamiltonianRows.map (fun row => Rows.dot row frameColumns86) := by rfl

theorem gram_row_86 : gramRows86 = frameColumns.map (Rows.dot frameColumns86) := by rfl

theorem eigen_residual_86 : residualColumns86 = (appliedColumns86.zip frameColumns86).map (fun pair => pair.1-pair.2*energies[86]!) := by rfl

theorem gram_error_86 : ((gramRows86.zip (List.ofFn (fun j : Fin 98 => if j=(86 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_86 : (residualColumns86.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_86 : hamiltonianRows86.length = 98 := by rfl
theorem frameRows_length_86 : frameRows86.length = 98 := by rfl
theorem frameColumns_length_86 : frameColumns86.length = 98 := by rfl
theorem appliedColumns_length_86 : appliedColumns86.length = 98 := by rfl
theorem gramRows_length_86 : gramRows86.length = 98 := by rfl
theorem residualColumns_length_86 : residualColumns86.length = 98 := by rfl

theorem original_row_87 : frameRows87 = originalRows[87]! := by rfl

theorem original_column_87 : frameColumns87 = originalRows.map (fun row => row[87]!) := by rfl

theorem original_hamiltonian_87 (j : Basis) : hamiltonianRows87[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (87 : Basis) j := by
  have previous := Upper.source_entries (87 : Basis) j
  have restore : hamiltonianRows87[j.val]! = (if j=(87 : Basis) then 3150000000000000 else 0)-Upper.numerator (87 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_87 : appliedColumns87 = hamiltonianRows.map (fun row => Rows.dot row frameColumns87) := by rfl

theorem gram_row_87 : gramRows87 = frameColumns.map (Rows.dot frameColumns87) := by rfl

theorem eigen_residual_87 : residualColumns87 = (appliedColumns87.zip frameColumns87).map (fun pair => pair.1-pair.2*energies[87]!) := by rfl

theorem gram_error_87 : ((gramRows87.zip (List.ofFn (fun j : Fin 98 => if j=(87 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_87 : (residualColumns87.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_87 : hamiltonianRows87.length = 98 := by rfl
theorem frameRows_length_87 : frameRows87.length = 98 := by rfl
theorem frameColumns_length_87 : frameColumns87.length = 98 := by rfl
theorem appliedColumns_length_87 : appliedColumns87.length = 98 := by rfl
theorem gramRows_length_87 : gramRows87.length = 98 := by rfl
theorem residualColumns_length_87 : residualColumns87.length = 98 := by rfl

theorem original_row_88 : frameRows88 = originalRows[88]! := by rfl

theorem original_column_88 : frameColumns88 = originalRows.map (fun row => row[88]!) := by rfl

theorem original_hamiltonian_88 (j : Basis) : hamiltonianRows88[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (88 : Basis) j := by
  have previous := Upper.source_entries (88 : Basis) j
  have restore : hamiltonianRows88[j.val]! = (if j=(88 : Basis) then 3150000000000000 else 0)-Upper.numerator (88 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_88 : appliedColumns88 = hamiltonianRows.map (fun row => Rows.dot row frameColumns88) := by rfl

theorem gram_row_88 : gramRows88 = frameColumns.map (Rows.dot frameColumns88) := by rfl

theorem eigen_residual_88 : residualColumns88 = (appliedColumns88.zip frameColumns88).map (fun pair => pair.1-pair.2*energies[88]!) := by rfl

theorem gram_error_88 : ((gramRows88.zip (List.ofFn (fun j : Fin 98 => if j=(88 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_88 : (residualColumns88.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_88 : hamiltonianRows88.length = 98 := by rfl
theorem frameRows_length_88 : frameRows88.length = 98 := by rfl
theorem frameColumns_length_88 : frameColumns88.length = 98 := by rfl
theorem appliedColumns_length_88 : appliedColumns88.length = 98 := by rfl
theorem gramRows_length_88 : gramRows88.length = 98 := by rfl
theorem residualColumns_length_88 : residualColumns88.length = 98 := by rfl

theorem original_row_89 : frameRows89 = originalRows[89]! := by rfl

theorem original_column_89 : frameColumns89 = originalRows.map (fun row => row[89]!) := by rfl

theorem original_hamiltonian_89 (j : Basis) : hamiltonianRows89[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (89 : Basis) j := by
  have previous := Upper.source_entries (89 : Basis) j
  have restore : hamiltonianRows89[j.val]! = (if j=(89 : Basis) then 3150000000000000 else 0)-Upper.numerator (89 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_89 : appliedColumns89 = hamiltonianRows.map (fun row => Rows.dot row frameColumns89) := by rfl

theorem gram_row_89 : gramRows89 = frameColumns.map (Rows.dot frameColumns89) := by rfl

theorem eigen_residual_89 : residualColumns89 = (appliedColumns89.zip frameColumns89).map (fun pair => pair.1-pair.2*energies[89]!) := by rfl

theorem gram_error_89 : ((gramRows89.zip (List.ofFn (fun j : Fin 98 => if j=(89 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_89 : (residualColumns89.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_89 : hamiltonianRows89.length = 98 := by rfl
theorem frameRows_length_89 : frameRows89.length = 98 := by rfl
theorem frameColumns_length_89 : frameColumns89.length = 98 := by rfl
theorem appliedColumns_length_89 : appliedColumns89.length = 98 := by rfl
theorem gramRows_length_89 : gramRows89.length = 98 := by rfl
theorem residualColumns_length_89 : residualColumns89.length = 98 := by rfl

theorem original_row_90 : frameRows90 = originalRows[90]! := by rfl

theorem original_column_90 : frameColumns90 = originalRows.map (fun row => row[90]!) := by rfl

theorem original_hamiltonian_90 (j : Basis) : hamiltonianRows90[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (90 : Basis) j := by
  have previous := Upper.source_entries (90 : Basis) j
  have restore : hamiltonianRows90[j.val]! = (if j=(90 : Basis) then 3150000000000000 else 0)-Upper.numerator (90 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_90 : appliedColumns90 = hamiltonianRows.map (fun row => Rows.dot row frameColumns90) := by rfl

theorem gram_row_90 : gramRows90 = frameColumns.map (Rows.dot frameColumns90) := by rfl

theorem eigen_residual_90 : residualColumns90 = (appliedColumns90.zip frameColumns90).map (fun pair => pair.1-pair.2*energies[90]!) := by rfl

theorem gram_error_90 : ((gramRows90.zip (List.ofFn (fun j : Fin 98 => if j=(90 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_90 : (residualColumns90.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_90 : hamiltonianRows90.length = 98 := by rfl
theorem frameRows_length_90 : frameRows90.length = 98 := by rfl
theorem frameColumns_length_90 : frameColumns90.length = 98 := by rfl
theorem appliedColumns_length_90 : appliedColumns90.length = 98 := by rfl
theorem gramRows_length_90 : gramRows90.length = 98 := by rfl
theorem residualColumns_length_90 : residualColumns90.length = 98 := by rfl

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
