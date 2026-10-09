import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Data
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Upper.Assembly

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
open Spectral Propagation.Interface

theorem original_row_35 : frameRows35 = originalRows[35]! := by rfl

theorem original_column_35 : frameColumns35 = originalRows.map (fun row => row[35]!) := by rfl

theorem original_hamiltonian_35 (j : Basis) : hamiltonianRows35[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (35 : Basis) j := by
  have previous := Upper.source_entries (35 : Basis) j
  have restore : hamiltonianRows35[j.val]! = (if j=(35 : Basis) then 3150000000000000 else 0)-Upper.numerator (35 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_35 : appliedColumns35 = hamiltonianRows.map (fun row => Rows.dot row frameColumns35) := by rfl

theorem gram_row_35 : gramRows35 = frameColumns.map (Rows.dot frameColumns35) := by rfl

theorem eigen_residual_35 : residualColumns35 = (appliedColumns35.zip frameColumns35).map (fun pair => pair.1-pair.2*energies[35]!) := by rfl

theorem gram_error_35 : ((gramRows35.zip (List.ofFn (fun j : Fin 98 => if j=(35 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_35 : (residualColumns35.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_35 : hamiltonianRows35.length = 98 := by rfl
theorem frameRows_length_35 : frameRows35.length = 98 := by rfl
theorem frameColumns_length_35 : frameColumns35.length = 98 := by rfl
theorem appliedColumns_length_35 : appliedColumns35.length = 98 := by rfl
theorem gramRows_length_35 : gramRows35.length = 98 := by rfl
theorem residualColumns_length_35 : residualColumns35.length = 98 := by rfl

theorem original_row_36 : frameRows36 = originalRows[36]! := by rfl

theorem original_column_36 : frameColumns36 = originalRows.map (fun row => row[36]!) := by rfl

theorem original_hamiltonian_36 (j : Basis) : hamiltonianRows36[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (36 : Basis) j := by
  have previous := Upper.source_entries (36 : Basis) j
  have restore : hamiltonianRows36[j.val]! = (if j=(36 : Basis) then 3150000000000000 else 0)-Upper.numerator (36 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_36 : appliedColumns36 = hamiltonianRows.map (fun row => Rows.dot row frameColumns36) := by rfl

theorem gram_row_36 : gramRows36 = frameColumns.map (Rows.dot frameColumns36) := by rfl

theorem eigen_residual_36 : residualColumns36 = (appliedColumns36.zip frameColumns36).map (fun pair => pair.1-pair.2*energies[36]!) := by rfl

theorem gram_error_36 : ((gramRows36.zip (List.ofFn (fun j : Fin 98 => if j=(36 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_36 : (residualColumns36.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_36 : hamiltonianRows36.length = 98 := by rfl
theorem frameRows_length_36 : frameRows36.length = 98 := by rfl
theorem frameColumns_length_36 : frameColumns36.length = 98 := by rfl
theorem appliedColumns_length_36 : appliedColumns36.length = 98 := by rfl
theorem gramRows_length_36 : gramRows36.length = 98 := by rfl
theorem residualColumns_length_36 : residualColumns36.length = 98 := by rfl

theorem original_row_37 : frameRows37 = originalRows[37]! := by rfl

theorem original_column_37 : frameColumns37 = originalRows.map (fun row => row[37]!) := by rfl

theorem original_hamiltonian_37 (j : Basis) : hamiltonianRows37[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (37 : Basis) j := by
  have previous := Upper.source_entries (37 : Basis) j
  have restore : hamiltonianRows37[j.val]! = (if j=(37 : Basis) then 3150000000000000 else 0)-Upper.numerator (37 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_37 : appliedColumns37 = hamiltonianRows.map (fun row => Rows.dot row frameColumns37) := by rfl

theorem gram_row_37 : gramRows37 = frameColumns.map (Rows.dot frameColumns37) := by rfl

theorem eigen_residual_37 : residualColumns37 = (appliedColumns37.zip frameColumns37).map (fun pair => pair.1-pair.2*energies[37]!) := by rfl

theorem gram_error_37 : ((gramRows37.zip (List.ofFn (fun j : Fin 98 => if j=(37 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_37 : (residualColumns37.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_37 : hamiltonianRows37.length = 98 := by rfl
theorem frameRows_length_37 : frameRows37.length = 98 := by rfl
theorem frameColumns_length_37 : frameColumns37.length = 98 := by rfl
theorem appliedColumns_length_37 : appliedColumns37.length = 98 := by rfl
theorem gramRows_length_37 : gramRows37.length = 98 := by rfl
theorem residualColumns_length_37 : residualColumns37.length = 98 := by rfl

theorem original_row_38 : frameRows38 = originalRows[38]! := by rfl

theorem original_column_38 : frameColumns38 = originalRows.map (fun row => row[38]!) := by rfl

theorem original_hamiltonian_38 (j : Basis) : hamiltonianRows38[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (38 : Basis) j := by
  have previous := Upper.source_entries (38 : Basis) j
  have restore : hamiltonianRows38[j.val]! = (if j=(38 : Basis) then 3150000000000000 else 0)-Upper.numerator (38 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_38 : appliedColumns38 = hamiltonianRows.map (fun row => Rows.dot row frameColumns38) := by rfl

theorem gram_row_38 : gramRows38 = frameColumns.map (Rows.dot frameColumns38) := by rfl

theorem eigen_residual_38 : residualColumns38 = (appliedColumns38.zip frameColumns38).map (fun pair => pair.1-pair.2*energies[38]!) := by rfl

theorem gram_error_38 : ((gramRows38.zip (List.ofFn (fun j : Fin 98 => if j=(38 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_38 : (residualColumns38.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_38 : hamiltonianRows38.length = 98 := by rfl
theorem frameRows_length_38 : frameRows38.length = 98 := by rfl
theorem frameColumns_length_38 : frameColumns38.length = 98 := by rfl
theorem appliedColumns_length_38 : appliedColumns38.length = 98 := by rfl
theorem gramRows_length_38 : gramRows38.length = 98 := by rfl
theorem residualColumns_length_38 : residualColumns38.length = 98 := by rfl

theorem original_row_39 : frameRows39 = originalRows[39]! := by rfl

theorem original_column_39 : frameColumns39 = originalRows.map (fun row => row[39]!) := by rfl

theorem original_hamiltonian_39 (j : Basis) : hamiltonianRows39[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (39 : Basis) j := by
  have previous := Upper.source_entries (39 : Basis) j
  have restore : hamiltonianRows39[j.val]! = (if j=(39 : Basis) then 3150000000000000 else 0)-Upper.numerator (39 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_39 : appliedColumns39 = hamiltonianRows.map (fun row => Rows.dot row frameColumns39) := by rfl

theorem gram_row_39 : gramRows39 = frameColumns.map (Rows.dot frameColumns39) := by rfl

theorem eigen_residual_39 : residualColumns39 = (appliedColumns39.zip frameColumns39).map (fun pair => pair.1-pair.2*energies[39]!) := by rfl

theorem gram_error_39 : ((gramRows39.zip (List.ofFn (fun j : Fin 98 => if j=(39 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_39 : (residualColumns39.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_39 : hamiltonianRows39.length = 98 := by rfl
theorem frameRows_length_39 : frameRows39.length = 98 := by rfl
theorem frameColumns_length_39 : frameColumns39.length = 98 := by rfl
theorem appliedColumns_length_39 : appliedColumns39.length = 98 := by rfl
theorem gramRows_length_39 : gramRows39.length = 98 := by rfl
theorem residualColumns_length_39 : residualColumns39.length = 98 := by rfl

theorem original_row_40 : frameRows40 = originalRows[40]! := by rfl

theorem original_column_40 : frameColumns40 = originalRows.map (fun row => row[40]!) := by rfl

theorem original_hamiltonian_40 (j : Basis) : hamiltonianRows40[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (40 : Basis) j := by
  have previous := Upper.source_entries (40 : Basis) j
  have restore : hamiltonianRows40[j.val]! = (if j=(40 : Basis) then 3150000000000000 else 0)-Upper.numerator (40 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_40 : appliedColumns40 = hamiltonianRows.map (fun row => Rows.dot row frameColumns40) := by rfl

theorem gram_row_40 : gramRows40 = frameColumns.map (Rows.dot frameColumns40) := by rfl

theorem eigen_residual_40 : residualColumns40 = (appliedColumns40.zip frameColumns40).map (fun pair => pair.1-pair.2*energies[40]!) := by rfl

theorem gram_error_40 : ((gramRows40.zip (List.ofFn (fun j : Fin 98 => if j=(40 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_40 : (residualColumns40.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_40 : hamiltonianRows40.length = 98 := by rfl
theorem frameRows_length_40 : frameRows40.length = 98 := by rfl
theorem frameColumns_length_40 : frameColumns40.length = 98 := by rfl
theorem appliedColumns_length_40 : appliedColumns40.length = 98 := by rfl
theorem gramRows_length_40 : gramRows40.length = 98 := by rfl
theorem residualColumns_length_40 : residualColumns40.length = 98 := by rfl

theorem original_row_41 : frameRows41 = originalRows[41]! := by rfl

theorem original_column_41 : frameColumns41 = originalRows.map (fun row => row[41]!) := by rfl

theorem original_hamiltonian_41 (j : Basis) : hamiltonianRows41[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (41 : Basis) j := by
  have previous := Upper.source_entries (41 : Basis) j
  have restore : hamiltonianRows41[j.val]! = (if j=(41 : Basis) then 3150000000000000 else 0)-Upper.numerator (41 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_41 : appliedColumns41 = hamiltonianRows.map (fun row => Rows.dot row frameColumns41) := by rfl

theorem gram_row_41 : gramRows41 = frameColumns.map (Rows.dot frameColumns41) := by rfl

theorem eigen_residual_41 : residualColumns41 = (appliedColumns41.zip frameColumns41).map (fun pair => pair.1-pair.2*energies[41]!) := by rfl

theorem gram_error_41 : ((gramRows41.zip (List.ofFn (fun j : Fin 98 => if j=(41 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_41 : (residualColumns41.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_41 : hamiltonianRows41.length = 98 := by rfl
theorem frameRows_length_41 : frameRows41.length = 98 := by rfl
theorem frameColumns_length_41 : frameColumns41.length = 98 := by rfl
theorem appliedColumns_length_41 : appliedColumns41.length = 98 := by rfl
theorem gramRows_length_41 : gramRows41.length = 98 := by rfl
theorem residualColumns_length_41 : residualColumns41.length = 98 := by rfl

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
