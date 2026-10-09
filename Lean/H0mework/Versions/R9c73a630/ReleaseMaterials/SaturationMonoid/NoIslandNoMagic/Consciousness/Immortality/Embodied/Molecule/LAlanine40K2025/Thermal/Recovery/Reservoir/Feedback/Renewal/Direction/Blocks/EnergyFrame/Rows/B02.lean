import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Data
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Upper.Assembly

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
open Spectral Propagation.Interface

theorem original_row_14 : frameRows14 = originalRows[14]! := by rfl

theorem original_column_14 : frameColumns14 = originalRows.map (fun row => row[14]!) := by rfl

theorem original_hamiltonian_14 (j : Basis) : hamiltonianRows14[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (14 : Basis) j := by
  have previous := Upper.source_entries (14 : Basis) j
  have restore : hamiltonianRows14[j.val]! = (if j=(14 : Basis) then 3150000000000000 else 0)-Upper.numerator (14 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_14 : appliedColumns14 = hamiltonianRows.map (fun row => Rows.dot row frameColumns14) := by rfl

theorem gram_row_14 : gramRows14 = frameColumns.map (Rows.dot frameColumns14) := by rfl

theorem eigen_residual_14 : residualColumns14 = (appliedColumns14.zip frameColumns14).map (fun pair => pair.1-pair.2*energies[14]!) := by rfl

theorem gram_error_14 : ((gramRows14.zip (List.ofFn (fun j : Fin 98 => if j=(14 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_14 : (residualColumns14.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_14 : hamiltonianRows14.length = 98 := by rfl
theorem frameRows_length_14 : frameRows14.length = 98 := by rfl
theorem frameColumns_length_14 : frameColumns14.length = 98 := by rfl
theorem appliedColumns_length_14 : appliedColumns14.length = 98 := by rfl
theorem gramRows_length_14 : gramRows14.length = 98 := by rfl
theorem residualColumns_length_14 : residualColumns14.length = 98 := by rfl

theorem original_row_15 : frameRows15 = originalRows[15]! := by rfl

theorem original_column_15 : frameColumns15 = originalRows.map (fun row => row[15]!) := by rfl

theorem original_hamiltonian_15 (j : Basis) : hamiltonianRows15[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (15 : Basis) j := by
  have previous := Upper.source_entries (15 : Basis) j
  have restore : hamiltonianRows15[j.val]! = (if j=(15 : Basis) then 3150000000000000 else 0)-Upper.numerator (15 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_15 : appliedColumns15 = hamiltonianRows.map (fun row => Rows.dot row frameColumns15) := by rfl

theorem gram_row_15 : gramRows15 = frameColumns.map (Rows.dot frameColumns15) := by rfl

theorem eigen_residual_15 : residualColumns15 = (appliedColumns15.zip frameColumns15).map (fun pair => pair.1-pair.2*energies[15]!) := by rfl

theorem gram_error_15 : ((gramRows15.zip (List.ofFn (fun j : Fin 98 => if j=(15 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_15 : (residualColumns15.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_15 : hamiltonianRows15.length = 98 := by rfl
theorem frameRows_length_15 : frameRows15.length = 98 := by rfl
theorem frameColumns_length_15 : frameColumns15.length = 98 := by rfl
theorem appliedColumns_length_15 : appliedColumns15.length = 98 := by rfl
theorem gramRows_length_15 : gramRows15.length = 98 := by rfl
theorem residualColumns_length_15 : residualColumns15.length = 98 := by rfl

theorem original_row_16 : frameRows16 = originalRows[16]! := by rfl

theorem original_column_16 : frameColumns16 = originalRows.map (fun row => row[16]!) := by rfl

theorem original_hamiltonian_16 (j : Basis) : hamiltonianRows16[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (16 : Basis) j := by
  have previous := Upper.source_entries (16 : Basis) j
  have restore : hamiltonianRows16[j.val]! = (if j=(16 : Basis) then 3150000000000000 else 0)-Upper.numerator (16 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_16 : appliedColumns16 = hamiltonianRows.map (fun row => Rows.dot row frameColumns16) := by rfl

theorem gram_row_16 : gramRows16 = frameColumns.map (Rows.dot frameColumns16) := by rfl

theorem eigen_residual_16 : residualColumns16 = (appliedColumns16.zip frameColumns16).map (fun pair => pair.1-pair.2*energies[16]!) := by rfl

theorem gram_error_16 : ((gramRows16.zip (List.ofFn (fun j : Fin 98 => if j=(16 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_16 : (residualColumns16.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_16 : hamiltonianRows16.length = 98 := by rfl
theorem frameRows_length_16 : frameRows16.length = 98 := by rfl
theorem frameColumns_length_16 : frameColumns16.length = 98 := by rfl
theorem appliedColumns_length_16 : appliedColumns16.length = 98 := by rfl
theorem gramRows_length_16 : gramRows16.length = 98 := by rfl
theorem residualColumns_length_16 : residualColumns16.length = 98 := by rfl

theorem original_row_17 : frameRows17 = originalRows[17]! := by rfl

theorem original_column_17 : frameColumns17 = originalRows.map (fun row => row[17]!) := by rfl

theorem original_hamiltonian_17 (j : Basis) : hamiltonianRows17[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (17 : Basis) j := by
  have previous := Upper.source_entries (17 : Basis) j
  have restore : hamiltonianRows17[j.val]! = (if j=(17 : Basis) then 3150000000000000 else 0)-Upper.numerator (17 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_17 : appliedColumns17 = hamiltonianRows.map (fun row => Rows.dot row frameColumns17) := by rfl

theorem gram_row_17 : gramRows17 = frameColumns.map (Rows.dot frameColumns17) := by rfl

theorem eigen_residual_17 : residualColumns17 = (appliedColumns17.zip frameColumns17).map (fun pair => pair.1-pair.2*energies[17]!) := by rfl

theorem gram_error_17 : ((gramRows17.zip (List.ofFn (fun j : Fin 98 => if j=(17 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_17 : (residualColumns17.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_17 : hamiltonianRows17.length = 98 := by rfl
theorem frameRows_length_17 : frameRows17.length = 98 := by rfl
theorem frameColumns_length_17 : frameColumns17.length = 98 := by rfl
theorem appliedColumns_length_17 : appliedColumns17.length = 98 := by rfl
theorem gramRows_length_17 : gramRows17.length = 98 := by rfl
theorem residualColumns_length_17 : residualColumns17.length = 98 := by rfl

theorem original_row_18 : frameRows18 = originalRows[18]! := by rfl

theorem original_column_18 : frameColumns18 = originalRows.map (fun row => row[18]!) := by rfl

theorem original_hamiltonian_18 (j : Basis) : hamiltonianRows18[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (18 : Basis) j := by
  have previous := Upper.source_entries (18 : Basis) j
  have restore : hamiltonianRows18[j.val]! = (if j=(18 : Basis) then 3150000000000000 else 0)-Upper.numerator (18 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_18 : appliedColumns18 = hamiltonianRows.map (fun row => Rows.dot row frameColumns18) := by rfl

theorem gram_row_18 : gramRows18 = frameColumns.map (Rows.dot frameColumns18) := by rfl

theorem eigen_residual_18 : residualColumns18 = (appliedColumns18.zip frameColumns18).map (fun pair => pair.1-pair.2*energies[18]!) := by rfl

theorem gram_error_18 : ((gramRows18.zip (List.ofFn (fun j : Fin 98 => if j=(18 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_18 : (residualColumns18.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_18 : hamiltonianRows18.length = 98 := by rfl
theorem frameRows_length_18 : frameRows18.length = 98 := by rfl
theorem frameColumns_length_18 : frameColumns18.length = 98 := by rfl
theorem appliedColumns_length_18 : appliedColumns18.length = 98 := by rfl
theorem gramRows_length_18 : gramRows18.length = 98 := by rfl
theorem residualColumns_length_18 : residualColumns18.length = 98 := by rfl

theorem original_row_19 : frameRows19 = originalRows[19]! := by rfl

theorem original_column_19 : frameColumns19 = originalRows.map (fun row => row[19]!) := by rfl

theorem original_hamiltonian_19 (j : Basis) : hamiltonianRows19[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (19 : Basis) j := by
  have previous := Upper.source_entries (19 : Basis) j
  have restore : hamiltonianRows19[j.val]! = (if j=(19 : Basis) then 3150000000000000 else 0)-Upper.numerator (19 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_19 : appliedColumns19 = hamiltonianRows.map (fun row => Rows.dot row frameColumns19) := by rfl

theorem gram_row_19 : gramRows19 = frameColumns.map (Rows.dot frameColumns19) := by rfl

theorem eigen_residual_19 : residualColumns19 = (appliedColumns19.zip frameColumns19).map (fun pair => pair.1-pair.2*energies[19]!) := by rfl

theorem gram_error_19 : ((gramRows19.zip (List.ofFn (fun j : Fin 98 => if j=(19 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_19 : (residualColumns19.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_19 : hamiltonianRows19.length = 98 := by rfl
theorem frameRows_length_19 : frameRows19.length = 98 := by rfl
theorem frameColumns_length_19 : frameColumns19.length = 98 := by rfl
theorem appliedColumns_length_19 : appliedColumns19.length = 98 := by rfl
theorem gramRows_length_19 : gramRows19.length = 98 := by rfl
theorem residualColumns_length_19 : residualColumns19.length = 98 := by rfl

theorem original_row_20 : frameRows20 = originalRows[20]! := by rfl

theorem original_column_20 : frameColumns20 = originalRows.map (fun row => row[20]!) := by rfl

theorem original_hamiltonian_20 (j : Basis) : hamiltonianRows20[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (20 : Basis) j := by
  have previous := Upper.source_entries (20 : Basis) j
  have restore : hamiltonianRows20[j.val]! = (if j=(20 : Basis) then 3150000000000000 else 0)-Upper.numerator (20 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_20 : appliedColumns20 = hamiltonianRows.map (fun row => Rows.dot row frameColumns20) := by rfl

theorem gram_row_20 : gramRows20 = frameColumns.map (Rows.dot frameColumns20) := by rfl

theorem eigen_residual_20 : residualColumns20 = (appliedColumns20.zip frameColumns20).map (fun pair => pair.1-pair.2*energies[20]!) := by rfl

theorem gram_error_20 : ((gramRows20.zip (List.ofFn (fun j : Fin 98 => if j=(20 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_20 : (residualColumns20.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_20 : hamiltonianRows20.length = 98 := by rfl
theorem frameRows_length_20 : frameRows20.length = 98 := by rfl
theorem frameColumns_length_20 : frameColumns20.length = 98 := by rfl
theorem appliedColumns_length_20 : appliedColumns20.length = 98 := by rfl
theorem gramRows_length_20 : gramRows20.length = 98 := by rfl
theorem residualColumns_length_20 : residualColumns20.length = 98 := by rfl

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
