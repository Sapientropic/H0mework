import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Data
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Upper.Assembly

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
open Spectral Propagation.Interface

theorem original_row_49 : frameRows49 = originalRows[49]! := by rfl

theorem original_column_49 : frameColumns49 = originalRows.map (fun row => row[49]!) := by rfl

theorem original_hamiltonian_49 (j : Basis) : hamiltonianRows49[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (49 : Basis) j := by
  have previous := Upper.source_entries (49 : Basis) j
  have restore : hamiltonianRows49[j.val]! = (if j=(49 : Basis) then 3150000000000000 else 0)-Upper.numerator (49 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_49 : appliedColumns49 = hamiltonianRows.map (fun row => Rows.dot row frameColumns49) := by rfl

theorem gram_row_49 : gramRows49 = frameColumns.map (Rows.dot frameColumns49) := by rfl

theorem eigen_residual_49 : residualColumns49 = (appliedColumns49.zip frameColumns49).map (fun pair => pair.1-pair.2*energies[49]!) := by rfl

theorem gram_error_49 : ((gramRows49.zip (List.ofFn (fun j : Fin 98 => if j=(49 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_49 : (residualColumns49.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_49 : hamiltonianRows49.length = 98 := by rfl
theorem frameRows_length_49 : frameRows49.length = 98 := by rfl
theorem frameColumns_length_49 : frameColumns49.length = 98 := by rfl
theorem appliedColumns_length_49 : appliedColumns49.length = 98 := by rfl
theorem gramRows_length_49 : gramRows49.length = 98 := by rfl
theorem residualColumns_length_49 : residualColumns49.length = 98 := by rfl

theorem original_row_50 : frameRows50 = originalRows[50]! := by rfl

theorem original_column_50 : frameColumns50 = originalRows.map (fun row => row[50]!) := by rfl

theorem original_hamiltonian_50 (j : Basis) : hamiltonianRows50[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (50 : Basis) j := by
  have previous := Upper.source_entries (50 : Basis) j
  have restore : hamiltonianRows50[j.val]! = (if j=(50 : Basis) then 3150000000000000 else 0)-Upper.numerator (50 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_50 : appliedColumns50 = hamiltonianRows.map (fun row => Rows.dot row frameColumns50) := by rfl

theorem gram_row_50 : gramRows50 = frameColumns.map (Rows.dot frameColumns50) := by rfl

theorem eigen_residual_50 : residualColumns50 = (appliedColumns50.zip frameColumns50).map (fun pair => pair.1-pair.2*energies[50]!) := by rfl

theorem gram_error_50 : ((gramRows50.zip (List.ofFn (fun j : Fin 98 => if j=(50 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_50 : (residualColumns50.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_50 : hamiltonianRows50.length = 98 := by rfl
theorem frameRows_length_50 : frameRows50.length = 98 := by rfl
theorem frameColumns_length_50 : frameColumns50.length = 98 := by rfl
theorem appliedColumns_length_50 : appliedColumns50.length = 98 := by rfl
theorem gramRows_length_50 : gramRows50.length = 98 := by rfl
theorem residualColumns_length_50 : residualColumns50.length = 98 := by rfl

theorem original_row_51 : frameRows51 = originalRows[51]! := by rfl

theorem original_column_51 : frameColumns51 = originalRows.map (fun row => row[51]!) := by rfl

theorem original_hamiltonian_51 (j : Basis) : hamiltonianRows51[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (51 : Basis) j := by
  have previous := Upper.source_entries (51 : Basis) j
  have restore : hamiltonianRows51[j.val]! = (if j=(51 : Basis) then 3150000000000000 else 0)-Upper.numerator (51 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_51 : appliedColumns51 = hamiltonianRows.map (fun row => Rows.dot row frameColumns51) := by rfl

theorem gram_row_51 : gramRows51 = frameColumns.map (Rows.dot frameColumns51) := by rfl

theorem eigen_residual_51 : residualColumns51 = (appliedColumns51.zip frameColumns51).map (fun pair => pair.1-pair.2*energies[51]!) := by rfl

theorem gram_error_51 : ((gramRows51.zip (List.ofFn (fun j : Fin 98 => if j=(51 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_51 : (residualColumns51.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_51 : hamiltonianRows51.length = 98 := by rfl
theorem frameRows_length_51 : frameRows51.length = 98 := by rfl
theorem frameColumns_length_51 : frameColumns51.length = 98 := by rfl
theorem appliedColumns_length_51 : appliedColumns51.length = 98 := by rfl
theorem gramRows_length_51 : gramRows51.length = 98 := by rfl
theorem residualColumns_length_51 : residualColumns51.length = 98 := by rfl

theorem original_row_52 : frameRows52 = originalRows[52]! := by rfl

theorem original_column_52 : frameColumns52 = originalRows.map (fun row => row[52]!) := by rfl

theorem original_hamiltonian_52 (j : Basis) : hamiltonianRows52[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (52 : Basis) j := by
  have previous := Upper.source_entries (52 : Basis) j
  have restore : hamiltonianRows52[j.val]! = (if j=(52 : Basis) then 3150000000000000 else 0)-Upper.numerator (52 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_52 : appliedColumns52 = hamiltonianRows.map (fun row => Rows.dot row frameColumns52) := by rfl

theorem gram_row_52 : gramRows52 = frameColumns.map (Rows.dot frameColumns52) := by rfl

theorem eigen_residual_52 : residualColumns52 = (appliedColumns52.zip frameColumns52).map (fun pair => pair.1-pair.2*energies[52]!) := by rfl

theorem gram_error_52 : ((gramRows52.zip (List.ofFn (fun j : Fin 98 => if j=(52 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_52 : (residualColumns52.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_52 : hamiltonianRows52.length = 98 := by rfl
theorem frameRows_length_52 : frameRows52.length = 98 := by rfl
theorem frameColumns_length_52 : frameColumns52.length = 98 := by rfl
theorem appliedColumns_length_52 : appliedColumns52.length = 98 := by rfl
theorem gramRows_length_52 : gramRows52.length = 98 := by rfl
theorem residualColumns_length_52 : residualColumns52.length = 98 := by rfl

theorem original_row_53 : frameRows53 = originalRows[53]! := by rfl

theorem original_column_53 : frameColumns53 = originalRows.map (fun row => row[53]!) := by rfl

theorem original_hamiltonian_53 (j : Basis) : hamiltonianRows53[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (53 : Basis) j := by
  have previous := Upper.source_entries (53 : Basis) j
  have restore : hamiltonianRows53[j.val]! = (if j=(53 : Basis) then 3150000000000000 else 0)-Upper.numerator (53 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_53 : appliedColumns53 = hamiltonianRows.map (fun row => Rows.dot row frameColumns53) := by rfl

theorem gram_row_53 : gramRows53 = frameColumns.map (Rows.dot frameColumns53) := by rfl

theorem eigen_residual_53 : residualColumns53 = (appliedColumns53.zip frameColumns53).map (fun pair => pair.1-pair.2*energies[53]!) := by rfl

theorem gram_error_53 : ((gramRows53.zip (List.ofFn (fun j : Fin 98 => if j=(53 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_53 : (residualColumns53.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_53 : hamiltonianRows53.length = 98 := by rfl
theorem frameRows_length_53 : frameRows53.length = 98 := by rfl
theorem frameColumns_length_53 : frameColumns53.length = 98 := by rfl
theorem appliedColumns_length_53 : appliedColumns53.length = 98 := by rfl
theorem gramRows_length_53 : gramRows53.length = 98 := by rfl
theorem residualColumns_length_53 : residualColumns53.length = 98 := by rfl

theorem original_row_54 : frameRows54 = originalRows[54]! := by rfl

theorem original_column_54 : frameColumns54 = originalRows.map (fun row => row[54]!) := by rfl

theorem original_hamiltonian_54 (j : Basis) : hamiltonianRows54[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (54 : Basis) j := by
  have previous := Upper.source_entries (54 : Basis) j
  have restore : hamiltonianRows54[j.val]! = (if j=(54 : Basis) then 3150000000000000 else 0)-Upper.numerator (54 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_54 : appliedColumns54 = hamiltonianRows.map (fun row => Rows.dot row frameColumns54) := by rfl

theorem gram_row_54 : gramRows54 = frameColumns.map (Rows.dot frameColumns54) := by rfl

theorem eigen_residual_54 : residualColumns54 = (appliedColumns54.zip frameColumns54).map (fun pair => pair.1-pair.2*energies[54]!) := by rfl

theorem gram_error_54 : ((gramRows54.zip (List.ofFn (fun j : Fin 98 => if j=(54 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_54 : (residualColumns54.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_54 : hamiltonianRows54.length = 98 := by rfl
theorem frameRows_length_54 : frameRows54.length = 98 := by rfl
theorem frameColumns_length_54 : frameColumns54.length = 98 := by rfl
theorem appliedColumns_length_54 : appliedColumns54.length = 98 := by rfl
theorem gramRows_length_54 : gramRows54.length = 98 := by rfl
theorem residualColumns_length_54 : residualColumns54.length = 98 := by rfl

theorem original_row_55 : frameRows55 = originalRows[55]! := by rfl

theorem original_column_55 : frameColumns55 = originalRows.map (fun row => row[55]!) := by rfl

theorem original_hamiltonian_55 (j : Basis) : hamiltonianRows55[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (55 : Basis) j := by
  have previous := Upper.source_entries (55 : Basis) j
  have restore : hamiltonianRows55[j.val]! = (if j=(55 : Basis) then 3150000000000000 else 0)-Upper.numerator (55 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_55 : appliedColumns55 = hamiltonianRows.map (fun row => Rows.dot row frameColumns55) := by rfl

theorem gram_row_55 : gramRows55 = frameColumns.map (Rows.dot frameColumns55) := by rfl

theorem eigen_residual_55 : residualColumns55 = (appliedColumns55.zip frameColumns55).map (fun pair => pair.1-pair.2*energies[55]!) := by rfl

theorem gram_error_55 : ((gramRows55.zip (List.ofFn (fun j : Fin 98 => if j=(55 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_55 : (residualColumns55.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_55 : hamiltonianRows55.length = 98 := by rfl
theorem frameRows_length_55 : frameRows55.length = 98 := by rfl
theorem frameColumns_length_55 : frameColumns55.length = 98 := by rfl
theorem appliedColumns_length_55 : appliedColumns55.length = 98 := by rfl
theorem gramRows_length_55 : gramRows55.length = 98 := by rfl
theorem residualColumns_length_55 : residualColumns55.length = 98 := by rfl

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
