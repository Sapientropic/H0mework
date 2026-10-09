import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Data
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Upper.Assembly

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
open Spectral Propagation.Interface

theorem original_row_42 : frameRows42 = originalRows[42]! := by rfl

theorem original_column_42 : frameColumns42 = originalRows.map (fun row => row[42]!) := by rfl

theorem original_hamiltonian_42 (j : Basis) : hamiltonianRows42[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (42 : Basis) j := by
  have previous := Upper.source_entries (42 : Basis) j
  have restore : hamiltonianRows42[j.val]! = (if j=(42 : Basis) then 3150000000000000 else 0)-Upper.numerator (42 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_42 : appliedColumns42 = hamiltonianRows.map (fun row => Rows.dot row frameColumns42) := by rfl

theorem gram_row_42 : gramRows42 = frameColumns.map (Rows.dot frameColumns42) := by rfl

theorem eigen_residual_42 : residualColumns42 = (appliedColumns42.zip frameColumns42).map (fun pair => pair.1-pair.2*energies[42]!) := by rfl

theorem gram_error_42 : ((gramRows42.zip (List.ofFn (fun j : Fin 98 => if j=(42 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_42 : (residualColumns42.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_42 : hamiltonianRows42.length = 98 := by rfl
theorem frameRows_length_42 : frameRows42.length = 98 := by rfl
theorem frameColumns_length_42 : frameColumns42.length = 98 := by rfl
theorem appliedColumns_length_42 : appliedColumns42.length = 98 := by rfl
theorem gramRows_length_42 : gramRows42.length = 98 := by rfl
theorem residualColumns_length_42 : residualColumns42.length = 98 := by rfl

theorem original_row_43 : frameRows43 = originalRows[43]! := by rfl

theorem original_column_43 : frameColumns43 = originalRows.map (fun row => row[43]!) := by rfl

theorem original_hamiltonian_43 (j : Basis) : hamiltonianRows43[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (43 : Basis) j := by
  have previous := Upper.source_entries (43 : Basis) j
  have restore : hamiltonianRows43[j.val]! = (if j=(43 : Basis) then 3150000000000000 else 0)-Upper.numerator (43 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_43 : appliedColumns43 = hamiltonianRows.map (fun row => Rows.dot row frameColumns43) := by rfl

theorem gram_row_43 : gramRows43 = frameColumns.map (Rows.dot frameColumns43) := by rfl

theorem eigen_residual_43 : residualColumns43 = (appliedColumns43.zip frameColumns43).map (fun pair => pair.1-pair.2*energies[43]!) := by rfl

theorem gram_error_43 : ((gramRows43.zip (List.ofFn (fun j : Fin 98 => if j=(43 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_43 : (residualColumns43.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_43 : hamiltonianRows43.length = 98 := by rfl
theorem frameRows_length_43 : frameRows43.length = 98 := by rfl
theorem frameColumns_length_43 : frameColumns43.length = 98 := by rfl
theorem appliedColumns_length_43 : appliedColumns43.length = 98 := by rfl
theorem gramRows_length_43 : gramRows43.length = 98 := by rfl
theorem residualColumns_length_43 : residualColumns43.length = 98 := by rfl

theorem original_row_44 : frameRows44 = originalRows[44]! := by rfl

theorem original_column_44 : frameColumns44 = originalRows.map (fun row => row[44]!) := by rfl

theorem original_hamiltonian_44 (j : Basis) : hamiltonianRows44[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (44 : Basis) j := by
  have previous := Upper.source_entries (44 : Basis) j
  have restore : hamiltonianRows44[j.val]! = (if j=(44 : Basis) then 3150000000000000 else 0)-Upper.numerator (44 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_44 : appliedColumns44 = hamiltonianRows.map (fun row => Rows.dot row frameColumns44) := by rfl

theorem gram_row_44 : gramRows44 = frameColumns.map (Rows.dot frameColumns44) := by rfl

theorem eigen_residual_44 : residualColumns44 = (appliedColumns44.zip frameColumns44).map (fun pair => pair.1-pair.2*energies[44]!) := by rfl

theorem gram_error_44 : ((gramRows44.zip (List.ofFn (fun j : Fin 98 => if j=(44 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_44 : (residualColumns44.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_44 : hamiltonianRows44.length = 98 := by rfl
theorem frameRows_length_44 : frameRows44.length = 98 := by rfl
theorem frameColumns_length_44 : frameColumns44.length = 98 := by rfl
theorem appliedColumns_length_44 : appliedColumns44.length = 98 := by rfl
theorem gramRows_length_44 : gramRows44.length = 98 := by rfl
theorem residualColumns_length_44 : residualColumns44.length = 98 := by rfl

theorem original_row_45 : frameRows45 = originalRows[45]! := by rfl

theorem original_column_45 : frameColumns45 = originalRows.map (fun row => row[45]!) := by rfl

theorem original_hamiltonian_45 (j : Basis) : hamiltonianRows45[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (45 : Basis) j := by
  have previous := Upper.source_entries (45 : Basis) j
  have restore : hamiltonianRows45[j.val]! = (if j=(45 : Basis) then 3150000000000000 else 0)-Upper.numerator (45 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_45 : appliedColumns45 = hamiltonianRows.map (fun row => Rows.dot row frameColumns45) := by rfl

theorem gram_row_45 : gramRows45 = frameColumns.map (Rows.dot frameColumns45) := by rfl

theorem eigen_residual_45 : residualColumns45 = (appliedColumns45.zip frameColumns45).map (fun pair => pair.1-pair.2*energies[45]!) := by rfl

theorem gram_error_45 : ((gramRows45.zip (List.ofFn (fun j : Fin 98 => if j=(45 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_45 : (residualColumns45.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_45 : hamiltonianRows45.length = 98 := by rfl
theorem frameRows_length_45 : frameRows45.length = 98 := by rfl
theorem frameColumns_length_45 : frameColumns45.length = 98 := by rfl
theorem appliedColumns_length_45 : appliedColumns45.length = 98 := by rfl
theorem gramRows_length_45 : gramRows45.length = 98 := by rfl
theorem residualColumns_length_45 : residualColumns45.length = 98 := by rfl

theorem original_row_46 : frameRows46 = originalRows[46]! := by rfl

theorem original_column_46 : frameColumns46 = originalRows.map (fun row => row[46]!) := by rfl

theorem original_hamiltonian_46 (j : Basis) : hamiltonianRows46[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (46 : Basis) j := by
  have previous := Upper.source_entries (46 : Basis) j
  have restore : hamiltonianRows46[j.val]! = (if j=(46 : Basis) then 3150000000000000 else 0)-Upper.numerator (46 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_46 : appliedColumns46 = hamiltonianRows.map (fun row => Rows.dot row frameColumns46) := by rfl

theorem gram_row_46 : gramRows46 = frameColumns.map (Rows.dot frameColumns46) := by rfl

theorem eigen_residual_46 : residualColumns46 = (appliedColumns46.zip frameColumns46).map (fun pair => pair.1-pair.2*energies[46]!) := by rfl

theorem gram_error_46 : ((gramRows46.zip (List.ofFn (fun j : Fin 98 => if j=(46 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_46 : (residualColumns46.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_46 : hamiltonianRows46.length = 98 := by rfl
theorem frameRows_length_46 : frameRows46.length = 98 := by rfl
theorem frameColumns_length_46 : frameColumns46.length = 98 := by rfl
theorem appliedColumns_length_46 : appliedColumns46.length = 98 := by rfl
theorem gramRows_length_46 : gramRows46.length = 98 := by rfl
theorem residualColumns_length_46 : residualColumns46.length = 98 := by rfl

theorem original_row_47 : frameRows47 = originalRows[47]! := by rfl

theorem original_column_47 : frameColumns47 = originalRows.map (fun row => row[47]!) := by rfl

theorem original_hamiltonian_47 (j : Basis) : hamiltonianRows47[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (47 : Basis) j := by
  have previous := Upper.source_entries (47 : Basis) j
  have restore : hamiltonianRows47[j.val]! = (if j=(47 : Basis) then 3150000000000000 else 0)-Upper.numerator (47 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_47 : appliedColumns47 = hamiltonianRows.map (fun row => Rows.dot row frameColumns47) := by rfl

theorem gram_row_47 : gramRows47 = frameColumns.map (Rows.dot frameColumns47) := by rfl

theorem eigen_residual_47 : residualColumns47 = (appliedColumns47.zip frameColumns47).map (fun pair => pair.1-pair.2*energies[47]!) := by rfl

theorem gram_error_47 : ((gramRows47.zip (List.ofFn (fun j : Fin 98 => if j=(47 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_47 : (residualColumns47.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_47 : hamiltonianRows47.length = 98 := by rfl
theorem frameRows_length_47 : frameRows47.length = 98 := by rfl
theorem frameColumns_length_47 : frameColumns47.length = 98 := by rfl
theorem appliedColumns_length_47 : appliedColumns47.length = 98 := by rfl
theorem gramRows_length_47 : gramRows47.length = 98 := by rfl
theorem residualColumns_length_47 : residualColumns47.length = 98 := by rfl

theorem original_row_48 : frameRows48 = originalRows[48]! := by rfl

theorem original_column_48 : frameColumns48 = originalRows.map (fun row => row[48]!) := by rfl

theorem original_hamiltonian_48 (j : Basis) : hamiltonianRows48[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (48 : Basis) j := by
  have previous := Upper.source_entries (48 : Basis) j
  have restore : hamiltonianRows48[j.val]! = (if j=(48 : Basis) then 3150000000000000 else 0)-Upper.numerator (48 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_48 : appliedColumns48 = hamiltonianRows.map (fun row => Rows.dot row frameColumns48) := by rfl

theorem gram_row_48 : gramRows48 = frameColumns.map (Rows.dot frameColumns48) := by rfl

theorem eigen_residual_48 : residualColumns48 = (appliedColumns48.zip frameColumns48).map (fun pair => pair.1-pair.2*energies[48]!) := by rfl

theorem gram_error_48 : ((gramRows48.zip (List.ofFn (fun j : Fin 98 => if j=(48 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_48 : (residualColumns48.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_48 : hamiltonianRows48.length = 98 := by rfl
theorem frameRows_length_48 : frameRows48.length = 98 := by rfl
theorem frameColumns_length_48 : frameColumns48.length = 98 := by rfl
theorem appliedColumns_length_48 : appliedColumns48.length = 98 := by rfl
theorem gramRows_length_48 : gramRows48.length = 98 := by rfl
theorem residualColumns_length_48 : residualColumns48.length = 98 := by rfl

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
