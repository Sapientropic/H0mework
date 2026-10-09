import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Data
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Upper.Assembly

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
open Spectral Propagation.Interface

theorem original_row_70 : frameRows70 = originalRows[70]! := by rfl

theorem original_column_70 : frameColumns70 = originalRows.map (fun row => row[70]!) := by rfl

theorem original_hamiltonian_70 (j : Basis) : hamiltonianRows70[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (70 : Basis) j := by
  have previous := Upper.source_entries (70 : Basis) j
  have restore : hamiltonianRows70[j.val]! = (if j=(70 : Basis) then 3150000000000000 else 0)-Upper.numerator (70 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_70 : appliedColumns70 = hamiltonianRows.map (fun row => Rows.dot row frameColumns70) := by rfl

theorem gram_row_70 : gramRows70 = frameColumns.map (Rows.dot frameColumns70) := by rfl

theorem eigen_residual_70 : residualColumns70 = (appliedColumns70.zip frameColumns70).map (fun pair => pair.1-pair.2*energies[70]!) := by rfl

theorem gram_error_70 : ((gramRows70.zip (List.ofFn (fun j : Fin 98 => if j=(70 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_70 : (residualColumns70.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_70 : hamiltonianRows70.length = 98 := by rfl
theorem frameRows_length_70 : frameRows70.length = 98 := by rfl
theorem frameColumns_length_70 : frameColumns70.length = 98 := by rfl
theorem appliedColumns_length_70 : appliedColumns70.length = 98 := by rfl
theorem gramRows_length_70 : gramRows70.length = 98 := by rfl
theorem residualColumns_length_70 : residualColumns70.length = 98 := by rfl

theorem original_row_71 : frameRows71 = originalRows[71]! := by rfl

theorem original_column_71 : frameColumns71 = originalRows.map (fun row => row[71]!) := by rfl

theorem original_hamiltonian_71 (j : Basis) : hamiltonianRows71[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (71 : Basis) j := by
  have previous := Upper.source_entries (71 : Basis) j
  have restore : hamiltonianRows71[j.val]! = (if j=(71 : Basis) then 3150000000000000 else 0)-Upper.numerator (71 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_71 : appliedColumns71 = hamiltonianRows.map (fun row => Rows.dot row frameColumns71) := by rfl

theorem gram_row_71 : gramRows71 = frameColumns.map (Rows.dot frameColumns71) := by rfl

theorem eigen_residual_71 : residualColumns71 = (appliedColumns71.zip frameColumns71).map (fun pair => pair.1-pair.2*energies[71]!) := by rfl

theorem gram_error_71 : ((gramRows71.zip (List.ofFn (fun j : Fin 98 => if j=(71 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_71 : (residualColumns71.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_71 : hamiltonianRows71.length = 98 := by rfl
theorem frameRows_length_71 : frameRows71.length = 98 := by rfl
theorem frameColumns_length_71 : frameColumns71.length = 98 := by rfl
theorem appliedColumns_length_71 : appliedColumns71.length = 98 := by rfl
theorem gramRows_length_71 : gramRows71.length = 98 := by rfl
theorem residualColumns_length_71 : residualColumns71.length = 98 := by rfl

theorem original_row_72 : frameRows72 = originalRows[72]! := by rfl

theorem original_column_72 : frameColumns72 = originalRows.map (fun row => row[72]!) := by rfl

theorem original_hamiltonian_72 (j : Basis) : hamiltonianRows72[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (72 : Basis) j := by
  have previous := Upper.source_entries (72 : Basis) j
  have restore : hamiltonianRows72[j.val]! = (if j=(72 : Basis) then 3150000000000000 else 0)-Upper.numerator (72 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_72 : appliedColumns72 = hamiltonianRows.map (fun row => Rows.dot row frameColumns72) := by rfl

theorem gram_row_72 : gramRows72 = frameColumns.map (Rows.dot frameColumns72) := by rfl

theorem eigen_residual_72 : residualColumns72 = (appliedColumns72.zip frameColumns72).map (fun pair => pair.1-pair.2*energies[72]!) := by rfl

theorem gram_error_72 : ((gramRows72.zip (List.ofFn (fun j : Fin 98 => if j=(72 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_72 : (residualColumns72.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_72 : hamiltonianRows72.length = 98 := by rfl
theorem frameRows_length_72 : frameRows72.length = 98 := by rfl
theorem frameColumns_length_72 : frameColumns72.length = 98 := by rfl
theorem appliedColumns_length_72 : appliedColumns72.length = 98 := by rfl
theorem gramRows_length_72 : gramRows72.length = 98 := by rfl
theorem residualColumns_length_72 : residualColumns72.length = 98 := by rfl

theorem original_row_73 : frameRows73 = originalRows[73]! := by rfl

theorem original_column_73 : frameColumns73 = originalRows.map (fun row => row[73]!) := by rfl

theorem original_hamiltonian_73 (j : Basis) : hamiltonianRows73[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (73 : Basis) j := by
  have previous := Upper.source_entries (73 : Basis) j
  have restore : hamiltonianRows73[j.val]! = (if j=(73 : Basis) then 3150000000000000 else 0)-Upper.numerator (73 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_73 : appliedColumns73 = hamiltonianRows.map (fun row => Rows.dot row frameColumns73) := by rfl

theorem gram_row_73 : gramRows73 = frameColumns.map (Rows.dot frameColumns73) := by rfl

theorem eigen_residual_73 : residualColumns73 = (appliedColumns73.zip frameColumns73).map (fun pair => pair.1-pair.2*energies[73]!) := by rfl

theorem gram_error_73 : ((gramRows73.zip (List.ofFn (fun j : Fin 98 => if j=(73 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_73 : (residualColumns73.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_73 : hamiltonianRows73.length = 98 := by rfl
theorem frameRows_length_73 : frameRows73.length = 98 := by rfl
theorem frameColumns_length_73 : frameColumns73.length = 98 := by rfl
theorem appliedColumns_length_73 : appliedColumns73.length = 98 := by rfl
theorem gramRows_length_73 : gramRows73.length = 98 := by rfl
theorem residualColumns_length_73 : residualColumns73.length = 98 := by rfl

theorem original_row_74 : frameRows74 = originalRows[74]! := by rfl

theorem original_column_74 : frameColumns74 = originalRows.map (fun row => row[74]!) := by rfl

theorem original_hamiltonian_74 (j : Basis) : hamiltonianRows74[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (74 : Basis) j := by
  have previous := Upper.source_entries (74 : Basis) j
  have restore : hamiltonianRows74[j.val]! = (if j=(74 : Basis) then 3150000000000000 else 0)-Upper.numerator (74 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_74 : appliedColumns74 = hamiltonianRows.map (fun row => Rows.dot row frameColumns74) := by rfl

theorem gram_row_74 : gramRows74 = frameColumns.map (Rows.dot frameColumns74) := by rfl

theorem eigen_residual_74 : residualColumns74 = (appliedColumns74.zip frameColumns74).map (fun pair => pair.1-pair.2*energies[74]!) := by rfl

theorem gram_error_74 : ((gramRows74.zip (List.ofFn (fun j : Fin 98 => if j=(74 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_74 : (residualColumns74.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_74 : hamiltonianRows74.length = 98 := by rfl
theorem frameRows_length_74 : frameRows74.length = 98 := by rfl
theorem frameColumns_length_74 : frameColumns74.length = 98 := by rfl
theorem appliedColumns_length_74 : appliedColumns74.length = 98 := by rfl
theorem gramRows_length_74 : gramRows74.length = 98 := by rfl
theorem residualColumns_length_74 : residualColumns74.length = 98 := by rfl

theorem original_row_75 : frameRows75 = originalRows[75]! := by rfl

theorem original_column_75 : frameColumns75 = originalRows.map (fun row => row[75]!) := by rfl

theorem original_hamiltonian_75 (j : Basis) : hamiltonianRows75[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (75 : Basis) j := by
  have previous := Upper.source_entries (75 : Basis) j
  have restore : hamiltonianRows75[j.val]! = (if j=(75 : Basis) then 3150000000000000 else 0)-Upper.numerator (75 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_75 : appliedColumns75 = hamiltonianRows.map (fun row => Rows.dot row frameColumns75) := by rfl

theorem gram_row_75 : gramRows75 = frameColumns.map (Rows.dot frameColumns75) := by rfl

theorem eigen_residual_75 : residualColumns75 = (appliedColumns75.zip frameColumns75).map (fun pair => pair.1-pair.2*energies[75]!) := by rfl

theorem gram_error_75 : ((gramRows75.zip (List.ofFn (fun j : Fin 98 => if j=(75 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_75 : (residualColumns75.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_75 : hamiltonianRows75.length = 98 := by rfl
theorem frameRows_length_75 : frameRows75.length = 98 := by rfl
theorem frameColumns_length_75 : frameColumns75.length = 98 := by rfl
theorem appliedColumns_length_75 : appliedColumns75.length = 98 := by rfl
theorem gramRows_length_75 : gramRows75.length = 98 := by rfl
theorem residualColumns_length_75 : residualColumns75.length = 98 := by rfl

theorem original_row_76 : frameRows76 = originalRows[76]! := by rfl

theorem original_column_76 : frameColumns76 = originalRows.map (fun row => row[76]!) := by rfl

theorem original_hamiltonian_76 (j : Basis) : hamiltonianRows76[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (76 : Basis) j := by
  have previous := Upper.source_entries (76 : Basis) j
  have restore : hamiltonianRows76[j.val]! = (if j=(76 : Basis) then 3150000000000000 else 0)-Upper.numerator (76 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_76 : appliedColumns76 = hamiltonianRows.map (fun row => Rows.dot row frameColumns76) := by rfl

theorem gram_row_76 : gramRows76 = frameColumns.map (Rows.dot frameColumns76) := by rfl

theorem eigen_residual_76 : residualColumns76 = (appliedColumns76.zip frameColumns76).map (fun pair => pair.1-pair.2*energies[76]!) := by rfl

theorem gram_error_76 : ((gramRows76.zip (List.ofFn (fun j : Fin 98 => if j=(76 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_76 : (residualColumns76.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_76 : hamiltonianRows76.length = 98 := by rfl
theorem frameRows_length_76 : frameRows76.length = 98 := by rfl
theorem frameColumns_length_76 : frameColumns76.length = 98 := by rfl
theorem appliedColumns_length_76 : appliedColumns76.length = 98 := by rfl
theorem gramRows_length_76 : gramRows76.length = 98 := by rfl
theorem residualColumns_length_76 : residualColumns76.length = 98 := by rfl

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
