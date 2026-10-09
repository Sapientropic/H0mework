import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Assembly.Products

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
open Spectral Propagation.Interface
open scoped Matrix BigOperators

def original : Matrix Basis Basis Int := Rows.rowMatrix hamiltonianRows
def frame : Matrix Basis Basis Int := Rows.columnMatrix frameColumns
def applied : Matrix Basis Basis Int := Rows.columnMatrix appliedColumns
def gram : Matrix Basis Basis Int := Rows.rowMatrix gramRows

theorem actual_source (i j : Basis) : original i j =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource i j := by
  fin_cases i
  · exact original_hamiltonian_0 j
  · exact original_hamiltonian_1 j
  · exact original_hamiltonian_2 j
  · exact original_hamiltonian_3 j
  · exact original_hamiltonian_4 j
  · exact original_hamiltonian_5 j
  · exact original_hamiltonian_6 j
  · exact original_hamiltonian_7 j
  · exact original_hamiltonian_8 j
  · exact original_hamiltonian_9 j
  · exact original_hamiltonian_10 j
  · exact original_hamiltonian_11 j
  · exact original_hamiltonian_12 j
  · exact original_hamiltonian_13 j
  · exact original_hamiltonian_14 j
  · exact original_hamiltonian_15 j
  · exact original_hamiltonian_16 j
  · exact original_hamiltonian_17 j
  · exact original_hamiltonian_18 j
  · exact original_hamiltonian_19 j
  · exact original_hamiltonian_20 j
  · exact original_hamiltonian_21 j
  · exact original_hamiltonian_22 j
  · exact original_hamiltonian_23 j
  · exact original_hamiltonian_24 j
  · exact original_hamiltonian_25 j
  · exact original_hamiltonian_26 j
  · exact original_hamiltonian_27 j
  · exact original_hamiltonian_28 j
  · exact original_hamiltonian_29 j
  · exact original_hamiltonian_30 j
  · exact original_hamiltonian_31 j
  · exact original_hamiltonian_32 j
  · exact original_hamiltonian_33 j
  · exact original_hamiltonian_34 j
  · exact original_hamiltonian_35 j
  · exact original_hamiltonian_36 j
  · exact original_hamiltonian_37 j
  · exact original_hamiltonian_38 j
  · exact original_hamiltonian_39 j
  · exact original_hamiltonian_40 j
  · exact original_hamiltonian_41 j
  · exact original_hamiltonian_42 j
  · exact original_hamiltonian_43 j
  · exact original_hamiltonian_44 j
  · exact original_hamiltonian_45 j
  · exact original_hamiltonian_46 j
  · exact original_hamiltonian_47 j
  · exact original_hamiltonian_48 j
  · exact original_hamiltonian_49 j
  · exact original_hamiltonian_50 j
  · exact original_hamiltonian_51 j
  · exact original_hamiltonian_52 j
  · exact original_hamiltonian_53 j
  · exact original_hamiltonian_54 j
  · exact original_hamiltonian_55 j
  · exact original_hamiltonian_56 j
  · exact original_hamiltonian_57 j
  · exact original_hamiltonian_58 j
  · exact original_hamiltonian_59 j
  · exact original_hamiltonian_60 j
  · exact original_hamiltonian_61 j
  · exact original_hamiltonian_62 j
  · exact original_hamiltonian_63 j
  · exact original_hamiltonian_64 j
  · exact original_hamiltonian_65 j
  · exact original_hamiltonian_66 j
  · exact original_hamiltonian_67 j
  · exact original_hamiltonian_68 j
  · exact original_hamiltonian_69 j
  · exact original_hamiltonian_70 j
  · exact original_hamiltonian_71 j
  · exact original_hamiltonian_72 j
  · exact original_hamiltonian_73 j
  · exact original_hamiltonian_74 j
  · exact original_hamiltonian_75 j
  · exact original_hamiltonian_76 j
  · exact original_hamiltonian_77 j
  · exact original_hamiltonian_78 j
  · exact original_hamiltonian_79 j
  · exact original_hamiltonian_80 j
  · exact original_hamiltonian_81 j
  · exact original_hamiltonian_82 j
  · exact original_hamiltonian_83 j
  · exact original_hamiltonian_84 j
  · exact original_hamiltonian_85 j
  · exact original_hamiltonian_86 j
  · exact original_hamiltonian_87 j
  · exact original_hamiltonian_88 j
  · exact original_hamiltonian_89 j
  · exact original_hamiltonian_90 j
  · exact original_hamiltonian_91 j
  · exact original_hamiltonian_92 j
  · exact original_hamiltonian_93 j
  · exact original_hamiltonian_94 j
  · exact original_hamiltonian_95 j
  · exact original_hamiltonian_96 j
  · exact original_hamiltonian_97 j


theorem source_product : original*frame = applied :=
  (Rows.first_matrix hamiltonianRows frameColumns appliedColumns hamiltonianRows_length
    hamiltonianRows_lengths frameColumns_lengths all_applied).symm

theorem source_gram : frame.transpose*frame = gram :=
  (Rows.second_matrix frameColumns frameColumns gramRows frameColumns_length
    frameColumns_lengths frameColumns_lengths all_gram).symm

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
