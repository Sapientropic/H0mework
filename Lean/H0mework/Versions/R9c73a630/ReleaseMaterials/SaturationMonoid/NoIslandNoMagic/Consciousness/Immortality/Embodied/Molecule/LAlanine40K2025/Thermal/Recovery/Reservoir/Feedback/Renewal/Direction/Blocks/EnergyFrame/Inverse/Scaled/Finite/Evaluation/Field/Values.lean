import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Field.Term1.Values
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Field.Term2.Values
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Field.Term3.Values
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Field.Term4.Values
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Field.Term5.Values
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Field.Term6.Values
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Field.Term7.Values
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Cast

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Field
open Spectral Propagation.Interface
open scoped Matrix

def termColumns : Nat → List (List Int)
  | 0 => List.ofFn (fun j : Basis => identityColumn j.val)
  | 1 => term1Columns
  | 2 => term2Columns
  | 3 => term3Columns
  | 4 => term4Columns
  | 5 => term5Columns
  | 6 => term6Columns
  | 7 => term7Columns
  | _ => []

def termInt (n : Nat) : Matrix Basis Basis Int := Rows.columnMatrix (termColumns n)

noncomputable def termMatrix (n : Nat) : Matrix Basis Basis ℂ :=
  (1/10^24 : ℂ) • Cast.complexMatrix (termInt n)

theorem term_zero_column (j : Basis) : Rows.rowAt (termColumns 0) j=identityColumn j.val := by
  change (List.ofFn (fun j : Basis => identityColumn j.val))[j.val]! = _
  rw [getElem!_pos _ _ (by rw [List.length_ofFn]; exact j.isLt),List.getElem_ofFn]

theorem identityColumn_length (j : Nat) : (identityColumn j).length=98 := by
  simp only [identityColumn,List.length_map,List.length_range]

theorem term_columns_length (n : Nat) (bound : n < 8) : (termColumns n).length=98 := by
  interval_cases n <;> rfl

theorem term_column_lengths (n : Nat) (bound : n < 8) (j : Basis) :
    (Rows.rowAt (termColumns n) j).length=98 := by
  interval_cases n
  · rw [term_zero_column,identityColumn_length]
  · exact term1_column_lengths j
  · exact term2_column_lengths j
  · exact term3_column_lengths j
  · exact term4_column_lengths j
  · exact term5_column_lengths j
  · exact term6_column_lengths j
  · exact term7_column_lengths j

theorem identityColumn_read (i j : Basis) :
    Rows.read (identityColumn j.val) i=if i=j then coefficientScale else 0 := by
  change (identityColumn j.val)[i.val]! = _
  rw [getElem!_pos _ _ (by rw [identityColumn_length]; exact i.isLt)]
  simp only [identityColumn,List.getElem_map,List.getElem_range,Fin.val_inj]

theorem termMatrix_zero : termMatrix 0=1 := by
  ext i j
  change (1/10^24 : ℂ)*(Rows.read (Rows.rowAt (termColumns 0) j) i : ℂ)=_
  rw [term_zero_column,identityColumn_read]
  by_cases same : i=j
  · subst j; norm_num [coefficientScale,Matrix.one_apply]
  · simp only [same,ite_false,Int.cast_zero,mul_zero,Matrix.one_apply]

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Field
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
