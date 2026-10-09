import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Dense.Algebra
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Dense.FieldApplied.Product
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Dense.DensityApplied.Product
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Dense.Field.Product
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Dense.Gram.Product
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Dense.Original.Mass

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Dense
open Spectral Propagation.Interface Propagation.Source
open scoped Matrix BigOperators

def h0Int : Matrix Basis Basis Int := Rows.rowMatrix h0Rows
def d0Int : Matrix Basis Basis Int := Rows.rowMatrix d0Rows
def fieldAppliedInt : Matrix Basis Basis Int := Rows.columnMatrix fieldAppliedColumns
def densityAppliedInt : Matrix Basis Basis Int := Rows.columnMatrix densityAppliedColumns
def fieldInt : Matrix Basis Basis Int := Rows.rowMatrix fieldRows
def densityGramInt : Matrix Basis Basis Int := Rows.rowMatrix densityGramRows

theorem h0_source_entry (i j : Basis) : h0Int i j=symmetricEntry electronicSource.h0Q i j := by
  change Rows.read (Rows.rowAt h0Rows i) j=_
  rw [h0_source_rows,read_ofFn]

theorem d0_source_entry (i j : Basis) : d0Int i j=symmetricEntry electronicSource.d0Q i j := by
  change Rows.read (Rows.rowAt d0Rows i) j=_
  rw [d0_source_rows,read_ofFn]

theorem original_field_times_frame : h0Int*frame=fieldAppliedInt :=
  (Rows.first_matrix h0Rows frameColumns fieldAppliedColumns h0Rows_length
    h0Rows_lengths frameColumns_lengths all_field_applied).symm

theorem original_density_times_frame : d0Int*frame=densityAppliedInt :=
  (Rows.first_matrix d0Rows frameColumns densityAppliedColumns d0Rows_length
    d0Rows_lengths frameColumns_lengths all_density_applied).symm

theorem original_field_full_product : frame.transpose*fieldAppliedInt=fieldInt :=
  (Rows.second_matrix frameColumns fieldAppliedColumns fieldRows fieldAppliedColumns_length
    frameColumns_lengths fieldAppliedColumns_lengths all_field_product).symm

theorem original_density_full_gram : densityAppliedInt.transpose*densityAppliedInt=densityGramInt :=
  (Rows.second_matrix densityAppliedColumns densityAppliedColumns densityGramRows densityAppliedColumns_length
    densityAppliedColumns_lengths densityAppliedColumns_lengths all_density_gram).symm

theorem density_mass_is_trace : (d0Int*d0Int.transpose).trace=densitySquaredMass := by
  symm
  calc
    densitySquaredMass=densitySquaredRows.sum := density_mass_sum.symm
    _=(List.ofFn (Rows.read (n := 98) densitySquaredRows)).sum :=
      congrArg List.sum (Rows.ofFn_read densitySquaredRows (show densitySquaredRows.length=98 by rfl)).symm
    _=∑ i : Basis, Rows.read densitySquaredRows i := List.sum_ofFn
    _=∑ i : Basis, ∑ j : Basis, Rows.read (Rows.rowAt d0Rows i) j*Rows.read (Rows.rowAt d0Rows i) j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [density_mass_row,Rows.dot_eq_sum _ _ (d0Rows_lengths i) (d0Rows_lengths i)]
    _=_ := rfl

noncomputable section

theorem original_field_off_matrix : activeMatrix Work.Drive.fieldOffSource=
    (1/10^12 : ℂ) • Cast.complexMatrix h0Int := by
  ext i j
  change ((1000*symmetricEntry electronicSource.h0Q i j+0 : Int) : ℂ)/1000000000000000=
    (1/10^12 : ℂ)*(h0Int i j : ℂ)
  rw [h0_source_entry]
  push_cast
  ring

theorem original_density_matrix : initialDensityMatrix electronicSource=
    (1/10^12 : ℂ) • Cast.complexMatrix d0Int := by
  ext i j
  change (symmetricEntry electronicSource.d0Q i j : ℂ)/1000000000000=
    (1/10^12 : ℂ)*(d0Int i j : ℂ)
  rw [d0_source_entry]
  ring

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Dense
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
