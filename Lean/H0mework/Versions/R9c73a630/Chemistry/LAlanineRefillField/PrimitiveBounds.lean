import H0mework.Versions.R9c73a630.Chemistry.LAlanineThermalLoad.HamiltonianBound
import H0mework.Chemistry.LAlanineRefillField.Block0
import H0mework.Chemistry.LAlanineRefillField.Block1
import H0mework.Chemistry.LAlanineRefillField.Block2
import H0mework.Chemistry.LAlanineRefillField.Block3
import H0mework.Chemistry.LAlanineRefillField.Block4
import H0mework.Chemistry.LAlanineRefillField.Block5
import H0mework.Chemistry.LAlanineRefillField.Block6

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.SourcePrimitive

open Propagation.Interface Propagation.Source Load.Producer.StrictThermal
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

noncomputable section

theorem source_H00_exact : activeNumerator electronicSource 0 0 = -18260595020028168 := by
  decide

theorem source_H00_lt : (activeMatrix electronicSource 0 0).re < -18 := by
  norm_num [activeMatrix, source_H00_exact]

theorem sourceFieldSquaredMagnitude_bound : sourceFieldSquaredMagnitude ≤ 28 * 10 ^ 27 := by
  have reindex := Equiv.sum_comp (finProdFinEquiv : Fin 7 × Fin 14 ≃ Fin 98)
    (fun i => ∑ j : Basis, symmetricEntry electronicSource.zQ i j ^ 2)
  have blocks : sourceFieldSquaredMagnitude = ∑ block, sourceFieldSquaredBlock block := by
    simpa only [sourceFieldSquaredMagnitude, sourceFieldSquaredBlock, Fintype.sum_prod_type]
      using reindex.symm
  rw [blocks]
  have bound (block : Fin 7) : sourceFieldSquaredBlock block ≤ 4 * 10 ^ 27 := by
    fin_cases block
    · exact sourceFieldSquaredBlock0
    · exact sourceFieldSquaredBlock1
    · exact sourceFieldSquaredBlock2
    · exact sourceFieldSquaredBlock3
    · exact sourceFieldSquaredBlock4
    · exact sourceFieldSquaredBlock5
    · exact sourceFieldSquaredBlock6
  have total := Finset.sum_le_sum (s := Finset.univ) (fun block _ => bound block)
  norm_num at total ⊢
  exact total

def sourceFieldDelta : Matrix Basis Basis ℂ :=
  fun i j => (symmetricEntry electronicSource.zQ i j : ℂ) / 1000000000000000

theorem source_field_delta_eq :
    activeMatrix electronicSource - activeMatrix Work.Drive.fieldOffSource = sourceFieldDelta := by
  ext i j
  change (((1000 * symmetricEntry electronicSource.h0Q i j +
    symmetricEntry electronicSource.zQ i j : ℤ) : ℂ) / 1000000000000000) -
    (((1000 * symmetricEntry electronicSource.h0Q i j + 0 : ℤ) : ℂ) / 1000000000000000) = _
  simp only [sourceFieldDelta, Int.cast_add, Int.cast_mul, Int.cast_ofNat, add_zero]
  ring

theorem sourceFieldDelta_norm_le_fifth : ‖sourceFieldDelta‖ ≤ 1 / 5 := by
  apply matrix_norm_le_of_entrySquares _ (1 / 5) (by norm_num)
  have bound : (sourceFieldSquaredMagnitude : ℝ) ≤ 28 * 10 ^ 27 := by
    exact_mod_cast sourceFieldSquaredMagnitude_bound
  have entries : (∑ i : Basis, ∑ j : Basis, ‖sourceFieldDelta i j‖ ^ 2) =
      (sourceFieldSquaredMagnitude : ℝ) / (1000000000000000 : ℝ) ^ 2 := by
    simp only [sourceFieldSquaredMagnitude, Int.cast_sum, Int.cast_pow, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    norm_num [sourceFieldDelta, norm_div, Complex.norm_intCast, div_pow]
  rw [entries]
  norm_num at bound ⊢
  linarith

theorem sourceFieldDelta_norm_lt_quarter : ‖sourceFieldDelta‖ < 1 / 4 :=
  lt_of_le_of_lt sourceFieldDelta_norm_le_fifth (by norm_num)

theorem source_field_energy_coordinates :
    Thermal.Source.energyHamiltonian - Work.Drive.fieldOffHamiltonian =
      Unitary.conjStarAlgAut ℂ _ (star Preparation.sourceEnergyFrame) sourceFieldDelta := by
  rw [← Powered.Source.sourceHamiltonian_in_shared_frame,
    Powered.Source.sourceCoordinates_as_conjugation]
  unfold Work.Drive.fieldOffHamiltonian Preparation.energyCoordinates
  rw [Unitary.conjStarAlgAut_apply]
  simp only [Unitary.coe_star, star_star]
  rw [← Matrix.sub_mul, ← Matrix.mul_sub, source_field_delta_eq]

theorem source_field_norm_lt_quarter :
    ‖Thermal.Source.energyHamiltonian - Work.Drive.fieldOffHamiltonian‖ < 1 / 4 := by
  rw [source_field_energy_coordinates, conjugation_norm]
  exact sourceFieldDelta_norm_lt_quarter

theorem sourceInitialDensity_nonzero : initialDensityMatrix electronicSource ≠ 0 := by
  have entry : symmetricEntry electronicSource.d0Q 0 0 = 1993811012481 := by decide
  intro zero
  have first := congrArg (fun matrix : Matrix Basis Basis ℂ => matrix 0 0) zero
  norm_num [initialDensityMatrix, entry] at first

theorem sourceGramMass_positive : 0 < Preparation.gramMass (initialDensityMatrix electronicSource) :=
  Preparation.gramMass_positive _ sourceInitialDensity_nonzero


end

end LAlanine40K2025.Thermal.Recovery.SourcePrimitive
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
