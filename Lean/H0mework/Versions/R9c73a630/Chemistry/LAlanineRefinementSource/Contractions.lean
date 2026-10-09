import H0mework.Versions.R9c73a630.Chemistry.LAlanineRefinementSource.ContractionRowsR0
import H0mework.Versions.R9c73a630.Chemistry.LAlanineRefinementSource.ContractionRowsR1
import H0mework.Versions.R9c73a630.Chemistry.LAlanineRefinementSource.ContractionRowsR2
import H0mework.Versions.R9c73a630.Chemistry.LAlanineRefinementSource.ContractionRowsR3
import H0mework.Versions.R9c73a630.Chemistry.LAlanineRefinementSource.ContractionRowsR4
import H0mework.Versions.R9c73a630.Chemistry.LAlanineRefinementSource.ContractionRowsR5
import H0mework.Versions.R9c73a630.Chemistry.LAlanineRefinementDensity.LaplaceSymmetry

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceLaplaceIntegers

open SourceLaplaceRowData SourceLaplaceRowProof SourceGaussianModel SourceFiniteData SourceJetIncidence
open scoped BigOperators

noncomputable section

theorem all_rows (direction : Direction) (basis : Basis) : rowCondition direction basis := by
  fin_cases direction
  · exact SourceLaplaceRows.R0.exact_rows basis
  · exact SourceLaplaceRows.R1.exact_rows basis
  · exact SourceLaplaceRows.R2.exact_rows basis
  · exact SourceLaplaceRows.R3.exact_rows basis
  · exact SourceLaplaceRows.R4.exact_rows basis
  · exact SourceLaplaceRows.R5.exact_rows basis

theorem source_row_sums (direction : Direction) : (∑ i : Basis, sourceRow direction i) = sourceSum direction := by
  fin_cases direction <;> decide +kernel

theorem canonical_fourth_sum (direction : Direction) : fourthInt (innerAxis direction) (outerAxis direction) = sourceSum direction := by
  rw [fourth_eq_sum_rows]
  exact (Finset.sum_congr rfl (fun i _ => all_rows direction i)).trans (source_row_sums direction)

theorem source_sum_bound (direction : Direction) :
    sourceSum direction ≤ 10 ^ 30 * densityInt (fourthIndex (innerAxis direction) (outerAxis direction)) := by
  fin_cases direction <;> decide +kernel

theorem canonical_fourth_bound (direction : Direction) :
    fourthInt (innerAxis direction) (outerAxis direction) ≤
      10 ^ 30 * densityInt (fourthIndex (innerAxis direction) (outerAxis direction)) := by
  rw [canonical_fourth_sum]
  exact source_sum_bound direction

theorem actual_fourth_bounds (innerAxis axis : Fin 3) :
    fourthInt innerAxis axis ≤ 10 ^ 30 * densityInt (fourthIndex innerAxis axis) := by
  fin_cases innerAxis <;> fin_cases axis
  · exact canonical_fourth_bound 0
  · exact canonical_fourth_bound 1
  · exact canonical_fourth_bound 2
  · change fourthInt 1 0 ≤ 10 ^ 30 * densityInt (fourthIndex 1 0)
    rw [fourthInt_symm 1 0, show fourthIndex 1 0 = fourthIndex 0 1 by decide +kernel]
    exact canonical_fourth_bound 1
  · exact canonical_fourth_bound 3
  · exact canonical_fourth_bound 4
  · change fourthInt 2 0 ≤ 10 ^ 30 * densityInt (fourthIndex 2 0)
    rw [fourthInt_symm 2 0, show fourthIndex 2 0 = fourthIndex 0 2 by decide +kernel]
    exact canonical_fourth_bound 2
  · change fourthInt 2 1 ≤ 10 ^ 30 * densityInt (fourthIndex 2 1)
    rw [fourthInt_symm 2 1, show fourthIndex 2 1 = fourthIndex 1 2 by decide +kernel]
    exact canonical_fourth_bound 4
  · exact canonical_fourth_bound 5

theorem actual_fourth_envelopes (innerAxis axis : Fin 3) :
    fourthEnvelope densityMatrixBound sourceOrbitalBound (fun _ => 0) (fun _ => 0) innerAxis axis ≤
      densityBound (fourthIndex innerAxis axis) := by
  rw [fourth_cast, div_le_iff₀ (by positivity : (0 : ℚ) < 10 ^ 30), ← densityInt_cast]
  have source : (fourthInt innerAxis axis : ℚ) ≤ (10 : ℚ) ^ 30 * (densityInt (fourthIndex innerAxis axis) : ℚ) := by
    exact_mod_cast actual_fourth_bounds innerAxis axis
  simpa only [mul_comm] using source

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceLaplaceIntegers
