import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidSector.A111.Spectrum
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.SchurNorm

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

/-! Source row/column majorants preserve the non-Hermitian rounding residual. -/

def midA111RowRadiusInt : Int := 2565*scale/10^9

theorem midA111_row_majorant (i : Fin 2 × Fin 2) :
    (∑ j : Fin 2 × Fin 2,
      (|midA111CenteredInt.re i j|+|midA111CenteredInt.im i j|)) ≤
      midA111RowRadiusInt := by
  rcases i with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem midA111_column_majorant (j : Fin 2 × Fin 2) :
    (∑ i : Fin 2 × Fin 2,
      (|midA111CenteredInt.re i j|+|midA111CenteredInt.im i j|)) ≤
      midA111RowRadiusInt := by
  rcases j with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem midA111_centered_row_norm :
    ‖value midA111NetInt-
      (12035/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (2565/10^9 : ℝ) := by
  rw [← midA111_centered_value]
  have h := integer_operator_row_column_bound midA111CenteredInt midA111RowRadiusInt
    (by norm_num [midA111RowRadiusInt,scale]) midA111_row_majorant midA111_column_majorant
  convert h using 1
  norm_num [midA111RowRadiusInt,scale]

theorem midA111_qnet_row_norm :
    ‖sourceOrdinaryQNet (1 : Basis) (11 : Basis) (by decide)-
      (12035/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (2571/10^9 : ℝ) := by
  have source := source_ordinary_net_error (1 : Basis) (11 : Basis) (by decide)
  rw [midA111_source_net_matrix] at source
  have triangle := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (1 : Basis) (11 : Basis) (by decide)) (value midA111NetInt)
    ((12035/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse : ‖sourceOrdinaryQNet (1 : Basis) (11 : Basis) (by decide)-value midA111NetInt‖ ≤
      (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact triangle.trans ((add_le_add reverse midA111_centered_row_norm).trans (by norm_num))

theorem midA111_qnet_row_floor :
    (9464/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (1 : Basis) (11 : Basis) (by decide) := by
  have h := hermitian_lower_from_center
    (sourceOrdinaryQNet (1 : Basis) (11 : Basis) (by decide))
    (ordinary_qnet_hermitian (1 : Basis) (11 : Basis) (by decide))
    (12035/10^9) (2571/10^9) midA111_qnet_row_norm
  convert h using 1
  norm_num

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
