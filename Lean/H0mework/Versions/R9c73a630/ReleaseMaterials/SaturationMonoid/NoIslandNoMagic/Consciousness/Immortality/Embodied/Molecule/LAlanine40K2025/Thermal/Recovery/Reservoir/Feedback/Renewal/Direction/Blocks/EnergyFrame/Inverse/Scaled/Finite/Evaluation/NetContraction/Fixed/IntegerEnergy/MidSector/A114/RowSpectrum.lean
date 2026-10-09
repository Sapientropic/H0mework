import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidSector.A114.Spectrum
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.SchurNorm

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

/-! Source row/column majorants preserve the non-Hermitian rounding residual. -/

def midA114RowRadiusInt : Int := 2569*scale/10^9

theorem midA114_row_majorant (i : Fin 2 × Fin 2) :
    (∑ j : Fin 2 × Fin 2,
      (|midA114CenteredInt.re i j|+|midA114CenteredInt.im i j|)) ≤
      midA114RowRadiusInt := by
  rcases i with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem midA114_column_majorant (j : Fin 2 × Fin 2) :
    (∑ i : Fin 2 × Fin 2,
      (|midA114CenteredInt.re i j|+|midA114CenteredInt.im i j|)) ≤
      midA114RowRadiusInt := by
  rcases j with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem midA114_centered_row_norm :
    ‖value midA114NetInt-
      (11947/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (2569/10^9 : ℝ) := by
  rw [← midA114_centered_value]
  have h := integer_operator_row_column_bound midA114CenteredInt midA114RowRadiusInt
    (by norm_num [midA114RowRadiusInt,scale]) midA114_row_majorant midA114_column_majorant
  convert h using 1
  norm_num [midA114RowRadiusInt,scale]

theorem midA114_qnet_row_norm :
    ‖sourceOrdinaryQNet (1 : Basis) (14 : Basis) (by decide)-
      (11947/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (2575/10^9 : ℝ) := by
  have source := source_ordinary_net_error (1 : Basis) (14 : Basis) (by decide)
  rw [midA114_source_net_matrix] at source
  have triangle := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (1 : Basis) (14 : Basis) (by decide)) (value midA114NetInt)
    ((11947/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse : ‖sourceOrdinaryQNet (1 : Basis) (14 : Basis) (by decide)-value midA114NetInt‖ ≤
      (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact triangle.trans ((add_le_add reverse midA114_centered_row_norm).trans (by norm_num))

theorem midA114_qnet_row_floor :
    (9372/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (1 : Basis) (14 : Basis) (by decide) := by
  have h := hermitian_lower_from_center
    (sourceOrdinaryQNet (1 : Basis) (14 : Basis) (by decide))
    (ordinary_qnet_hermitian (1 : Basis) (14 : Basis) (by decide))
    (11947/10^9) (2575/10^9) midA114_qnet_row_norm
  convert h using 1
  norm_num

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
