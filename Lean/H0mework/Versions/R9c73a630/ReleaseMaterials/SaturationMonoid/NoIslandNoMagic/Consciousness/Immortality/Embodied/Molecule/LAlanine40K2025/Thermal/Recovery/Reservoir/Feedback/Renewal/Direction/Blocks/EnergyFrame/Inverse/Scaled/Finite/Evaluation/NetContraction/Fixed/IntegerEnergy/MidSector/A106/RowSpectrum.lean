import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidSector.A106.Spectrum
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.SchurNorm

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

/-! Source row/column majorants preserve the non-Hermitian rounding residual. -/

def midA106RowRadiusInt : Int := 2555*scale/10^9

theorem midA106_row_majorant (i : Fin 2 × Fin 2) :
    (∑ j : Fin 2 × Fin 2,
      (|midA106CenteredInt.re i j|+|midA106CenteredInt.im i j|)) ≤
      midA106RowRadiusInt := by
  rcases i with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem midA106_column_majorant (j : Fin 2 × Fin 2) :
    (∑ i : Fin 2 × Fin 2,
      (|midA106CenteredInt.re i j|+|midA106CenteredInt.im i j|)) ≤
      midA106RowRadiusInt := by
  rcases j with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem midA106_centered_row_norm :
    ‖value midA106NetInt-
      (12242/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (2555/10^9 : ℝ) := by
  rw [← midA106_centered_value]
  have h := integer_operator_row_column_bound midA106CenteredInt midA106RowRadiusInt
    (by norm_num [midA106RowRadiusInt,scale]) midA106_row_majorant midA106_column_majorant
  convert h using 1
  norm_num [midA106RowRadiusInt,scale]

theorem midA106_qnet_row_norm :
    ‖sourceOrdinaryQNet (1 : Basis) (6 : Basis) (by decide)-
      (12242/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (2561/10^9 : ℝ) := by
  have source := source_ordinary_net_error (1 : Basis) (6 : Basis) (by decide)
  rw [midA106_source_net_matrix] at source
  have triangle := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (1 : Basis) (6 : Basis) (by decide)) (value midA106NetInt)
    ((12242/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse : ‖sourceOrdinaryQNet (1 : Basis) (6 : Basis) (by decide)-value midA106NetInt‖ ≤
      (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact triangle.trans ((add_le_add reverse midA106_centered_row_norm).trans (by norm_num))

theorem midA106_qnet_row_floor :
    (9681/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (1 : Basis) (6 : Basis) (by decide) := by
  have h := hermitian_lower_from_center
    (sourceOrdinaryQNet (1 : Basis) (6 : Basis) (by decide))
    (ordinary_qnet_hermitian (1 : Basis) (6 : Basis) (by decide))
    (12242/10^9) (2561/10^9) midA106_qnet_row_norm
  convert h using 1
  norm_num

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
