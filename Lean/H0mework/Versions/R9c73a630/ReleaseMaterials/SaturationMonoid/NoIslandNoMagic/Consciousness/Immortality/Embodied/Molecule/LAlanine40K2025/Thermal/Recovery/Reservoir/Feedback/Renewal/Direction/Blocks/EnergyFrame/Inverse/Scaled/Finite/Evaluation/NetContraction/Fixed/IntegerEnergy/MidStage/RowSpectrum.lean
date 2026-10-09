import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidStage.Spectrum
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.SchurNorm

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

/-! Source row/column majorants preserve the non-Hermitian rounding residual. -/

def midRowRadiusInt : Int := 2558*scale/10^9

theorem mid_row_majorant (i : Fin 2 × Fin 2) :
    (∑ j : Fin 2 × Fin 2,
      (|midCenteredInt.re i j|+|midCenteredInt.im i j|)) ≤
      midRowRadiusInt := by
  rcases i with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem mid_column_majorant (j : Fin 2 × Fin 2) :
    (∑ i : Fin 2 × Fin 2,
      (|midCenteredInt.re i j|+|midCenteredInt.im i j|)) ≤
      midRowRadiusInt := by
  rcases j with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem mid_centered_row_norm :
    ‖value midNetInt-
      (1225/10^8 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (2558/10^9 : ℝ) := by
  rw [← mid_centered_value]
  have h := integer_operator_row_column_bound midCenteredInt midRowRadiusInt
    (by norm_num [midRowRadiusInt,scale]) mid_row_majorant mid_column_majorant
  convert h using 1
  norm_num [midRowRadiusInt,scale]

theorem mid_qnet_row_norm :
    ‖sourceOrdinaryQNet (0 : Basis) (6 : Basis) (by decide)-
      (1225/10^8 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (2564/10^9 : ℝ) := by
  have source := source_ordinary_net_error (0 : Basis) (6 : Basis) (by decide)
  rw [mid_source_net_matrix] at source
  have triangle := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (0 : Basis) (6 : Basis) (by decide)) (value midNetInt)
    ((1225/10^8 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse : ‖sourceOrdinaryQNet (0 : Basis) (6 : Basis) (by decide)-value midNetInt‖ ≤
      (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact triangle.trans ((add_le_add reverse mid_centered_row_norm).trans (by norm_num))

theorem mid_qnet_row_floor :
    (9686/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (0 : Basis) (6 : Basis) (by decide) := by
  have h := hermitian_lower_from_center
    (sourceOrdinaryQNet (0 : Basis) (6 : Basis) (by decide))
    (ordinary_qnet_hermitian (0 : Basis) (6 : Basis) (by decide))
    (1225/10^8) (2564/10^9) mid_qnet_row_norm
  convert h using 1
  norm_num

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
