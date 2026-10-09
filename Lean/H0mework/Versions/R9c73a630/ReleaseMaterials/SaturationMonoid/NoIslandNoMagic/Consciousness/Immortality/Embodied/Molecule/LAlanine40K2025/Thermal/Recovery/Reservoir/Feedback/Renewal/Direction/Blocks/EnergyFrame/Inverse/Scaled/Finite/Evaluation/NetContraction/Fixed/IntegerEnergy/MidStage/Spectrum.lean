import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidStage.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def midNetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable midNetTable pairFin pairFin
def midCenterInt : Int := 1225*scale/10^8
def midRadiusInt : Int := 387*scale/10^8
def midCenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => midNetInt.re i j - (if i=j then midCenterInt else 0), midNetInt.im⟩
def midCenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((midCenteredInt.re i j)^2+(midCenteredInt.im i j)^2)

theorem mid_source_net_matrix :
    sourceOrdinaryNetInt (0 : Basis) (6 : Basis) (by decide) = midNetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (0 : Basis) (6 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = midNetInt := by rw [mid_source_net_literal]; rfl

theorem mid_centered_square_lt :
    midCenteredSquareInt < midRadiusInt^2 := by decide +kernel

theorem mid_centered_value :
    value midCenteredInt = value midNetInt -
      (1225/10^8 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [midCenteredInt,midCenterInt,value,raw,scale]
    ring
  · simp [midCenteredInt,midCenterInt,value,raw,scale,h]

theorem mid_centered_norm :
    ‖value midNetInt -
      (1225/10^8 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (387/10^8 : ℝ) := by
  rw [← mid_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((midCenteredInt.re i j)^2+(midCenteredInt.im i j)^2)) ≤
        midRadiusInt^2 := by
    simpa only [midCenteredSquareInt] using le_of_lt mid_centered_square_lt
  have h := integer_operator_norm_bound midCenteredInt midRadiusInt
    (by norm_num [midRadiusInt,scale]) square
  convert h using 1
  norm_num [midRadiusInt,scale]

theorem mid_qnet_centered_norm :
    ‖sourceOrdinaryQNet (0 : Basis) (6 : Basis) (by decide) -
      (1225/10^8 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3876/10^9 : ℝ) := by
  have source := source_ordinary_net_error (0 : Basis) (6 : Basis) (by decide)
  rw [mid_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (0 : Basis) (6 : Basis) (by decide))
    (value midNetInt)
    ((1225/10^8 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (0 : Basis) (6 : Basis) (by decide) - value midNetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse mid_centered_norm).trans (by norm_num))

theorem mid_qnet_floor :
    (837/10^8 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (0 : Basis) (6 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (0 : Basis) (6 : Basis) (by decide))
    (ordinary_qnet_hermitian (0 : Basis) (6 : Basis) (by decide))
    (1225/10^8) (3876/10^9) mid_qnet_centered_norm
  have compare : (837/10^8 : ℝ) ≤ 1225/10^8-3876/10^9 := by norm_num
  have smaller : (837/10^8 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (1225/10^8-3876/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
