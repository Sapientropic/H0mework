import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.RestSector.A515.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def restA515NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable restA515NetTable pairFin pairFin
def restA515CenterInt : Int := 7016*scale/10^9
def restA515RadiusInt : Int := 3729*scale/10^9
def restA515CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => restA515NetInt.re i j - (if i=j then restA515CenterInt else 0), restA515NetInt.im⟩
def restA515CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((restA515CenteredInt.re i j)^2+(restA515CenteredInt.im i j)^2)

theorem restA515_source_net_matrix :
    sourceOrdinaryNetInt (5 : Basis) (15 : Basis) (by decide) = restA515NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (5 : Basis) (15 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = restA515NetInt := by rw [restA515_source_net_literal]; rfl

theorem restA515_centered_square_lt :
    restA515CenteredSquareInt < restA515RadiusInt^2 := by decide +kernel

theorem restA515_centered_value :
    value restA515CenteredInt = value restA515NetInt -
      (7016/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [restA515CenteredInt,restA515CenterInt,value,raw,scale]
    ring
  · simp [restA515CenteredInt,restA515CenterInt,value,raw,scale,h]

theorem restA515_centered_norm :
    ‖value restA515NetInt -
      (7016/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3729/10^9 : ℝ) := by
  rw [← restA515_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((restA515CenteredInt.re i j)^2+(restA515CenteredInt.im i j)^2)) ≤
        restA515RadiusInt^2 := by
    simpa only [restA515CenteredSquareInt] using le_of_lt restA515_centered_square_lt
  have h := integer_operator_norm_bound restA515CenteredInt restA515RadiusInt
    (by norm_num [restA515RadiusInt,scale]) square
  convert h using 1
  norm_num [restA515RadiusInt,scale]

theorem restA515_qnet_centered_norm :
    ‖sourceOrdinaryQNet (5 : Basis) (15 : Basis) (by decide) -
      (7016/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3735/10^9 : ℝ) := by
  have source := source_ordinary_net_error (5 : Basis) (15 : Basis) (by decide)
  rw [restA515_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (5 : Basis) (15 : Basis) (by decide))
    (value restA515NetInt)
    ((7016/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (5 : Basis) (15 : Basis) (by decide) - value restA515NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse restA515_centered_norm).trans (by norm_num))

theorem restA515_qnet_floor :
    (3281/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (5 : Basis) (15 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (5 : Basis) (15 : Basis) (by decide))
    (ordinary_qnet_hermitian (5 : Basis) (15 : Basis) (by decide))
    (7016/10^9) (3735/10^9) restA515_qnet_centered_norm
  have compare : (3281/10^9 : ℝ) ≤ 7016/10^9-3735/10^9 := by norm_num
  have smaller : (3281/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (7016/10^9-3735/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
