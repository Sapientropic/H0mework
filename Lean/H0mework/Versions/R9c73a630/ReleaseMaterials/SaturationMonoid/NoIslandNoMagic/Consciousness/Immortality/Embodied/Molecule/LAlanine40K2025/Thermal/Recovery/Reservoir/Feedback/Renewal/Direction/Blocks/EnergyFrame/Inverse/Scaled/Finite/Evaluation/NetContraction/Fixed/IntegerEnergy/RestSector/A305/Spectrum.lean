import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.RestSector.A305.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def restA305NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable restA305NetTable pairFin pairFin
def restA305CenterInt : Int := 12121*scale/10^9
def restA305RadiusInt : Int := 3704*scale/10^9
def restA305CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => restA305NetInt.re i j - (if i=j then restA305CenterInt else 0), restA305NetInt.im⟩
def restA305CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((restA305CenteredInt.re i j)^2+(restA305CenteredInt.im i j)^2)

theorem restA305_source_net_matrix :
    sourceOrdinaryNetInt (3 : Basis) (5 : Basis) (by decide) = restA305NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (3 : Basis) (5 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = restA305NetInt := by rw [restA305_source_net_literal]; rfl

theorem restA305_centered_square_lt :
    restA305CenteredSquareInt < restA305RadiusInt^2 := by decide +kernel

theorem restA305_centered_value :
    value restA305CenteredInt = value restA305NetInt -
      (12121/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [restA305CenteredInt,restA305CenterInt,value,raw,scale]
    ring
  · simp [restA305CenteredInt,restA305CenterInt,value,raw,scale,h]

theorem restA305_centered_norm :
    ‖value restA305NetInt -
      (12121/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3704/10^9 : ℝ) := by
  rw [← restA305_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((restA305CenteredInt.re i j)^2+(restA305CenteredInt.im i j)^2)) ≤
        restA305RadiusInt^2 := by
    simpa only [restA305CenteredSquareInt] using le_of_lt restA305_centered_square_lt
  have h := integer_operator_norm_bound restA305CenteredInt restA305RadiusInt
    (by norm_num [restA305RadiusInt,scale]) square
  convert h using 1
  norm_num [restA305RadiusInt,scale]

theorem restA305_qnet_centered_norm :
    ‖sourceOrdinaryQNet (3 : Basis) (5 : Basis) (by decide) -
      (12121/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3710/10^9 : ℝ) := by
  have source := source_ordinary_net_error (3 : Basis) (5 : Basis) (by decide)
  rw [restA305_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (3 : Basis) (5 : Basis) (by decide))
    (value restA305NetInt)
    ((12121/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (3 : Basis) (5 : Basis) (by decide) - value restA305NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse restA305_centered_norm).trans (by norm_num))

theorem restA305_qnet_floor :
    (8411/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (3 : Basis) (5 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (3 : Basis) (5 : Basis) (by decide))
    (ordinary_qnet_hermitian (3 : Basis) (5 : Basis) (by decide))
    (12121/10^9) (3710/10^9) restA305_qnet_centered_norm
  have compare : (8411/10^9 : ℝ) ≤ 12121/10^9-3710/10^9 := by norm_num
  have smaller : (8411/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (12121/10^9-3710/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
