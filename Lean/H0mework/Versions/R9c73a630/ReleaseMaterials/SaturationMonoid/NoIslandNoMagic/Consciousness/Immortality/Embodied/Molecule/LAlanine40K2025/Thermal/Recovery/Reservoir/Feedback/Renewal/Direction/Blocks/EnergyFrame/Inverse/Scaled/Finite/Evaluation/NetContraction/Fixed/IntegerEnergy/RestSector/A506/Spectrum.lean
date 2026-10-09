import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.RestSector.A506.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def restA506NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable restA506NetTable pairFin pairFin
def restA506CenterInt : Int := 7335*scale/10^9
def restA506RadiusInt : Int := 3724*scale/10^9
def restA506CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => restA506NetInt.re i j - (if i=j then restA506CenterInt else 0), restA506NetInt.im⟩
def restA506CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((restA506CenteredInt.re i j)^2+(restA506CenteredInt.im i j)^2)

theorem restA506_source_net_matrix :
    sourceOrdinaryNetInt (5 : Basis) (6 : Basis) (by decide) = restA506NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (5 : Basis) (6 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = restA506NetInt := by rw [restA506_source_net_literal]; rfl

theorem restA506_centered_square_lt :
    restA506CenteredSquareInt < restA506RadiusInt^2 := by decide +kernel

theorem restA506_centered_value :
    value restA506CenteredInt = value restA506NetInt -
      (7335/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [restA506CenteredInt,restA506CenterInt,value,raw,scale]
    ring
  · simp [restA506CenteredInt,restA506CenterInt,value,raw,scale,h]

theorem restA506_centered_norm :
    ‖value restA506NetInt -
      (7335/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3724/10^9 : ℝ) := by
  rw [← restA506_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((restA506CenteredInt.re i j)^2+(restA506CenteredInt.im i j)^2)) ≤
        restA506RadiusInt^2 := by
    simpa only [restA506CenteredSquareInt] using le_of_lt restA506_centered_square_lt
  have h := integer_operator_norm_bound restA506CenteredInt restA506RadiusInt
    (by norm_num [restA506RadiusInt,scale]) square
  convert h using 1
  norm_num [restA506RadiusInt,scale]

theorem restA506_qnet_centered_norm :
    ‖sourceOrdinaryQNet (5 : Basis) (6 : Basis) (by decide) -
      (7335/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3730/10^9 : ℝ) := by
  have source := source_ordinary_net_error (5 : Basis) (6 : Basis) (by decide)
  rw [restA506_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (5 : Basis) (6 : Basis) (by decide))
    (value restA506NetInt)
    ((7335/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (5 : Basis) (6 : Basis) (by decide) - value restA506NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse restA506_centered_norm).trans (by norm_num))

theorem restA506_qnet_floor :
    (3605/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (5 : Basis) (6 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (5 : Basis) (6 : Basis) (by decide))
    (ordinary_qnet_hermitian (5 : Basis) (6 : Basis) (by decide))
    (7335/10^9) (3730/10^9) restA506_qnet_centered_norm
  have compare : (3605/10^9 : ℝ) ≤ 7335/10^9-3730/10^9 := by norm_num
  have smaller : (3605/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (7335/10^9-3730/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
