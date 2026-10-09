import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.RestSector.A416.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def restA416NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable restA416NetTable pairFin pairFin
def restA416CenterInt : Int := 7043*scale/10^9
def restA416RadiusInt : Int := 3730*scale/10^9
def restA416CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => restA416NetInt.re i j - (if i=j then restA416CenterInt else 0), restA416NetInt.im⟩
def restA416CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((restA416CenteredInt.re i j)^2+(restA416CenteredInt.im i j)^2)

theorem restA416_source_net_matrix :
    sourceOrdinaryNetInt (4 : Basis) (16 : Basis) (by decide) = restA416NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (4 : Basis) (16 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = restA416NetInt := by rw [restA416_source_net_literal]; rfl

theorem restA416_centered_square_lt :
    restA416CenteredSquareInt < restA416RadiusInt^2 := by decide +kernel

theorem restA416_centered_value :
    value restA416CenteredInt = value restA416NetInt -
      (7043/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [restA416CenteredInt,restA416CenterInt,value,raw,scale]
    ring
  · simp [restA416CenteredInt,restA416CenterInt,value,raw,scale,h]

theorem restA416_centered_norm :
    ‖value restA416NetInt -
      (7043/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3730/10^9 : ℝ) := by
  rw [← restA416_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((restA416CenteredInt.re i j)^2+(restA416CenteredInt.im i j)^2)) ≤
        restA416RadiusInt^2 := by
    simpa only [restA416CenteredSquareInt] using le_of_lt restA416_centered_square_lt
  have h := integer_operator_norm_bound restA416CenteredInt restA416RadiusInt
    (by norm_num [restA416RadiusInt,scale]) square
  convert h using 1
  norm_num [restA416RadiusInt,scale]

theorem restA416_qnet_centered_norm :
    ‖sourceOrdinaryQNet (4 : Basis) (16 : Basis) (by decide) -
      (7043/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3736/10^9 : ℝ) := by
  have source := source_ordinary_net_error (4 : Basis) (16 : Basis) (by decide)
  rw [restA416_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (4 : Basis) (16 : Basis) (by decide))
    (value restA416NetInt)
    ((7043/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (4 : Basis) (16 : Basis) (by decide) - value restA416NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse restA416_centered_norm).trans (by norm_num))

theorem restA416_qnet_floor :
    (3307/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (4 : Basis) (16 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (4 : Basis) (16 : Basis) (by decide))
    (ordinary_qnet_hermitian (4 : Basis) (16 : Basis) (by decide))
    (7043/10^9) (3736/10^9) restA416_qnet_centered_norm
  have compare : (3307/10^9 : ℝ) ≤ 7043/10^9-3736/10^9 := by norm_num
  have smaller : (3307/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (7043/10^9-3736/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
