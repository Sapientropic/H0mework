import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.RestSector.A414.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def restA414NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable restA414NetTable pairFin pairFin
def restA414CenterInt : Int := 7078*scale/10^9
def restA414RadiusInt : Int := 3729*scale/10^9
def restA414CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => restA414NetInt.re i j - (if i=j then restA414CenterInt else 0), restA414NetInt.im⟩
def restA414CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((restA414CenteredInt.re i j)^2+(restA414CenteredInt.im i j)^2)

theorem restA414_source_net_matrix :
    sourceOrdinaryNetInt (4 : Basis) (14 : Basis) (by decide) = restA414NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (4 : Basis) (14 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = restA414NetInt := by rw [restA414_source_net_literal]; rfl

theorem restA414_centered_square_lt :
    restA414CenteredSquareInt < restA414RadiusInt^2 := by decide +kernel

theorem restA414_centered_value :
    value restA414CenteredInt = value restA414NetInt -
      (7078/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [restA414CenteredInt,restA414CenterInt,value,raw,scale]
    ring
  · simp [restA414CenteredInt,restA414CenterInt,value,raw,scale,h]

theorem restA414_centered_norm :
    ‖value restA414NetInt -
      (7078/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3729/10^9 : ℝ) := by
  rw [← restA414_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((restA414CenteredInt.re i j)^2+(restA414CenteredInt.im i j)^2)) ≤
        restA414RadiusInt^2 := by
    simpa only [restA414CenteredSquareInt] using le_of_lt restA414_centered_square_lt
  have h := integer_operator_norm_bound restA414CenteredInt restA414RadiusInt
    (by norm_num [restA414RadiusInt,scale]) square
  convert h using 1
  norm_num [restA414RadiusInt,scale]

theorem restA414_qnet_centered_norm :
    ‖sourceOrdinaryQNet (4 : Basis) (14 : Basis) (by decide) -
      (7078/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3735/10^9 : ℝ) := by
  have source := source_ordinary_net_error (4 : Basis) (14 : Basis) (by decide)
  rw [restA414_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (4 : Basis) (14 : Basis) (by decide))
    (value restA414NetInt)
    ((7078/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (4 : Basis) (14 : Basis) (by decide) - value restA414NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse restA414_centered_norm).trans (by norm_num))

theorem restA414_qnet_floor :
    (3343/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (4 : Basis) (14 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (4 : Basis) (14 : Basis) (by decide))
    (ordinary_qnet_hermitian (4 : Basis) (14 : Basis) (by decide))
    (7078/10^9) (3735/10^9) restA414_qnet_centered_norm
  have compare : (3343/10^9 : ℝ) ≤ 7078/10^9-3735/10^9 := by norm_num
  have smaller : (3343/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (7078/10^9-3735/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
