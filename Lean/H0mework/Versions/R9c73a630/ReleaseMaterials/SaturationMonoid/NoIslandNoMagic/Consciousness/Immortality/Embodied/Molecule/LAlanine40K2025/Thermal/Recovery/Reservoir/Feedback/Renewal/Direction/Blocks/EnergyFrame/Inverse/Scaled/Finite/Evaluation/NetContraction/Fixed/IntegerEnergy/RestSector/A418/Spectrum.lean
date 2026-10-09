import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.RestSector.A418.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def restA418NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable restA418NetTable pairFin pairFin
def restA418CenterInt : Int := 7008*scale/10^9
def restA418RadiusInt : Int := 3730*scale/10^9
def restA418CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => restA418NetInt.re i j - (if i=j then restA418CenterInt else 0), restA418NetInt.im⟩
def restA418CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((restA418CenteredInt.re i j)^2+(restA418CenteredInt.im i j)^2)

theorem restA418_source_net_matrix :
    sourceOrdinaryNetInt (4 : Basis) (18 : Basis) (by decide) = restA418NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (4 : Basis) (18 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = restA418NetInt := by rw [restA418_source_net_literal]; rfl

theorem restA418_centered_square_lt :
    restA418CenteredSquareInt < restA418RadiusInt^2 := by decide +kernel

theorem restA418_centered_value :
    value restA418CenteredInt = value restA418NetInt -
      (7008/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [restA418CenteredInt,restA418CenterInt,value,raw,scale]
    ring
  · simp [restA418CenteredInt,restA418CenterInt,value,raw,scale,h]

theorem restA418_centered_norm :
    ‖value restA418NetInt -
      (7008/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3730/10^9 : ℝ) := by
  rw [← restA418_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((restA418CenteredInt.re i j)^2+(restA418CenteredInt.im i j)^2)) ≤
        restA418RadiusInt^2 := by
    simpa only [restA418CenteredSquareInt] using le_of_lt restA418_centered_square_lt
  have h := integer_operator_norm_bound restA418CenteredInt restA418RadiusInt
    (by norm_num [restA418RadiusInt,scale]) square
  convert h using 1
  norm_num [restA418RadiusInt,scale]

theorem restA418_qnet_centered_norm :
    ‖sourceOrdinaryQNet (4 : Basis) (18 : Basis) (by decide) -
      (7008/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3736/10^9 : ℝ) := by
  have source := source_ordinary_net_error (4 : Basis) (18 : Basis) (by decide)
  rw [restA418_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (4 : Basis) (18 : Basis) (by decide))
    (value restA418NetInt)
    ((7008/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (4 : Basis) (18 : Basis) (by decide) - value restA418NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse restA418_centered_norm).trans (by norm_num))

theorem restA418_qnet_floor :
    (3272/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (4 : Basis) (18 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (4 : Basis) (18 : Basis) (by decide))
    (ordinary_qnet_hermitian (4 : Basis) (18 : Basis) (by decide))
    (7008/10^9) (3736/10^9) restA418_qnet_centered_norm
  have compare : (3272/10^9 : ℝ) ≤ 7008/10^9-3736/10^9 := by norm_num
  have smaller : (3272/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (7008/10^9-3736/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
