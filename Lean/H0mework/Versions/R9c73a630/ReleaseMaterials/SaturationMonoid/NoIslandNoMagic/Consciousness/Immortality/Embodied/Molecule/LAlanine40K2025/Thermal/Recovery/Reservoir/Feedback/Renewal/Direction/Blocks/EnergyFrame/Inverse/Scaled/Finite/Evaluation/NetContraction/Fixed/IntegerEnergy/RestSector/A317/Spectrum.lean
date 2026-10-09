import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.RestSector.A317.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def restA317NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable restA317NetTable pairFin pairFin
def restA317CenterInt : Int := 7042*scale/10^9
def restA317RadiusInt : Int := 3730*scale/10^9
def restA317CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => restA317NetInt.re i j - (if i=j then restA317CenterInt else 0), restA317NetInt.im⟩
def restA317CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((restA317CenteredInt.re i j)^2+(restA317CenteredInt.im i j)^2)

theorem restA317_source_net_matrix :
    sourceOrdinaryNetInt (3 : Basis) (17 : Basis) (by decide) = restA317NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (3 : Basis) (17 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = restA317NetInt := by rw [restA317_source_net_literal]; rfl

theorem restA317_centered_square_lt :
    restA317CenteredSquareInt < restA317RadiusInt^2 := by decide +kernel

theorem restA317_centered_value :
    value restA317CenteredInt = value restA317NetInt -
      (7042/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [restA317CenteredInt,restA317CenterInt,value,raw,scale]
    ring
  · simp [restA317CenteredInt,restA317CenterInt,value,raw,scale,h]

theorem restA317_centered_norm :
    ‖value restA317NetInt -
      (7042/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3730/10^9 : ℝ) := by
  rw [← restA317_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((restA317CenteredInt.re i j)^2+(restA317CenteredInt.im i j)^2)) ≤
        restA317RadiusInt^2 := by
    simpa only [restA317CenteredSquareInt] using le_of_lt restA317_centered_square_lt
  have h := integer_operator_norm_bound restA317CenteredInt restA317RadiusInt
    (by norm_num [restA317RadiusInt,scale]) square
  convert h using 1
  norm_num [restA317RadiusInt,scale]

theorem restA317_qnet_centered_norm :
    ‖sourceOrdinaryQNet (3 : Basis) (17 : Basis) (by decide) -
      (7042/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3736/10^9 : ℝ) := by
  have source := source_ordinary_net_error (3 : Basis) (17 : Basis) (by decide)
  rw [restA317_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (3 : Basis) (17 : Basis) (by decide))
    (value restA317NetInt)
    ((7042/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (3 : Basis) (17 : Basis) (by decide) - value restA317NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse restA317_centered_norm).trans (by norm_num))

theorem restA317_qnet_floor :
    (3306/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (3 : Basis) (17 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (3 : Basis) (17 : Basis) (by decide))
    (ordinary_qnet_hermitian (3 : Basis) (17 : Basis) (by decide))
    (7042/10^9) (3736/10^9) restA317_qnet_centered_norm
  have compare : (3306/10^9 : ℝ) ≤ 7042/10^9-3736/10^9 := by norm_num
  have smaller : (3306/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (7042/10^9-3736/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
