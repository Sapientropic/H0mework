import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.RestSector.A315.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def restA315NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable restA315NetTable pairFin pairFin
def restA315CenterInt : Int := 7053*scale/10^9
def restA315RadiusInt : Int := 3730*scale/10^9
def restA315CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => restA315NetInt.re i j - (if i=j then restA315CenterInt else 0), restA315NetInt.im⟩
def restA315CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((restA315CenteredInt.re i j)^2+(restA315CenteredInt.im i j)^2)

theorem restA315_source_net_matrix :
    sourceOrdinaryNetInt (3 : Basis) (15 : Basis) (by decide) = restA315NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (3 : Basis) (15 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = restA315NetInt := by rw [restA315_source_net_literal]; rfl

theorem restA315_centered_square_lt :
    restA315CenteredSquareInt < restA315RadiusInt^2 := by decide +kernel

theorem restA315_centered_value :
    value restA315CenteredInt = value restA315NetInt -
      (7053/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [restA315CenteredInt,restA315CenterInt,value,raw,scale]
    ring
  · simp [restA315CenteredInt,restA315CenterInt,value,raw,scale,h]

theorem restA315_centered_norm :
    ‖value restA315NetInt -
      (7053/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3730/10^9 : ℝ) := by
  rw [← restA315_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((restA315CenteredInt.re i j)^2+(restA315CenteredInt.im i j)^2)) ≤
        restA315RadiusInt^2 := by
    simpa only [restA315CenteredSquareInt] using le_of_lt restA315_centered_square_lt
  have h := integer_operator_norm_bound restA315CenteredInt restA315RadiusInt
    (by norm_num [restA315RadiusInt,scale]) square
  convert h using 1
  norm_num [restA315RadiusInt,scale]

theorem restA315_qnet_centered_norm :
    ‖sourceOrdinaryQNet (3 : Basis) (15 : Basis) (by decide) -
      (7053/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3736/10^9 : ℝ) := by
  have source := source_ordinary_net_error (3 : Basis) (15 : Basis) (by decide)
  rw [restA315_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (3 : Basis) (15 : Basis) (by decide))
    (value restA315NetInt)
    ((7053/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (3 : Basis) (15 : Basis) (by decide) - value restA315NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse restA315_centered_norm).trans (by norm_num))

theorem restA315_qnet_floor :
    (3317/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (3 : Basis) (15 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (3 : Basis) (15 : Basis) (by decide))
    (ordinary_qnet_hermitian (3 : Basis) (15 : Basis) (by decide))
    (7053/10^9) (3736/10^9) restA315_qnet_centered_norm
  have compare : (3317/10^9 : ℝ) ≤ 7053/10^9-3736/10^9 := by norm_num
  have smaller : (3317/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (7053/10^9-3736/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
