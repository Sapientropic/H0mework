import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.RestSector.A212.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def restA212NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable restA212NetTable pairFin pairFin
def restA212CenterInt : Int := 9463*scale/10^9
def restA212RadiusInt : Int := 3783*scale/10^9
def restA212CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => restA212NetInt.re i j - (if i=j then restA212CenterInt else 0), restA212NetInt.im⟩
def restA212CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((restA212CenteredInt.re i j)^2+(restA212CenteredInt.im i j)^2)

theorem restA212_source_net_matrix :
    sourceOrdinaryNetInt (2 : Basis) (12 : Basis) (by decide) = restA212NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (2 : Basis) (12 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = restA212NetInt := by rw [restA212_source_net_literal]; rfl

theorem restA212_centered_square_lt :
    restA212CenteredSquareInt < restA212RadiusInt^2 := by decide +kernel

theorem restA212_centered_value :
    value restA212CenteredInt = value restA212NetInt -
      (9463/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [restA212CenteredInt,restA212CenterInt,value,raw,scale]
    ring
  · simp [restA212CenteredInt,restA212CenterInt,value,raw,scale,h]

theorem restA212_centered_norm :
    ‖value restA212NetInt -
      (9463/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3783/10^9 : ℝ) := by
  rw [← restA212_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((restA212CenteredInt.re i j)^2+(restA212CenteredInt.im i j)^2)) ≤
        restA212RadiusInt^2 := by
    simpa only [restA212CenteredSquareInt] using le_of_lt restA212_centered_square_lt
  have h := integer_operator_norm_bound restA212CenteredInt restA212RadiusInt
    (by norm_num [restA212RadiusInt,scale]) square
  convert h using 1
  norm_num [restA212RadiusInt,scale]

theorem restA212_qnet_centered_norm :
    ‖sourceOrdinaryQNet (2 : Basis) (12 : Basis) (by decide) -
      (9463/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3789/10^9 : ℝ) := by
  have source := source_ordinary_net_error (2 : Basis) (12 : Basis) (by decide)
  rw [restA212_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (2 : Basis) (12 : Basis) (by decide))
    (value restA212NetInt)
    ((9463/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (2 : Basis) (12 : Basis) (by decide) - value restA212NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse restA212_centered_norm).trans (by norm_num))

theorem restA212_qnet_floor :
    (5674/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (2 : Basis) (12 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (2 : Basis) (12 : Basis) (by decide))
    (ordinary_qnet_hermitian (2 : Basis) (12 : Basis) (by decide))
    (9463/10^9) (3789/10^9) restA212_qnet_centered_norm
  have compare : (5674/10^9 : ℝ) ≤ 9463/10^9-3789/10^9 := by norm_num
  have smaller : (5674/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (9463/10^9-3789/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
