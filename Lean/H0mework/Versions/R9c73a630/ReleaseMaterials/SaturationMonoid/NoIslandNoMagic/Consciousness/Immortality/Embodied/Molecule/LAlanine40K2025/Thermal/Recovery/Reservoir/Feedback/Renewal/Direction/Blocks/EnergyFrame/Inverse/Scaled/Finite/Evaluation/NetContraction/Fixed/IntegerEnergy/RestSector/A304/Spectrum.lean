import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.RestSector.A304.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def restA304NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable restA304NetTable pairFin pairFin
def restA304CenterInt : Int := 12153*scale/10^9
def restA304RadiusInt : Int := 3704*scale/10^9
def restA304CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => restA304NetInt.re i j - (if i=j then restA304CenterInt else 0), restA304NetInt.im⟩
def restA304CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((restA304CenteredInt.re i j)^2+(restA304CenteredInt.im i j)^2)

theorem restA304_source_net_matrix :
    sourceOrdinaryNetInt (3 : Basis) (4 : Basis) (by decide) = restA304NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (3 : Basis) (4 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = restA304NetInt := by rw [restA304_source_net_literal]; rfl

theorem restA304_centered_square_lt :
    restA304CenteredSquareInt < restA304RadiusInt^2 := by decide +kernel

theorem restA304_centered_value :
    value restA304CenteredInt = value restA304NetInt -
      (12153/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [restA304CenteredInt,restA304CenterInt,value,raw,scale]
    ring
  · simp [restA304CenteredInt,restA304CenterInt,value,raw,scale,h]

theorem restA304_centered_norm :
    ‖value restA304NetInt -
      (12153/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3704/10^9 : ℝ) := by
  rw [← restA304_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((restA304CenteredInt.re i j)^2+(restA304CenteredInt.im i j)^2)) ≤
        restA304RadiusInt^2 := by
    simpa only [restA304CenteredSquareInt] using le_of_lt restA304_centered_square_lt
  have h := integer_operator_norm_bound restA304CenteredInt restA304RadiusInt
    (by norm_num [restA304RadiusInt,scale]) square
  convert h using 1
  norm_num [restA304RadiusInt,scale]

theorem restA304_qnet_centered_norm :
    ‖sourceOrdinaryQNet (3 : Basis) (4 : Basis) (by decide) -
      (12153/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3710/10^9 : ℝ) := by
  have source := source_ordinary_net_error (3 : Basis) (4 : Basis) (by decide)
  rw [restA304_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (3 : Basis) (4 : Basis) (by decide))
    (value restA304NetInt)
    ((12153/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (3 : Basis) (4 : Basis) (by decide) - value restA304NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse restA304_centered_norm).trans (by norm_num))

theorem restA304_qnet_floor :
    (8443/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (3 : Basis) (4 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (3 : Basis) (4 : Basis) (by decide))
    (ordinary_qnet_hermitian (3 : Basis) (4 : Basis) (by decide))
    (12153/10^9) (3710/10^9) restA304_qnet_centered_norm
  have compare : (8443/10^9 : ℝ) ≤ 12153/10^9-3710/10^9 := by norm_num
  have smaller : (8443/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (12153/10^9-3710/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
