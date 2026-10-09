import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.RestSector.A307.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def restA307NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable restA307NetTable pairFin pairFin
def restA307CenterInt : Int := 7302*scale/10^9
def restA307RadiusInt : Int := 3726*scale/10^9
def restA307CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => restA307NetInt.re i j - (if i=j then restA307CenterInt else 0), restA307NetInt.im⟩
def restA307CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((restA307CenteredInt.re i j)^2+(restA307CenteredInt.im i j)^2)

theorem restA307_source_net_matrix :
    sourceOrdinaryNetInt (3 : Basis) (7 : Basis) (by decide) = restA307NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (3 : Basis) (7 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = restA307NetInt := by rw [restA307_source_net_literal]; rfl

theorem restA307_centered_square_lt :
    restA307CenteredSquareInt < restA307RadiusInt^2 := by decide +kernel

theorem restA307_centered_value :
    value restA307CenteredInt = value restA307NetInt -
      (7302/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [restA307CenteredInt,restA307CenterInt,value,raw,scale]
    ring
  · simp [restA307CenteredInt,restA307CenterInt,value,raw,scale,h]

theorem restA307_centered_norm :
    ‖value restA307NetInt -
      (7302/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3726/10^9 : ℝ) := by
  rw [← restA307_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((restA307CenteredInt.re i j)^2+(restA307CenteredInt.im i j)^2)) ≤
        restA307RadiusInt^2 := by
    simpa only [restA307CenteredSquareInt] using le_of_lt restA307_centered_square_lt
  have h := integer_operator_norm_bound restA307CenteredInt restA307RadiusInt
    (by norm_num [restA307RadiusInt,scale]) square
  convert h using 1
  norm_num [restA307RadiusInt,scale]

theorem restA307_qnet_centered_norm :
    ‖sourceOrdinaryQNet (3 : Basis) (7 : Basis) (by decide) -
      (7302/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3732/10^9 : ℝ) := by
  have source := source_ordinary_net_error (3 : Basis) (7 : Basis) (by decide)
  rw [restA307_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (3 : Basis) (7 : Basis) (by decide))
    (value restA307NetInt)
    ((7302/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (3 : Basis) (7 : Basis) (by decide) - value restA307NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse restA307_centered_norm).trans (by norm_num))

theorem restA307_qnet_floor :
    (3570/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (3 : Basis) (7 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (3 : Basis) (7 : Basis) (by decide))
    (ordinary_qnet_hermitian (3 : Basis) (7 : Basis) (by decide))
    (7302/10^9) (3732/10^9) restA307_qnet_centered_norm
  have compare : (3570/10^9 : ℝ) ≤ 7302/10^9-3732/10^9 := by norm_num
  have smaller : (3570/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (7302/10^9-3732/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
