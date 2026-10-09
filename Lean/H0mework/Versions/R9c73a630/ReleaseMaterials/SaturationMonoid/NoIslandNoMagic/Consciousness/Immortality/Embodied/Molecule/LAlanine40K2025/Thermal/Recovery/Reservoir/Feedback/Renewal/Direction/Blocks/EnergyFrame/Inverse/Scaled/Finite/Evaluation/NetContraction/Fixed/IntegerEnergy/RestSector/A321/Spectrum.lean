import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.RestSector.A321.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def restA321NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable restA321NetTable pairFin pairFin
def restA321CenterInt : Int := 6931*scale/10^9
def restA321RadiusInt : Int := 3732*scale/10^9
def restA321CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => restA321NetInt.re i j - (if i=j then restA321CenterInt else 0), restA321NetInt.im⟩
def restA321CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((restA321CenteredInt.re i j)^2+(restA321CenteredInt.im i j)^2)

theorem restA321_source_net_matrix :
    sourceOrdinaryNetInt (3 : Basis) (21 : Basis) (by decide) = restA321NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (3 : Basis) (21 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = restA321NetInt := by rw [restA321_source_net_literal]; rfl

theorem restA321_centered_square_lt :
    restA321CenteredSquareInt < restA321RadiusInt^2 := by decide +kernel

theorem restA321_centered_value :
    value restA321CenteredInt = value restA321NetInt -
      (6931/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [restA321CenteredInt,restA321CenterInt,value,raw,scale]
    ring
  · simp [restA321CenteredInt,restA321CenterInt,value,raw,scale,h]

theorem restA321_centered_norm :
    ‖value restA321NetInt -
      (6931/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3732/10^9 : ℝ) := by
  rw [← restA321_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((restA321CenteredInt.re i j)^2+(restA321CenteredInt.im i j)^2)) ≤
        restA321RadiusInt^2 := by
    simpa only [restA321CenteredSquareInt] using le_of_lt restA321_centered_square_lt
  have h := integer_operator_norm_bound restA321CenteredInt restA321RadiusInt
    (by norm_num [restA321RadiusInt,scale]) square
  convert h using 1
  norm_num [restA321RadiusInt,scale]

theorem restA321_qnet_centered_norm :
    ‖sourceOrdinaryQNet (3 : Basis) (21 : Basis) (by decide) -
      (6931/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3738/10^9 : ℝ) := by
  have source := source_ordinary_net_error (3 : Basis) (21 : Basis) (by decide)
  rw [restA321_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (3 : Basis) (21 : Basis) (by decide))
    (value restA321NetInt)
    ((6931/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (3 : Basis) (21 : Basis) (by decide) - value restA321NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse restA321_centered_norm).trans (by norm_num))

theorem restA321_qnet_floor :
    (3193/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (3 : Basis) (21 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (3 : Basis) (21 : Basis) (by decide))
    (ordinary_qnet_hermitian (3 : Basis) (21 : Basis) (by decide))
    (6931/10^9) (3738/10^9) restA321_qnet_centered_norm
  have compare : (3193/10^9 : ℝ) ≤ 6931/10^9-3738/10^9 := by norm_num
  have smaller : (3193/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (6931/10^9-3738/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
