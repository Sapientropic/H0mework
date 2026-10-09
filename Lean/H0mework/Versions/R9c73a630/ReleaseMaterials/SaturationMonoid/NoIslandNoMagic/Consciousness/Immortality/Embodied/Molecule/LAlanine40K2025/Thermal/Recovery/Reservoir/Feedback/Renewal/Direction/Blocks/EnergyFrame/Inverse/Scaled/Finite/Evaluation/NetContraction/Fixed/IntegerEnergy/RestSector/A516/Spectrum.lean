import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.RestSector.A516.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def restA516NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable restA516NetTable pairFin pairFin
def restA516CenterInt : Int := 7012*scale/10^9
def restA516RadiusInt : Int := 3729*scale/10^9
def restA516CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => restA516NetInt.re i j - (if i=j then restA516CenterInt else 0), restA516NetInt.im⟩
def restA516CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((restA516CenteredInt.re i j)^2+(restA516CenteredInt.im i j)^2)

theorem restA516_source_net_matrix :
    sourceOrdinaryNetInt (5 : Basis) (16 : Basis) (by decide) = restA516NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (5 : Basis) (16 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = restA516NetInt := by rw [restA516_source_net_literal]; rfl

theorem restA516_centered_square_lt :
    restA516CenteredSquareInt < restA516RadiusInt^2 := by decide +kernel

theorem restA516_centered_value :
    value restA516CenteredInt = value restA516NetInt -
      (7012/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [restA516CenteredInt,restA516CenterInt,value,raw,scale]
    ring
  · simp [restA516CenteredInt,restA516CenterInt,value,raw,scale,h]

theorem restA516_centered_norm :
    ‖value restA516NetInt -
      (7012/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3729/10^9 : ℝ) := by
  rw [← restA516_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((restA516CenteredInt.re i j)^2+(restA516CenteredInt.im i j)^2)) ≤
        restA516RadiusInt^2 := by
    simpa only [restA516CenteredSquareInt] using le_of_lt restA516_centered_square_lt
  have h := integer_operator_norm_bound restA516CenteredInt restA516RadiusInt
    (by norm_num [restA516RadiusInt,scale]) square
  convert h using 1
  norm_num [restA516RadiusInt,scale]

theorem restA516_qnet_centered_norm :
    ‖sourceOrdinaryQNet (5 : Basis) (16 : Basis) (by decide) -
      (7012/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3735/10^9 : ℝ) := by
  have source := source_ordinary_net_error (5 : Basis) (16 : Basis) (by decide)
  rw [restA516_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (5 : Basis) (16 : Basis) (by decide))
    (value restA516NetInt)
    ((7012/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (5 : Basis) (16 : Basis) (by decide) - value restA516NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse restA516_centered_norm).trans (by norm_num))

theorem restA516_qnet_floor :
    (3277/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (5 : Basis) (16 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (5 : Basis) (16 : Basis) (by decide))
    (ordinary_qnet_hermitian (5 : Basis) (16 : Basis) (by decide))
    (7012/10^9) (3735/10^9) restA516_qnet_centered_norm
  have compare : (3277/10^9 : ℝ) ≤ 7012/10^9-3735/10^9 := by norm_num
  have smaller : (3277/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (7012/10^9-3735/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
