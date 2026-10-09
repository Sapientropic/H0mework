import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.RestSector.A514.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def restA514NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable restA514NetTable pairFin pairFin
def restA514CenterInt : Int := 7047*scale/10^9
def restA514RadiusInt : Int := 3729*scale/10^9
def restA514CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => restA514NetInt.re i j - (if i=j then restA514CenterInt else 0), restA514NetInt.im⟩
def restA514CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((restA514CenteredInt.re i j)^2+(restA514CenteredInt.im i j)^2)

theorem restA514_source_net_matrix :
    sourceOrdinaryNetInt (5 : Basis) (14 : Basis) (by decide) = restA514NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (5 : Basis) (14 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = restA514NetInt := by rw [restA514_source_net_literal]; rfl

theorem restA514_centered_square_lt :
    restA514CenteredSquareInt < restA514RadiusInt^2 := by decide +kernel

theorem restA514_centered_value :
    value restA514CenteredInt = value restA514NetInt -
      (7047/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [restA514CenteredInt,restA514CenterInt,value,raw,scale]
    ring
  · simp [restA514CenteredInt,restA514CenterInt,value,raw,scale,h]

theorem restA514_centered_norm :
    ‖value restA514NetInt -
      (7047/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3729/10^9 : ℝ) := by
  rw [← restA514_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((restA514CenteredInt.re i j)^2+(restA514CenteredInt.im i j)^2)) ≤
        restA514RadiusInt^2 := by
    simpa only [restA514CenteredSquareInt] using le_of_lt restA514_centered_square_lt
  have h := integer_operator_norm_bound restA514CenteredInt restA514RadiusInt
    (by norm_num [restA514RadiusInt,scale]) square
  convert h using 1
  norm_num [restA514RadiusInt,scale]

theorem restA514_qnet_centered_norm :
    ‖sourceOrdinaryQNet (5 : Basis) (14 : Basis) (by decide) -
      (7047/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3735/10^9 : ℝ) := by
  have source := source_ordinary_net_error (5 : Basis) (14 : Basis) (by decide)
  rw [restA514_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (5 : Basis) (14 : Basis) (by decide))
    (value restA514NetInt)
    ((7047/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (5 : Basis) (14 : Basis) (by decide) - value restA514NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse restA514_centered_norm).trans (by norm_num))

theorem restA514_qnet_floor :
    (3312/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (5 : Basis) (14 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (5 : Basis) (14 : Basis) (by decide))
    (ordinary_qnet_hermitian (5 : Basis) (14 : Basis) (by decide))
    (7047/10^9) (3735/10^9) restA514_qnet_centered_norm
  have compare : (3312/10^9 : ℝ) ≤ 7047/10^9-3735/10^9 := by norm_num
  have smaller : (3312/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (7047/10^9-3735/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
