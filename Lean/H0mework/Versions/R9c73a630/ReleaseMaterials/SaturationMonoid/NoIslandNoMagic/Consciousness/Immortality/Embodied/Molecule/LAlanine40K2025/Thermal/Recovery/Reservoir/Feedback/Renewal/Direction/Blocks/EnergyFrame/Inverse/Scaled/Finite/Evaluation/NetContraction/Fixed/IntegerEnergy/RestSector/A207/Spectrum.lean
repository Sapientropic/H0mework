import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.RestSector.A207.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def restA207NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable restA207NetTable pairFin pairFin
def restA207CenterInt : Int := 9602*scale/10^9
def restA207RadiusInt : Int := 3779*scale/10^9
def restA207CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => restA207NetInt.re i j - (if i=j then restA207CenterInt else 0), restA207NetInt.im⟩
def restA207CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((restA207CenteredInt.re i j)^2+(restA207CenteredInt.im i j)^2)

theorem restA207_source_net_matrix :
    sourceOrdinaryNetInt (2 : Basis) (7 : Basis) (by decide) = restA207NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (2 : Basis) (7 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = restA207NetInt := by rw [restA207_source_net_literal]; rfl

theorem restA207_centered_square_lt :
    restA207CenteredSquareInt < restA207RadiusInt^2 := by decide +kernel

theorem restA207_centered_value :
    value restA207CenteredInt = value restA207NetInt -
      (9602/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [restA207CenteredInt,restA207CenterInt,value,raw,scale]
    ring
  · simp [restA207CenteredInt,restA207CenterInt,value,raw,scale,h]

theorem restA207_centered_norm :
    ‖value restA207NetInt -
      (9602/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3779/10^9 : ℝ) := by
  rw [← restA207_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((restA207CenteredInt.re i j)^2+(restA207CenteredInt.im i j)^2)) ≤
        restA207RadiusInt^2 := by
    simpa only [restA207CenteredSquareInt] using le_of_lt restA207_centered_square_lt
  have h := integer_operator_norm_bound restA207CenteredInt restA207RadiusInt
    (by norm_num [restA207RadiusInt,scale]) square
  convert h using 1
  norm_num [restA207RadiusInt,scale]

theorem restA207_qnet_centered_norm :
    ‖sourceOrdinaryQNet (2 : Basis) (7 : Basis) (by decide) -
      (9602/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3785/10^9 : ℝ) := by
  have source := source_ordinary_net_error (2 : Basis) (7 : Basis) (by decide)
  rw [restA207_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (2 : Basis) (7 : Basis) (by decide))
    (value restA207NetInt)
    ((9602/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (2 : Basis) (7 : Basis) (by decide) - value restA207NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse restA207_centered_norm).trans (by norm_num))

theorem restA207_qnet_floor :
    (5817/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (2 : Basis) (7 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (2 : Basis) (7 : Basis) (by decide))
    (ordinary_qnet_hermitian (2 : Basis) (7 : Basis) (by decide))
    (9602/10^9) (3785/10^9) restA207_qnet_centered_norm
  have compare : (5817/10^9 : ℝ) ≤ 9602/10^9-3785/10^9 := by norm_num
  have smaller : (5817/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (9602/10^9-3785/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
