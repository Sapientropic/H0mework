import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.RestSector.A513.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def restA513NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable restA513NetTable pairFin pairFin
def restA513CenterInt : Int := 7066*scale/10^9
def restA513RadiusInt : Int := 3728*scale/10^9
def restA513CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => restA513NetInt.re i j - (if i=j then restA513CenterInt else 0), restA513NetInt.im⟩
def restA513CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((restA513CenteredInt.re i j)^2+(restA513CenteredInt.im i j)^2)

theorem restA513_source_net_matrix :
    sourceOrdinaryNetInt (5 : Basis) (13 : Basis) (by decide) = restA513NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (5 : Basis) (13 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = restA513NetInt := by rw [restA513_source_net_literal]; rfl

theorem restA513_centered_square_lt :
    restA513CenteredSquareInt < restA513RadiusInt^2 := by decide +kernel

theorem restA513_centered_value :
    value restA513CenteredInt = value restA513NetInt -
      (7066/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [restA513CenteredInt,restA513CenterInt,value,raw,scale]
    ring
  · simp [restA513CenteredInt,restA513CenterInt,value,raw,scale,h]

theorem restA513_centered_norm :
    ‖value restA513NetInt -
      (7066/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3728/10^9 : ℝ) := by
  rw [← restA513_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((restA513CenteredInt.re i j)^2+(restA513CenteredInt.im i j)^2)) ≤
        restA513RadiusInt^2 := by
    simpa only [restA513CenteredSquareInt] using le_of_lt restA513_centered_square_lt
  have h := integer_operator_norm_bound restA513CenteredInt restA513RadiusInt
    (by norm_num [restA513RadiusInt,scale]) square
  convert h using 1
  norm_num [restA513RadiusInt,scale]

theorem restA513_qnet_centered_norm :
    ‖sourceOrdinaryQNet (5 : Basis) (13 : Basis) (by decide) -
      (7066/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3734/10^9 : ℝ) := by
  have source := source_ordinary_net_error (5 : Basis) (13 : Basis) (by decide)
  rw [restA513_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (5 : Basis) (13 : Basis) (by decide))
    (value restA513NetInt)
    ((7066/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (5 : Basis) (13 : Basis) (by decide) - value restA513NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse restA513_centered_norm).trans (by norm_num))

theorem restA513_qnet_floor :
    (3332/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (5 : Basis) (13 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (5 : Basis) (13 : Basis) (by decide))
    (ordinary_qnet_hermitian (5 : Basis) (13 : Basis) (by decide))
    (7066/10^9) (3734/10^9) restA513_qnet_centered_norm
  have compare : (3332/10^9 : ℝ) ≤ 7066/10^9-3734/10^9 := by norm_num
  have smaller : (3332/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (7066/10^9-3734/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
