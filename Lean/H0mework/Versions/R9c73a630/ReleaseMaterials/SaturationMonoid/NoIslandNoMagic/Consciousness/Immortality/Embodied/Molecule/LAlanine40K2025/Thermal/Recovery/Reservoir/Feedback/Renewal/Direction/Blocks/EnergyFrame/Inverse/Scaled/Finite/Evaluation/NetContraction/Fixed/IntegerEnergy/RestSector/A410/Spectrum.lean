import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.RestSector.A410.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def restA410NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable restA410NetTable pairFin pairFin
def restA410CenterInt : Int := 7175*scale/10^9
def restA410RadiusInt : Int := 3728*scale/10^9
def restA410CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => restA410NetInt.re i j - (if i=j then restA410CenterInt else 0), restA410NetInt.im⟩
def restA410CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((restA410CenteredInt.re i j)^2+(restA410CenteredInt.im i j)^2)

theorem restA410_source_net_matrix :
    sourceOrdinaryNetInt (4 : Basis) (10 : Basis) (by decide) = restA410NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (4 : Basis) (10 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = restA410NetInt := by rw [restA410_source_net_literal]; rfl

theorem restA410_centered_square_lt :
    restA410CenteredSquareInt < restA410RadiusInt^2 := by decide +kernel

theorem restA410_centered_value :
    value restA410CenteredInt = value restA410NetInt -
      (7175/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [restA410CenteredInt,restA410CenterInt,value,raw,scale]
    ring
  · simp [restA410CenteredInt,restA410CenterInt,value,raw,scale,h]

theorem restA410_centered_norm :
    ‖value restA410NetInt -
      (7175/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3728/10^9 : ℝ) := by
  rw [← restA410_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((restA410CenteredInt.re i j)^2+(restA410CenteredInt.im i j)^2)) ≤
        restA410RadiusInt^2 := by
    simpa only [restA410CenteredSquareInt] using le_of_lt restA410_centered_square_lt
  have h := integer_operator_norm_bound restA410CenteredInt restA410RadiusInt
    (by norm_num [restA410RadiusInt,scale]) square
  convert h using 1
  norm_num [restA410RadiusInt,scale]

theorem restA410_qnet_centered_norm :
    ‖sourceOrdinaryQNet (4 : Basis) (10 : Basis) (by decide) -
      (7175/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3734/10^9 : ℝ) := by
  have source := source_ordinary_net_error (4 : Basis) (10 : Basis) (by decide)
  rw [restA410_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (4 : Basis) (10 : Basis) (by decide))
    (value restA410NetInt)
    ((7175/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (4 : Basis) (10 : Basis) (by decide) - value restA410NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse restA410_centered_norm).trans (by norm_num))

theorem restA410_qnet_floor :
    (3441/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (4 : Basis) (10 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (4 : Basis) (10 : Basis) (by decide))
    (ordinary_qnet_hermitian (4 : Basis) (10 : Basis) (by decide))
    (7175/10^9) (3734/10^9) restA410_qnet_centered_norm
  have compare : (3441/10^9 : ℝ) ≤ 7175/10^9-3734/10^9 := by norm_num
  have smaller : (3441/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (7175/10^9-3734/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
