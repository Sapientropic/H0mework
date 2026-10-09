import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.RestSector.A203.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def restA203NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable restA203NetTable pairFin pairFin
def restA203CenterInt : Int := 14516*scale/10^9
def restA203RadiusInt : Int := 3718*scale/10^9
def restA203CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => restA203NetInt.re i j - (if i=j then restA203CenterInt else 0), restA203NetInt.im⟩
def restA203CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((restA203CenteredInt.re i j)^2+(restA203CenteredInt.im i j)^2)

theorem restA203_source_net_matrix :
    sourceOrdinaryNetInt (2 : Basis) (3 : Basis) (by decide) = restA203NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (2 : Basis) (3 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = restA203NetInt := by rw [restA203_source_net_literal]; rfl

theorem restA203_centered_square_lt :
    restA203CenteredSquareInt < restA203RadiusInt^2 := by decide +kernel

theorem restA203_centered_value :
    value restA203CenteredInt = value restA203NetInt -
      (14516/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [restA203CenteredInt,restA203CenterInt,value,raw,scale]
    ring
  · simp [restA203CenteredInt,restA203CenterInt,value,raw,scale,h]

theorem restA203_centered_norm :
    ‖value restA203NetInt -
      (14516/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3718/10^9 : ℝ) := by
  rw [← restA203_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((restA203CenteredInt.re i j)^2+(restA203CenteredInt.im i j)^2)) ≤
        restA203RadiusInt^2 := by
    simpa only [restA203CenteredSquareInt] using le_of_lt restA203_centered_square_lt
  have h := integer_operator_norm_bound restA203CenteredInt restA203RadiusInt
    (by norm_num [restA203RadiusInt,scale]) square
  convert h using 1
  norm_num [restA203RadiusInt,scale]

theorem restA203_qnet_centered_norm :
    ‖sourceOrdinaryQNet (2 : Basis) (3 : Basis) (by decide) -
      (14516/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3724/10^9 : ℝ) := by
  have source := source_ordinary_net_error (2 : Basis) (3 : Basis) (by decide)
  rw [restA203_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (2 : Basis) (3 : Basis) (by decide))
    (value restA203NetInt)
    ((14516/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (2 : Basis) (3 : Basis) (by decide) - value restA203NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse restA203_centered_norm).trans (by norm_num))

theorem restA203_qnet_floor :
    (10792/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (2 : Basis) (3 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (2 : Basis) (3 : Basis) (by decide))
    (ordinary_qnet_hermitian (2 : Basis) (3 : Basis) (by decide))
    (14516/10^9) (3724/10^9) restA203_qnet_centered_norm
  have compare : (10792/10^9 : ℝ) ≤ 14516/10^9-3724/10^9 := by norm_num
  have smaller : (10792/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (14516/10^9-3724/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
