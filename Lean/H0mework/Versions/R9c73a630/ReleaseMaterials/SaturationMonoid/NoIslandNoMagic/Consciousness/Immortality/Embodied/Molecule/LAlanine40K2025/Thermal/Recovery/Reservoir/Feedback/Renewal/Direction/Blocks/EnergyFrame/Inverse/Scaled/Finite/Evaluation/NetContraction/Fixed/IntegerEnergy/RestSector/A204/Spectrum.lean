import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.RestSector.A204.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def restA204NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable restA204NetTable pairFin pairFin
def restA204CenterInt : Int := 14509*scale/10^9
def restA204RadiusInt : Int := 3718*scale/10^9
def restA204CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => restA204NetInt.re i j - (if i=j then restA204CenterInt else 0), restA204NetInt.im⟩
def restA204CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((restA204CenteredInt.re i j)^2+(restA204CenteredInt.im i j)^2)

theorem restA204_source_net_matrix :
    sourceOrdinaryNetInt (2 : Basis) (4 : Basis) (by decide) = restA204NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (2 : Basis) (4 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = restA204NetInt := by rw [restA204_source_net_literal]; rfl

theorem restA204_centered_square_lt :
    restA204CenteredSquareInt < restA204RadiusInt^2 := by decide +kernel

theorem restA204_centered_value :
    value restA204CenteredInt = value restA204NetInt -
      (14509/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [restA204CenteredInt,restA204CenterInt,value,raw,scale]
    ring
  · simp [restA204CenteredInt,restA204CenterInt,value,raw,scale,h]

theorem restA204_centered_norm :
    ‖value restA204NetInt -
      (14509/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3718/10^9 : ℝ) := by
  rw [← restA204_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((restA204CenteredInt.re i j)^2+(restA204CenteredInt.im i j)^2)) ≤
        restA204RadiusInt^2 := by
    simpa only [restA204CenteredSquareInt] using le_of_lt restA204_centered_square_lt
  have h := integer_operator_norm_bound restA204CenteredInt restA204RadiusInt
    (by norm_num [restA204RadiusInt,scale]) square
  convert h using 1
  norm_num [restA204RadiusInt,scale]

theorem restA204_qnet_centered_norm :
    ‖sourceOrdinaryQNet (2 : Basis) (4 : Basis) (by decide) -
      (14509/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3724/10^9 : ℝ) := by
  have source := source_ordinary_net_error (2 : Basis) (4 : Basis) (by decide)
  rw [restA204_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (2 : Basis) (4 : Basis) (by decide))
    (value restA204NetInt)
    ((14509/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (2 : Basis) (4 : Basis) (by decide) - value restA204NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse restA204_centered_norm).trans (by norm_num))

theorem restA204_qnet_floor :
    (10785/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (2 : Basis) (4 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (2 : Basis) (4 : Basis) (by decide))
    (ordinary_qnet_hermitian (2 : Basis) (4 : Basis) (by decide))
    (14509/10^9) (3724/10^9) restA204_qnet_centered_norm
  have compare : (10785/10^9 : ℝ) ≤ 14509/10^9-3724/10^9 := by norm_num
  have smaller : (10785/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (14509/10^9-3724/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
