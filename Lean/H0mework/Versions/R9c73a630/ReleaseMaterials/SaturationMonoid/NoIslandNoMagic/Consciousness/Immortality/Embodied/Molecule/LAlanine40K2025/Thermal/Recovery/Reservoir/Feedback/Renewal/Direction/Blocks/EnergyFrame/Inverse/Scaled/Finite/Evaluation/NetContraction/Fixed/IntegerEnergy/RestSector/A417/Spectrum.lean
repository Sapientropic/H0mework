import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.RestSector.A417.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def restA417NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable restA417NetTable pairFin pairFin
def restA417CenterInt : Int := 7035*scale/10^9
def restA417RadiusInt : Int := 3730*scale/10^9
def restA417CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => restA417NetInt.re i j - (if i=j then restA417CenterInt else 0), restA417NetInt.im⟩
def restA417CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((restA417CenteredInt.re i j)^2+(restA417CenteredInt.im i j)^2)

theorem restA417_source_net_matrix :
    sourceOrdinaryNetInt (4 : Basis) (17 : Basis) (by decide) = restA417NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (4 : Basis) (17 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = restA417NetInt := by rw [restA417_source_net_literal]; rfl

theorem restA417_centered_square_lt :
    restA417CenteredSquareInt < restA417RadiusInt^2 := by decide +kernel

theorem restA417_centered_value :
    value restA417CenteredInt = value restA417NetInt -
      (7035/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [restA417CenteredInt,restA417CenterInt,value,raw,scale]
    ring
  · simp [restA417CenteredInt,restA417CenterInt,value,raw,scale,h]

theorem restA417_centered_norm :
    ‖value restA417NetInt -
      (7035/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3730/10^9 : ℝ) := by
  rw [← restA417_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((restA417CenteredInt.re i j)^2+(restA417CenteredInt.im i j)^2)) ≤
        restA417RadiusInt^2 := by
    simpa only [restA417CenteredSquareInt] using le_of_lt restA417_centered_square_lt
  have h := integer_operator_norm_bound restA417CenteredInt restA417RadiusInt
    (by norm_num [restA417RadiusInt,scale]) square
  convert h using 1
  norm_num [restA417RadiusInt,scale]

theorem restA417_qnet_centered_norm :
    ‖sourceOrdinaryQNet (4 : Basis) (17 : Basis) (by decide) -
      (7035/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3736/10^9 : ℝ) := by
  have source := source_ordinary_net_error (4 : Basis) (17 : Basis) (by decide)
  rw [restA417_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (4 : Basis) (17 : Basis) (by decide))
    (value restA417NetInt)
    ((7035/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (4 : Basis) (17 : Basis) (by decide) - value restA417NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse restA417_centered_norm).trans (by norm_num))

theorem restA417_qnet_floor :
    (3299/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (4 : Basis) (17 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (4 : Basis) (17 : Basis) (by decide))
    (ordinary_qnet_hermitian (4 : Basis) (17 : Basis) (by decide))
    (7035/10^9) (3736/10^9) restA417_qnet_centered_norm
  have compare : (3299/10^9 : ℝ) ≤ 7035/10^9-3736/10^9 := by norm_num
  have smaller : (3299/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (7035/10^9-3736/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
