import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.NearSector.A102.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def nearA102NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable nearA102NetTable pairFin pairFin
def nearA102CenterInt : Int := 19546*scale/10^9
def nearA102RadiusInt : Int := 3733*scale/10^9
def nearA102CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => nearA102NetInt.re i j - (if i=j then nearA102CenterInt else 0), nearA102NetInt.im⟩
def nearA102CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((nearA102CenteredInt.re i j)^2+(nearA102CenteredInt.im i j)^2)

theorem nearA102_source_net_matrix :
    sourceOrdinaryNetInt (1 : Basis) (2 : Basis) (by decide) = nearA102NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (1 : Basis) (2 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = nearA102NetInt := by rw [nearA102_source_net_literal]; rfl

theorem nearA102_centered_square_lt :
    nearA102CenteredSquareInt < nearA102RadiusInt^2 := by decide +kernel

theorem nearA102_centered_value :
    value nearA102CenteredInt = value nearA102NetInt -
      (19546/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [nearA102CenteredInt,nearA102CenterInt,value,raw,scale]
    ring
  · simp [nearA102CenteredInt,nearA102CenterInt,value,raw,scale,h]

theorem nearA102_centered_norm :
    ‖value nearA102NetInt -
      (19546/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3733/10^9 : ℝ) := by
  rw [← nearA102_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((nearA102CenteredInt.re i j)^2+(nearA102CenteredInt.im i j)^2)) ≤
        nearA102RadiusInt^2 := by
    simpa only [nearA102CenteredSquareInt] using le_of_lt nearA102_centered_square_lt
  have h := integer_operator_norm_bound nearA102CenteredInt nearA102RadiusInt
    (by norm_num [nearA102RadiusInt,scale]) square
  convert h using 1
  norm_num [nearA102RadiusInt,scale]

theorem nearA102_qnet_centered_norm :
    ‖sourceOrdinaryQNet (1 : Basis) (2 : Basis) (by decide) -
      (19546/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3739/10^9 : ℝ) := by
  have source := source_ordinary_net_error (1 : Basis) (2 : Basis) (by decide)
  rw [nearA102_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (1 : Basis) (2 : Basis) (by decide))
    (value nearA102NetInt)
    ((19546/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (1 : Basis) (2 : Basis) (by decide) - value nearA102NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse nearA102_centered_norm).trans (by norm_num))

theorem nearA102_qnet_floor :
    (15807/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (1 : Basis) (2 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (1 : Basis) (2 : Basis) (by decide))
    (ordinary_qnet_hermitian (1 : Basis) (2 : Basis) (by decide))
    (19546/10^9) (3739/10^9) nearA102_qnet_centered_norm
  have compare : (15807/10^9 : ℝ) ≤ 19546/10^9-3739/10^9 := by norm_num
  have smaller : (15807/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (19546/10^9-3739/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
