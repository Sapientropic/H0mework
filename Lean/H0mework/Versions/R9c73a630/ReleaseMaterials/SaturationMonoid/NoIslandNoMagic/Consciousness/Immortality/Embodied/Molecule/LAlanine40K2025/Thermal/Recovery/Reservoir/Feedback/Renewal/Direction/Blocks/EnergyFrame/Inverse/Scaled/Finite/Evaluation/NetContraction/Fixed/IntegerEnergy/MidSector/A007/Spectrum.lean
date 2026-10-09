import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidSector.A007.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def midA007NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable midA007NetTable pairFin pairFin
def midA007CenterInt : Int := 12180*scale/10^9
def midA007RadiusInt : Int := 3861*scale/10^9
def midA007CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => midA007NetInt.re i j - (if i=j then midA007CenterInt else 0), midA007NetInt.im⟩
def midA007CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((midA007CenteredInt.re i j)^2+(midA007CenteredInt.im i j)^2)

theorem midA007_source_net_matrix :
    sourceOrdinaryNetInt (0 : Basis) (7 : Basis) (by decide) = midA007NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (0 : Basis) (7 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = midA007NetInt := by rw [midA007_source_net_literal]; rfl

theorem midA007_centered_square_lt :
    midA007CenteredSquareInt < midA007RadiusInt^2 := by decide +kernel

theorem midA007_centered_value :
    value midA007CenteredInt = value midA007NetInt -
      (12180/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [midA007CenteredInt,midA007CenterInt,value,raw,scale]
    ring
  · simp [midA007CenteredInt,midA007CenterInt,value,raw,scale,h]

theorem midA007_centered_norm :
    ‖value midA007NetInt -
      (12180/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3861/10^9 : ℝ) := by
  rw [← midA007_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((midA007CenteredInt.re i j)^2+(midA007CenteredInt.im i j)^2)) ≤
        midA007RadiusInt^2 := by
    simpa only [midA007CenteredSquareInt] using le_of_lt midA007_centered_square_lt
  have h := integer_operator_norm_bound midA007CenteredInt midA007RadiusInt
    (by norm_num [midA007RadiusInt,scale]) square
  convert h using 1
  norm_num [midA007RadiusInt,scale]

theorem midA007_qnet_centered_norm :
    ‖sourceOrdinaryQNet (0 : Basis) (7 : Basis) (by decide) -
      (12180/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3867/10^9 : ℝ) := by
  have source := source_ordinary_net_error (0 : Basis) (7 : Basis) (by decide)
  rw [midA007_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (0 : Basis) (7 : Basis) (by decide))
    (value midA007NetInt)
    ((12180/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (0 : Basis) (7 : Basis) (by decide) - value midA007NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse midA007_centered_norm).trans (by norm_num))

theorem midA007_qnet_floor :
    (8313/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (0 : Basis) (7 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (0 : Basis) (7 : Basis) (by decide))
    (ordinary_qnet_hermitian (0 : Basis) (7 : Basis) (by decide))
    (12180/10^9) (3867/10^9) midA007_qnet_centered_norm
  have compare : (8313/10^9 : ℝ) ≤ 12180/10^9-3867/10^9 := by norm_num
  have smaller : (8313/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (12180/10^9-3867/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
