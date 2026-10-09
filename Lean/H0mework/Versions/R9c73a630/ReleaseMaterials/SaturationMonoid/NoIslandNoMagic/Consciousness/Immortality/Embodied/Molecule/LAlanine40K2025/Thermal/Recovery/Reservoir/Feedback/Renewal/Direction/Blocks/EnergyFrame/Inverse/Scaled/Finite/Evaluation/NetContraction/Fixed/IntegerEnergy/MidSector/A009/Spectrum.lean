import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidSector.A009.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def midA009NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable midA009NetTable pairFin pairFin
def midA009CenterInt : Int := 12108*scale/10^9
def midA009RadiusInt : Int := 3863*scale/10^9
def midA009CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => midA009NetInt.re i j - (if i=j then midA009CenterInt else 0), midA009NetInt.im⟩
def midA009CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((midA009CenteredInt.re i j)^2+(midA009CenteredInt.im i j)^2)

theorem midA009_source_net_matrix :
    sourceOrdinaryNetInt (0 : Basis) (9 : Basis) (by decide) = midA009NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (0 : Basis) (9 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = midA009NetInt := by rw [midA009_source_net_literal]; rfl

theorem midA009_centered_square_lt :
    midA009CenteredSquareInt < midA009RadiusInt^2 := by decide +kernel

theorem midA009_centered_value :
    value midA009CenteredInt = value midA009NetInt -
      (12108/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [midA009CenteredInt,midA009CenterInt,value,raw,scale]
    ring
  · simp [midA009CenteredInt,midA009CenterInt,value,raw,scale,h]

theorem midA009_centered_norm :
    ‖value midA009NetInt -
      (12108/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3863/10^9 : ℝ) := by
  rw [← midA009_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((midA009CenteredInt.re i j)^2+(midA009CenteredInt.im i j)^2)) ≤
        midA009RadiusInt^2 := by
    simpa only [midA009CenteredSquareInt] using le_of_lt midA009_centered_square_lt
  have h := integer_operator_norm_bound midA009CenteredInt midA009RadiusInt
    (by norm_num [midA009RadiusInt,scale]) square
  convert h using 1
  norm_num [midA009RadiusInt,scale]

theorem midA009_qnet_centered_norm :
    ‖sourceOrdinaryQNet (0 : Basis) (9 : Basis) (by decide) -
      (12108/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3869/10^9 : ℝ) := by
  have source := source_ordinary_net_error (0 : Basis) (9 : Basis) (by decide)
  rw [midA009_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (0 : Basis) (9 : Basis) (by decide))
    (value midA009NetInt)
    ((12108/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (0 : Basis) (9 : Basis) (by decide) - value midA009NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse midA009_centered_norm).trans (by norm_num))

theorem midA009_qnet_floor :
    (8239/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (0 : Basis) (9 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (0 : Basis) (9 : Basis) (by decide))
    (ordinary_qnet_hermitian (0 : Basis) (9 : Basis) (by decide))
    (12108/10^9) (3869/10^9) midA009_qnet_centered_norm
  have compare : (8239/10^9 : ℝ) ≤ 12108/10^9-3869/10^9 := by norm_num
  have smaller : (8239/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (12108/10^9-3869/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
