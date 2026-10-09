import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidSector.A109.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def midA109NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable midA109NetTable pairFin pairFin
def midA109CenterInt : Int := 12097*scale/10^9
def midA109RadiusInt : Int := 3863*scale/10^9
def midA109CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => midA109NetInt.re i j - (if i=j then midA109CenterInt else 0), midA109NetInt.im⟩
def midA109CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((midA109CenteredInt.re i j)^2+(midA109CenteredInt.im i j)^2)

theorem midA109_source_net_matrix :
    sourceOrdinaryNetInt (1 : Basis) (9 : Basis) (by decide) = midA109NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (1 : Basis) (9 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = midA109NetInt := by rw [midA109_source_net_literal]; rfl

theorem midA109_centered_square_lt :
    midA109CenteredSquareInt < midA109RadiusInt^2 := by decide +kernel

theorem midA109_centered_value :
    value midA109CenteredInt = value midA109NetInt -
      (12097/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [midA109CenteredInt,midA109CenterInt,value,raw,scale]
    ring
  · simp [midA109CenteredInt,midA109CenterInt,value,raw,scale,h]

theorem midA109_centered_norm :
    ‖value midA109NetInt -
      (12097/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3863/10^9 : ℝ) := by
  rw [← midA109_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((midA109CenteredInt.re i j)^2+(midA109CenteredInt.im i j)^2)) ≤
        midA109RadiusInt^2 := by
    simpa only [midA109CenteredSquareInt] using le_of_lt midA109_centered_square_lt
  have h := integer_operator_norm_bound midA109CenteredInt midA109RadiusInt
    (by norm_num [midA109RadiusInt,scale]) square
  convert h using 1
  norm_num [midA109RadiusInt,scale]

theorem midA109_qnet_centered_norm :
    ‖sourceOrdinaryQNet (1 : Basis) (9 : Basis) (by decide) -
      (12097/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3869/10^9 : ℝ) := by
  have source := source_ordinary_net_error (1 : Basis) (9 : Basis) (by decide)
  rw [midA109_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (1 : Basis) (9 : Basis) (by decide))
    (value midA109NetInt)
    ((12097/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (1 : Basis) (9 : Basis) (by decide) - value midA109NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse midA109_centered_norm).trans (by norm_num))

theorem midA109_qnet_floor :
    (8228/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (1 : Basis) (9 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (1 : Basis) (9 : Basis) (by decide))
    (ordinary_qnet_hermitian (1 : Basis) (9 : Basis) (by decide))
    (12097/10^9) (3869/10^9) midA109_qnet_centered_norm
  have compare : (8228/10^9 : ℝ) ≤ 12097/10^9-3869/10^9 := by norm_num
  have smaller : (8228/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (12097/10^9-3869/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
