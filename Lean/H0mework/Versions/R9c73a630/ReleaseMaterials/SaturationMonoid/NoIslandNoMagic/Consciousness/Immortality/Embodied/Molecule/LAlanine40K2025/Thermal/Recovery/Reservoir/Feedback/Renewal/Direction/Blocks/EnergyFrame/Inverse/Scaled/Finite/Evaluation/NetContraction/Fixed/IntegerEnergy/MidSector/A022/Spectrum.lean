import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidSector.A022.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def midA022NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable midA022NetTable pairFin pairFin
def midA022CenterInt : Int := 11798*scale/10^9
def midA022RadiusInt : Int := 3876*scale/10^9
def midA022CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => midA022NetInt.re i j - (if i=j then midA022CenterInt else 0), midA022NetInt.im⟩
def midA022CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((midA022CenteredInt.re i j)^2+(midA022CenteredInt.im i j)^2)

theorem midA022_source_net_matrix :
    sourceOrdinaryNetInt (0 : Basis) (22 : Basis) (by decide) = midA022NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (0 : Basis) (22 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = midA022NetInt := by rw [midA022_source_net_literal]; rfl

theorem midA022_centered_square_lt :
    midA022CenteredSquareInt < midA022RadiusInt^2 := by decide +kernel

theorem midA022_centered_value :
    value midA022CenteredInt = value midA022NetInt -
      (11798/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [midA022CenteredInt,midA022CenterInt,value,raw,scale]
    ring
  · simp [midA022CenteredInt,midA022CenterInt,value,raw,scale,h]

theorem midA022_centered_norm :
    ‖value midA022NetInt -
      (11798/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3876/10^9 : ℝ) := by
  rw [← midA022_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((midA022CenteredInt.re i j)^2+(midA022CenteredInt.im i j)^2)) ≤
        midA022RadiusInt^2 := by
    simpa only [midA022CenteredSquareInt] using le_of_lt midA022_centered_square_lt
  have h := integer_operator_norm_bound midA022CenteredInt midA022RadiusInt
    (by norm_num [midA022RadiusInt,scale]) square
  convert h using 1
  norm_num [midA022RadiusInt,scale]

theorem midA022_qnet_centered_norm :
    ‖sourceOrdinaryQNet (0 : Basis) (22 : Basis) (by decide) -
      (11798/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3882/10^9 : ℝ) := by
  have source := source_ordinary_net_error (0 : Basis) (22 : Basis) (by decide)
  rw [midA022_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (0 : Basis) (22 : Basis) (by decide))
    (value midA022NetInt)
    ((11798/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (0 : Basis) (22 : Basis) (by decide) - value midA022NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse midA022_centered_norm).trans (by norm_num))

theorem midA022_qnet_floor :
    (7916/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (0 : Basis) (22 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (0 : Basis) (22 : Basis) (by decide))
    (ordinary_qnet_hermitian (0 : Basis) (22 : Basis) (by decide))
    (11798/10^9) (3882/10^9) midA022_qnet_centered_norm
  have compare : (7916/10^9 : ℝ) ≤ 11798/10^9-3882/10^9 := by norm_num
  have smaller : (7916/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (11798/10^9-3882/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
