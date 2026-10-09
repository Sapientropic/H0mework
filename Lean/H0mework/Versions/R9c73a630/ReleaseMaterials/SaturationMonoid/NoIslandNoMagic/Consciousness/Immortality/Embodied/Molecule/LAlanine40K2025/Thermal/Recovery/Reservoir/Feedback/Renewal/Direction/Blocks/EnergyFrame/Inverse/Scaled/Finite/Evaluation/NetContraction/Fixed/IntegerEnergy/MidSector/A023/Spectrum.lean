import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidSector.A023.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def midA023NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable midA023NetTable pairFin pairFin
def midA023CenterInt : Int := 11785*scale/10^9
def midA023RadiusInt : Int := 3876*scale/10^9
def midA023CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => midA023NetInt.re i j - (if i=j then midA023CenterInt else 0), midA023NetInt.im⟩
def midA023CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((midA023CenteredInt.re i j)^2+(midA023CenteredInt.im i j)^2)

theorem midA023_source_net_matrix :
    sourceOrdinaryNetInt (0 : Basis) (23 : Basis) (by decide) = midA023NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (0 : Basis) (23 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = midA023NetInt := by rw [midA023_source_net_literal]; rfl

theorem midA023_centered_square_lt :
    midA023CenteredSquareInt < midA023RadiusInt^2 := by decide +kernel

theorem midA023_centered_value :
    value midA023CenteredInt = value midA023NetInt -
      (11785/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [midA023CenteredInt,midA023CenterInt,value,raw,scale]
    ring
  · simp [midA023CenteredInt,midA023CenterInt,value,raw,scale,h]

theorem midA023_centered_norm :
    ‖value midA023NetInt -
      (11785/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3876/10^9 : ℝ) := by
  rw [← midA023_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((midA023CenteredInt.re i j)^2+(midA023CenteredInt.im i j)^2)) ≤
        midA023RadiusInt^2 := by
    simpa only [midA023CenteredSquareInt] using le_of_lt midA023_centered_square_lt
  have h := integer_operator_norm_bound midA023CenteredInt midA023RadiusInt
    (by norm_num [midA023RadiusInt,scale]) square
  convert h using 1
  norm_num [midA023RadiusInt,scale]

theorem midA023_qnet_centered_norm :
    ‖sourceOrdinaryQNet (0 : Basis) (23 : Basis) (by decide) -
      (11785/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3882/10^9 : ℝ) := by
  have source := source_ordinary_net_error (0 : Basis) (23 : Basis) (by decide)
  rw [midA023_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (0 : Basis) (23 : Basis) (by decide))
    (value midA023NetInt)
    ((11785/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (0 : Basis) (23 : Basis) (by decide) - value midA023NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse midA023_centered_norm).trans (by norm_num))

theorem midA023_qnet_floor :
    (7903/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (0 : Basis) (23 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (0 : Basis) (23 : Basis) (by decide))
    (ordinary_qnet_hermitian (0 : Basis) (23 : Basis) (by decide))
    (11785/10^9) (3882/10^9) midA023_qnet_centered_norm
  have compare : (7903/10^9 : ℝ) ≤ 11785/10^9-3882/10^9 := by norm_num
  have smaller : (7903/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (11785/10^9-3882/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
