import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidSector.A015.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def midA015NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable midA015NetTable pairFin pairFin
def midA015CenterInt : Int := 11925*scale/10^9
def midA015RadiusInt : Int := 3870*scale/10^9
def midA015CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => midA015NetInt.re i j - (if i=j then midA015CenterInt else 0), midA015NetInt.im⟩
def midA015CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((midA015CenteredInt.re i j)^2+(midA015CenteredInt.im i j)^2)

theorem midA015_source_net_matrix :
    sourceOrdinaryNetInt (0 : Basis) (15 : Basis) (by decide) = midA015NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (0 : Basis) (15 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = midA015NetInt := by rw [midA015_source_net_literal]; rfl

theorem midA015_centered_square_lt :
    midA015CenteredSquareInt < midA015RadiusInt^2 := by decide +kernel

theorem midA015_centered_value :
    value midA015CenteredInt = value midA015NetInt -
      (11925/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [midA015CenteredInt,midA015CenterInt,value,raw,scale]
    ring
  · simp [midA015CenteredInt,midA015CenterInt,value,raw,scale,h]

theorem midA015_centered_norm :
    ‖value midA015NetInt -
      (11925/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3870/10^9 : ℝ) := by
  rw [← midA015_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((midA015CenteredInt.re i j)^2+(midA015CenteredInt.im i j)^2)) ≤
        midA015RadiusInt^2 := by
    simpa only [midA015CenteredSquareInt] using le_of_lt midA015_centered_square_lt
  have h := integer_operator_norm_bound midA015CenteredInt midA015RadiusInt
    (by norm_num [midA015RadiusInt,scale]) square
  convert h using 1
  norm_num [midA015RadiusInt,scale]

theorem midA015_qnet_centered_norm :
    ‖sourceOrdinaryQNet (0 : Basis) (15 : Basis) (by decide) -
      (11925/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3876/10^9 : ℝ) := by
  have source := source_ordinary_net_error (0 : Basis) (15 : Basis) (by decide)
  rw [midA015_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (0 : Basis) (15 : Basis) (by decide))
    (value midA015NetInt)
    ((11925/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (0 : Basis) (15 : Basis) (by decide) - value midA015NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse midA015_centered_norm).trans (by norm_num))

theorem midA015_qnet_floor :
    (8049/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (0 : Basis) (15 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (0 : Basis) (15 : Basis) (by decide))
    (ordinary_qnet_hermitian (0 : Basis) (15 : Basis) (by decide))
    (11925/10^9) (3876/10^9) midA015_qnet_centered_norm
  have compare : (8049/10^9 : ℝ) ≤ 11925/10^9-3876/10^9 := by norm_num
  have smaller : (8049/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (11925/10^9-3876/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
