import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidSector.A116.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def midA116NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable midA116NetTable pairFin pairFin
def midA116CenterInt : Int := 11911*scale/10^9
def midA116RadiusInt : Int := 3870*scale/10^9
def midA116CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => midA116NetInt.re i j - (if i=j then midA116CenterInt else 0), midA116NetInt.im⟩
def midA116CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((midA116CenteredInt.re i j)^2+(midA116CenteredInt.im i j)^2)

theorem midA116_source_net_matrix :
    sourceOrdinaryNetInt (1 : Basis) (16 : Basis) (by decide) = midA116NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (1 : Basis) (16 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = midA116NetInt := by rw [midA116_source_net_literal]; rfl

theorem midA116_centered_square_lt :
    midA116CenteredSquareInt < midA116RadiusInt^2 := by decide +kernel

theorem midA116_centered_value :
    value midA116CenteredInt = value midA116NetInt -
      (11911/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [midA116CenteredInt,midA116CenterInt,value,raw,scale]
    ring
  · simp [midA116CenteredInt,midA116CenterInt,value,raw,scale,h]

theorem midA116_centered_norm :
    ‖value midA116NetInt -
      (11911/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3870/10^9 : ℝ) := by
  rw [← midA116_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((midA116CenteredInt.re i j)^2+(midA116CenteredInt.im i j)^2)) ≤
        midA116RadiusInt^2 := by
    simpa only [midA116CenteredSquareInt] using le_of_lt midA116_centered_square_lt
  have h := integer_operator_norm_bound midA116CenteredInt midA116RadiusInt
    (by norm_num [midA116RadiusInt,scale]) square
  convert h using 1
  norm_num [midA116RadiusInt,scale]

theorem midA116_qnet_centered_norm :
    ‖sourceOrdinaryQNet (1 : Basis) (16 : Basis) (by decide) -
      (11911/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3876/10^9 : ℝ) := by
  have source := source_ordinary_net_error (1 : Basis) (16 : Basis) (by decide)
  rw [midA116_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (1 : Basis) (16 : Basis) (by decide))
    (value midA116NetInt)
    ((11911/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (1 : Basis) (16 : Basis) (by decide) - value midA116NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse midA116_centered_norm).trans (by norm_num))

theorem midA116_qnet_floor :
    (8035/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (1 : Basis) (16 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (1 : Basis) (16 : Basis) (by decide))
    (ordinary_qnet_hermitian (1 : Basis) (16 : Basis) (by decide))
    (11911/10^9) (3876/10^9) midA116_qnet_centered_norm
  have compare : (8035/10^9 : ℝ) ≤ 11911/10^9-3876/10^9 := by norm_num
  have smaller : (8035/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (11911/10^9-3876/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
