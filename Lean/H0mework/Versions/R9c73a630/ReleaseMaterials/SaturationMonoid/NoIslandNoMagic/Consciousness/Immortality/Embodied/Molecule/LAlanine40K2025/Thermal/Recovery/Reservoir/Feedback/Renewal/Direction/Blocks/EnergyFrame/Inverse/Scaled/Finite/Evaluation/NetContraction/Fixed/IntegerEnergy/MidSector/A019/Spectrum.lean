import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidSector.A019.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def midA019NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable midA019NetTable pairFin pairFin
def midA019CenterInt : Int := 11867*scale/10^9
def midA019RadiusInt : Int := 3873*scale/10^9
def midA019CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => midA019NetInt.re i j - (if i=j then midA019CenterInt else 0), midA019NetInt.im⟩
def midA019CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((midA019CenteredInt.re i j)^2+(midA019CenteredInt.im i j)^2)

theorem midA019_source_net_matrix :
    sourceOrdinaryNetInt (0 : Basis) (19 : Basis) (by decide) = midA019NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (0 : Basis) (19 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = midA019NetInt := by rw [midA019_source_net_literal]; rfl

theorem midA019_centered_square_lt :
    midA019CenteredSquareInt < midA019RadiusInt^2 := by decide +kernel

theorem midA019_centered_value :
    value midA019CenteredInt = value midA019NetInt -
      (11867/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [midA019CenteredInt,midA019CenterInt,value,raw,scale]
    ring
  · simp [midA019CenteredInt,midA019CenterInt,value,raw,scale,h]

theorem midA019_centered_norm :
    ‖value midA019NetInt -
      (11867/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3873/10^9 : ℝ) := by
  rw [← midA019_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((midA019CenteredInt.re i j)^2+(midA019CenteredInt.im i j)^2)) ≤
        midA019RadiusInt^2 := by
    simpa only [midA019CenteredSquareInt] using le_of_lt midA019_centered_square_lt
  have h := integer_operator_norm_bound midA019CenteredInt midA019RadiusInt
    (by norm_num [midA019RadiusInt,scale]) square
  convert h using 1
  norm_num [midA019RadiusInt,scale]

theorem midA019_qnet_centered_norm :
    ‖sourceOrdinaryQNet (0 : Basis) (19 : Basis) (by decide) -
      (11867/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3879/10^9 : ℝ) := by
  have source := source_ordinary_net_error (0 : Basis) (19 : Basis) (by decide)
  rw [midA019_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (0 : Basis) (19 : Basis) (by decide))
    (value midA019NetInt)
    ((11867/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (0 : Basis) (19 : Basis) (by decide) - value midA019NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse midA019_centered_norm).trans (by norm_num))

theorem midA019_qnet_floor :
    (7988/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (0 : Basis) (19 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (0 : Basis) (19 : Basis) (by decide))
    (ordinary_qnet_hermitian (0 : Basis) (19 : Basis) (by decide))
    (11867/10^9) (3879/10^9) midA019_qnet_centered_norm
  have compare : (7988/10^9 : ℝ) ≤ 11867/10^9-3879/10^9 := by norm_num
  have smaller : (7988/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (11867/10^9-3879/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
