import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidSector.A112.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def midA112NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable midA112NetTable pairFin pairFin
def midA112CenterInt : Int := 12029*scale/10^9
def midA112RadiusInt : Int := 3866*scale/10^9
def midA112CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => midA112NetInt.re i j - (if i=j then midA112CenterInt else 0), midA112NetInt.im⟩
def midA112CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((midA112CenteredInt.re i j)^2+(midA112CenteredInt.im i j)^2)

theorem midA112_source_net_matrix :
    sourceOrdinaryNetInt (1 : Basis) (12 : Basis) (by decide) = midA112NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (1 : Basis) (12 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = midA112NetInt := by rw [midA112_source_net_literal]; rfl

theorem midA112_centered_square_lt :
    midA112CenteredSquareInt < midA112RadiusInt^2 := by decide +kernel

theorem midA112_centered_value :
    value midA112CenteredInt = value midA112NetInt -
      (12029/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [midA112CenteredInt,midA112CenterInt,value,raw,scale]
    ring
  · simp [midA112CenteredInt,midA112CenterInt,value,raw,scale,h]

theorem midA112_centered_norm :
    ‖value midA112NetInt -
      (12029/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3866/10^9 : ℝ) := by
  rw [← midA112_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((midA112CenteredInt.re i j)^2+(midA112CenteredInt.im i j)^2)) ≤
        midA112RadiusInt^2 := by
    simpa only [midA112CenteredSquareInt] using le_of_lt midA112_centered_square_lt
  have h := integer_operator_norm_bound midA112CenteredInt midA112RadiusInt
    (by norm_num [midA112RadiusInt,scale]) square
  convert h using 1
  norm_num [midA112RadiusInt,scale]

theorem midA112_qnet_centered_norm :
    ‖sourceOrdinaryQNet (1 : Basis) (12 : Basis) (by decide) -
      (12029/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3872/10^9 : ℝ) := by
  have source := source_ordinary_net_error (1 : Basis) (12 : Basis) (by decide)
  rw [midA112_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (1 : Basis) (12 : Basis) (by decide))
    (value midA112NetInt)
    ((12029/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (1 : Basis) (12 : Basis) (by decide) - value midA112NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse midA112_centered_norm).trans (by norm_num))

theorem midA112_qnet_floor :
    (8157/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (1 : Basis) (12 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (1 : Basis) (12 : Basis) (by decide))
    (ordinary_qnet_hermitian (1 : Basis) (12 : Basis) (by decide))
    (12029/10^9) (3872/10^9) midA112_qnet_centered_norm
  have compare : (8157/10^9 : ℝ) ≤ 12029/10^9-3872/10^9 := by norm_num
  have smaller : (8157/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (12029/10^9-3872/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
