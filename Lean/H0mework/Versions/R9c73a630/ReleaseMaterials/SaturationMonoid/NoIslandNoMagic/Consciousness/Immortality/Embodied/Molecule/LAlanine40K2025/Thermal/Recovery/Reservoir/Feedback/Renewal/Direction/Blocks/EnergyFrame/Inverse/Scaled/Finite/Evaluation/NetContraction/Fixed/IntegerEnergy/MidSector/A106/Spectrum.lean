import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidSector.A106.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def midA106NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable midA106NetTable pairFin pairFin
def midA106CenterInt : Int := 12242*scale/10^9
def midA106RadiusInt : Int := 3858*scale/10^9
def midA106CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => midA106NetInt.re i j - (if i=j then midA106CenterInt else 0), midA106NetInt.im⟩
def midA106CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((midA106CenteredInt.re i j)^2+(midA106CenteredInt.im i j)^2)

theorem midA106_source_net_matrix :
    sourceOrdinaryNetInt (1 : Basis) (6 : Basis) (by decide) = midA106NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (1 : Basis) (6 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = midA106NetInt := by rw [midA106_source_net_literal]; rfl

theorem midA106_centered_square_lt :
    midA106CenteredSquareInt < midA106RadiusInt^2 := by decide +kernel

theorem midA106_centered_value :
    value midA106CenteredInt = value midA106NetInt -
      (12242/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [midA106CenteredInt,midA106CenterInt,value,raw,scale]
    ring
  · simp [midA106CenteredInt,midA106CenterInt,value,raw,scale,h]

theorem midA106_centered_norm :
    ‖value midA106NetInt -
      (12242/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3858/10^9 : ℝ) := by
  rw [← midA106_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((midA106CenteredInt.re i j)^2+(midA106CenteredInt.im i j)^2)) ≤
        midA106RadiusInt^2 := by
    simpa only [midA106CenteredSquareInt] using le_of_lt midA106_centered_square_lt
  have h := integer_operator_norm_bound midA106CenteredInt midA106RadiusInt
    (by norm_num [midA106RadiusInt,scale]) square
  convert h using 1
  norm_num [midA106RadiusInt,scale]

theorem midA106_qnet_centered_norm :
    ‖sourceOrdinaryQNet (1 : Basis) (6 : Basis) (by decide) -
      (12242/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3864/10^9 : ℝ) := by
  have source := source_ordinary_net_error (1 : Basis) (6 : Basis) (by decide)
  rw [midA106_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (1 : Basis) (6 : Basis) (by decide))
    (value midA106NetInt)
    ((12242/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (1 : Basis) (6 : Basis) (by decide) - value midA106NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse midA106_centered_norm).trans (by norm_num))

theorem midA106_qnet_floor :
    (8378/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (1 : Basis) (6 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (1 : Basis) (6 : Basis) (by decide))
    (ordinary_qnet_hermitian (1 : Basis) (6 : Basis) (by decide))
    (12242/10^9) (3864/10^9) midA106_qnet_centered_norm
  have compare : (8378/10^9 : ℝ) ≤ 12242/10^9-3864/10^9 := by norm_num
  have smaller : (8378/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (12242/10^9-3864/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
