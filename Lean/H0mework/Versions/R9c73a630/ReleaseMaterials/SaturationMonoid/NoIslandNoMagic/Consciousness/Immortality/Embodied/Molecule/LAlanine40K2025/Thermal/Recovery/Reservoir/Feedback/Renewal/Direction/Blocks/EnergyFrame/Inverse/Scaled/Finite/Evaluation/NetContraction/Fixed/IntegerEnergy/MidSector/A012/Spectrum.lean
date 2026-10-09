import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidSector.A012.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def midA012NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable midA012NetTable pairFin pairFin
def midA012CenterInt : Int := 12040*scale/10^9
def midA012RadiusInt : Int := 3866*scale/10^9
def midA012CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => midA012NetInt.re i j - (if i=j then midA012CenterInt else 0), midA012NetInt.im⟩
def midA012CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((midA012CenteredInt.re i j)^2+(midA012CenteredInt.im i j)^2)

theorem midA012_source_net_matrix :
    sourceOrdinaryNetInt (0 : Basis) (12 : Basis) (by decide) = midA012NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (0 : Basis) (12 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = midA012NetInt := by rw [midA012_source_net_literal]; rfl

theorem midA012_centered_square_lt :
    midA012CenteredSquareInt < midA012RadiusInt^2 := by decide +kernel

theorem midA012_centered_value :
    value midA012CenteredInt = value midA012NetInt -
      (12040/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [midA012CenteredInt,midA012CenterInt,value,raw,scale]
    ring
  · simp [midA012CenteredInt,midA012CenterInt,value,raw,scale,h]

theorem midA012_centered_norm :
    ‖value midA012NetInt -
      (12040/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3866/10^9 : ℝ) := by
  rw [← midA012_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((midA012CenteredInt.re i j)^2+(midA012CenteredInt.im i j)^2)) ≤
        midA012RadiusInt^2 := by
    simpa only [midA012CenteredSquareInt] using le_of_lt midA012_centered_square_lt
  have h := integer_operator_norm_bound midA012CenteredInt midA012RadiusInt
    (by norm_num [midA012RadiusInt,scale]) square
  convert h using 1
  norm_num [midA012RadiusInt,scale]

theorem midA012_qnet_centered_norm :
    ‖sourceOrdinaryQNet (0 : Basis) (12 : Basis) (by decide) -
      (12040/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3872/10^9 : ℝ) := by
  have source := source_ordinary_net_error (0 : Basis) (12 : Basis) (by decide)
  rw [midA012_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (0 : Basis) (12 : Basis) (by decide))
    (value midA012NetInt)
    ((12040/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (0 : Basis) (12 : Basis) (by decide) - value midA012NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse midA012_centered_norm).trans (by norm_num))

theorem midA012_qnet_floor :
    (8168/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (0 : Basis) (12 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (0 : Basis) (12 : Basis) (by decide))
    (ordinary_qnet_hermitian (0 : Basis) (12 : Basis) (by decide))
    (12040/10^9) (3872/10^9) midA012_qnet_centered_norm
  have compare : (8168/10^9 : ℝ) ≤ 12040/10^9-3872/10^9 := by norm_num
  have smaller : (8168/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (12040/10^9-3872/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
