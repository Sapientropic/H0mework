import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidSector.A110.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def midA110NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable midA110NetTable pairFin pairFin
def midA110CenterInt : Int := 12046*scale/10^9
def midA110RadiusInt : Int := 3865*scale/10^9
def midA110CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => midA110NetInt.re i j - (if i=j then midA110CenterInt else 0), midA110NetInt.im⟩
def midA110CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((midA110CenteredInt.re i j)^2+(midA110CenteredInt.im i j)^2)

theorem midA110_source_net_matrix :
    sourceOrdinaryNetInt (1 : Basis) (10 : Basis) (by decide) = midA110NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (1 : Basis) (10 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = midA110NetInt := by rw [midA110_source_net_literal]; rfl

theorem midA110_centered_square_lt :
    midA110CenteredSquareInt < midA110RadiusInt^2 := by decide +kernel

theorem midA110_centered_value :
    value midA110CenteredInt = value midA110NetInt -
      (12046/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [midA110CenteredInt,midA110CenterInt,value,raw,scale]
    ring
  · simp [midA110CenteredInt,midA110CenterInt,value,raw,scale,h]

theorem midA110_centered_norm :
    ‖value midA110NetInt -
      (12046/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3865/10^9 : ℝ) := by
  rw [← midA110_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((midA110CenteredInt.re i j)^2+(midA110CenteredInt.im i j)^2)) ≤
        midA110RadiusInt^2 := by
    simpa only [midA110CenteredSquareInt] using le_of_lt midA110_centered_square_lt
  have h := integer_operator_norm_bound midA110CenteredInt midA110RadiusInt
    (by norm_num [midA110RadiusInt,scale]) square
  convert h using 1
  norm_num [midA110RadiusInt,scale]

theorem midA110_qnet_centered_norm :
    ‖sourceOrdinaryQNet (1 : Basis) (10 : Basis) (by decide) -
      (12046/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3871/10^9 : ℝ) := by
  have source := source_ordinary_net_error (1 : Basis) (10 : Basis) (by decide)
  rw [midA110_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (1 : Basis) (10 : Basis) (by decide))
    (value midA110NetInt)
    ((12046/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (1 : Basis) (10 : Basis) (by decide) - value midA110NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse midA110_centered_norm).trans (by norm_num))

theorem midA110_qnet_floor :
    (8175/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (1 : Basis) (10 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (1 : Basis) (10 : Basis) (by decide))
    (ordinary_qnet_hermitian (1 : Basis) (10 : Basis) (by decide))
    (12046/10^9) (3871/10^9) midA110_qnet_centered_norm
  have compare : (8175/10^9 : ℝ) ≤ 12046/10^9-3871/10^9 := by norm_num
  have smaller : (8175/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (12046/10^9-3871/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
