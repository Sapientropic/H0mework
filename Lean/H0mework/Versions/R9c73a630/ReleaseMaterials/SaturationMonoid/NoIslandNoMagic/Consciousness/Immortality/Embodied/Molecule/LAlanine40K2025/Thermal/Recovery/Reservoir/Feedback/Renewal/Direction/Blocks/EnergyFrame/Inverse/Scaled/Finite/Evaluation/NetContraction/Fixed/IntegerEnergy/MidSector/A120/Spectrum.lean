import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidSector.A120.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def midA120NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable midA120NetTable pairFin pairFin
def midA120CenterInt : Int := 11853*scale/10^9
def midA120RadiusInt : Int := 3873*scale/10^9
def midA120CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => midA120NetInt.re i j - (if i=j then midA120CenterInt else 0), midA120NetInt.im⟩
def midA120CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((midA120CenteredInt.re i j)^2+(midA120CenteredInt.im i j)^2)

theorem midA120_source_net_matrix :
    sourceOrdinaryNetInt (1 : Basis) (20 : Basis) (by decide) = midA120NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (1 : Basis) (20 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = midA120NetInt := by rw [midA120_source_net_literal]; rfl

theorem midA120_centered_square_lt :
    midA120CenteredSquareInt < midA120RadiusInt^2 := by decide +kernel

theorem midA120_centered_value :
    value midA120CenteredInt = value midA120NetInt -
      (11853/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [midA120CenteredInt,midA120CenterInt,value,raw,scale]
    ring
  · simp [midA120CenteredInt,midA120CenterInt,value,raw,scale,h]

theorem midA120_centered_norm :
    ‖value midA120NetInt -
      (11853/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3873/10^9 : ℝ) := by
  rw [← midA120_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((midA120CenteredInt.re i j)^2+(midA120CenteredInt.im i j)^2)) ≤
        midA120RadiusInt^2 := by
    simpa only [midA120CenteredSquareInt] using le_of_lt midA120_centered_square_lt
  have h := integer_operator_norm_bound midA120CenteredInt midA120RadiusInt
    (by norm_num [midA120RadiusInt,scale]) square
  convert h using 1
  norm_num [midA120RadiusInt,scale]

theorem midA120_qnet_centered_norm :
    ‖sourceOrdinaryQNet (1 : Basis) (20 : Basis) (by decide) -
      (11853/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3879/10^9 : ℝ) := by
  have source := source_ordinary_net_error (1 : Basis) (20 : Basis) (by decide)
  rw [midA120_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (1 : Basis) (20 : Basis) (by decide))
    (value midA120NetInt)
    ((11853/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (1 : Basis) (20 : Basis) (by decide) - value midA120NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse midA120_centered_norm).trans (by norm_num))

theorem midA120_qnet_floor :
    (7974/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (1 : Basis) (20 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (1 : Basis) (20 : Basis) (by decide))
    (ordinary_qnet_hermitian (1 : Basis) (20 : Basis) (by decide))
    (11853/10^9) (3879/10^9) midA120_qnet_centered_norm
  have compare : (7974/10^9 : ℝ) ≤ 11853/10^9-3879/10^9 := by norm_num
  have smaller : (7974/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (11853/10^9-3879/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
