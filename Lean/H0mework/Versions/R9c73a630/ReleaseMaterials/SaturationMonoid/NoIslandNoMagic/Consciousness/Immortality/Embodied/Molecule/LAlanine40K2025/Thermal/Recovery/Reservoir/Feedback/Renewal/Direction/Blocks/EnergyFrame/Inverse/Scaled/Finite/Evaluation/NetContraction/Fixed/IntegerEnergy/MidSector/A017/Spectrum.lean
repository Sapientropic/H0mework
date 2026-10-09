import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidSector.A017.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def midA017NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable midA017NetTable pairFin pairFin
def midA017CenterInt : Int := 11913*scale/10^9
def midA017RadiusInt : Int := 3871*scale/10^9
def midA017CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => midA017NetInt.re i j - (if i=j then midA017CenterInt else 0), midA017NetInt.im⟩
def midA017CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((midA017CenteredInt.re i j)^2+(midA017CenteredInt.im i j)^2)

theorem midA017_source_net_matrix :
    sourceOrdinaryNetInt (0 : Basis) (17 : Basis) (by decide) = midA017NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (0 : Basis) (17 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = midA017NetInt := by rw [midA017_source_net_literal]; rfl

theorem midA017_centered_square_lt :
    midA017CenteredSquareInt < midA017RadiusInt^2 := by decide +kernel

theorem midA017_centered_value :
    value midA017CenteredInt = value midA017NetInt -
      (11913/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [midA017CenteredInt,midA017CenterInt,value,raw,scale]
    ring
  · simp [midA017CenteredInt,midA017CenterInt,value,raw,scale,h]

theorem midA017_centered_norm :
    ‖value midA017NetInt -
      (11913/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3871/10^9 : ℝ) := by
  rw [← midA017_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((midA017CenteredInt.re i j)^2+(midA017CenteredInt.im i j)^2)) ≤
        midA017RadiusInt^2 := by
    simpa only [midA017CenteredSquareInt] using le_of_lt midA017_centered_square_lt
  have h := integer_operator_norm_bound midA017CenteredInt midA017RadiusInt
    (by norm_num [midA017RadiusInt,scale]) square
  convert h using 1
  norm_num [midA017RadiusInt,scale]

theorem midA017_qnet_centered_norm :
    ‖sourceOrdinaryQNet (0 : Basis) (17 : Basis) (by decide) -
      (11913/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3877/10^9 : ℝ) := by
  have source := source_ordinary_net_error (0 : Basis) (17 : Basis) (by decide)
  rw [midA017_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (0 : Basis) (17 : Basis) (by decide))
    (value midA017NetInt)
    ((11913/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (0 : Basis) (17 : Basis) (by decide) - value midA017NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse midA017_centered_norm).trans (by norm_num))

theorem midA017_qnet_floor :
    (8036/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (0 : Basis) (17 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (0 : Basis) (17 : Basis) (by decide))
    (ordinary_qnet_hermitian (0 : Basis) (17 : Basis) (by decide))
    (11913/10^9) (3877/10^9) midA017_qnet_centered_norm
  have compare : (8036/10^9 : ℝ) ≤ 11913/10^9-3877/10^9 := by norm_num
  have smaller : (8036/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (11913/10^9-3877/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
