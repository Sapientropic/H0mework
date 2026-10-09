import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidSector.A115.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def midA115NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable midA115NetTable pairFin pairFin
def midA115CenterInt : Int := 11915*scale/10^9
def midA115RadiusInt : Int := 3870*scale/10^9
def midA115CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => midA115NetInt.re i j - (if i=j then midA115CenterInt else 0), midA115NetInt.im⟩
def midA115CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((midA115CenteredInt.re i j)^2+(midA115CenteredInt.im i j)^2)

theorem midA115_source_net_matrix :
    sourceOrdinaryNetInt (1 : Basis) (15 : Basis) (by decide) = midA115NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (1 : Basis) (15 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = midA115NetInt := by rw [midA115_source_net_literal]; rfl

theorem midA115_centered_square_lt :
    midA115CenteredSquareInt < midA115RadiusInt^2 := by decide +kernel

theorem midA115_centered_value :
    value midA115CenteredInt = value midA115NetInt -
      (11915/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [midA115CenteredInt,midA115CenterInt,value,raw,scale]
    ring
  · simp [midA115CenteredInt,midA115CenterInt,value,raw,scale,h]

theorem midA115_centered_norm :
    ‖value midA115NetInt -
      (11915/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3870/10^9 : ℝ) := by
  rw [← midA115_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((midA115CenteredInt.re i j)^2+(midA115CenteredInt.im i j)^2)) ≤
        midA115RadiusInt^2 := by
    simpa only [midA115CenteredSquareInt] using le_of_lt midA115_centered_square_lt
  have h := integer_operator_norm_bound midA115CenteredInt midA115RadiusInt
    (by norm_num [midA115RadiusInt,scale]) square
  convert h using 1
  norm_num [midA115RadiusInt,scale]

theorem midA115_qnet_centered_norm :
    ‖sourceOrdinaryQNet (1 : Basis) (15 : Basis) (by decide) -
      (11915/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3876/10^9 : ℝ) := by
  have source := source_ordinary_net_error (1 : Basis) (15 : Basis) (by decide)
  rw [midA115_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (1 : Basis) (15 : Basis) (by decide))
    (value midA115NetInt)
    ((11915/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (1 : Basis) (15 : Basis) (by decide) - value midA115NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse midA115_centered_norm).trans (by norm_num))

theorem midA115_qnet_floor :
    (8039/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (1 : Basis) (15 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (1 : Basis) (15 : Basis) (by decide))
    (ordinary_qnet_hermitian (1 : Basis) (15 : Basis) (by decide))
    (11915/10^9) (3876/10^9) midA115_qnet_centered_norm
  have compare : (8039/10^9 : ℝ) ≤ 11915/10^9-3876/10^9 := by norm_num
  have smaller : (8039/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (11915/10^9-3876/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
