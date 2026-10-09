import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidSector.A014.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def midA014NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable midA014NetTable pairFin pairFin
def midA014CenterInt : Int := 11957*scale/10^9
def midA014RadiusInt : Int := 3869*scale/10^9
def midA014CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => midA014NetInt.re i j - (if i=j then midA014CenterInt else 0), midA014NetInt.im⟩
def midA014CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((midA014CenteredInt.re i j)^2+(midA014CenteredInt.im i j)^2)

theorem midA014_source_net_matrix :
    sourceOrdinaryNetInt (0 : Basis) (14 : Basis) (by decide) = midA014NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (0 : Basis) (14 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = midA014NetInt := by rw [midA014_source_net_literal]; rfl

theorem midA014_centered_square_lt :
    midA014CenteredSquareInt < midA014RadiusInt^2 := by decide +kernel

theorem midA014_centered_value :
    value midA014CenteredInt = value midA014NetInt -
      (11957/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [midA014CenteredInt,midA014CenterInt,value,raw,scale]
    ring
  · simp [midA014CenteredInt,midA014CenterInt,value,raw,scale,h]

theorem midA014_centered_norm :
    ‖value midA014NetInt -
      (11957/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3869/10^9 : ℝ) := by
  rw [← midA014_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((midA014CenteredInt.re i j)^2+(midA014CenteredInt.im i j)^2)) ≤
        midA014RadiusInt^2 := by
    simpa only [midA014CenteredSquareInt] using le_of_lt midA014_centered_square_lt
  have h := integer_operator_norm_bound midA014CenteredInt midA014RadiusInt
    (by norm_num [midA014RadiusInt,scale]) square
  convert h using 1
  norm_num [midA014RadiusInt,scale]

theorem midA014_qnet_centered_norm :
    ‖sourceOrdinaryQNet (0 : Basis) (14 : Basis) (by decide) -
      (11957/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3875/10^9 : ℝ) := by
  have source := source_ordinary_net_error (0 : Basis) (14 : Basis) (by decide)
  rw [midA014_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (0 : Basis) (14 : Basis) (by decide))
    (value midA014NetInt)
    ((11957/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (0 : Basis) (14 : Basis) (by decide) - value midA014NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse midA014_centered_norm).trans (by norm_num))

theorem midA014_qnet_floor :
    (8082/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (0 : Basis) (14 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (0 : Basis) (14 : Basis) (by decide))
    (ordinary_qnet_hermitian (0 : Basis) (14 : Basis) (by decide))
    (11957/10^9) (3875/10^9) midA014_qnet_centered_norm
  have compare : (8082/10^9 : ℝ) ≤ 11957/10^9-3875/10^9 := by norm_num
  have smaller : (8082/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (11957/10^9-3875/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
