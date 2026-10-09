import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.SpectralNorm
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ThirdStage.NetSource

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def thirdNetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) := fromTable netTable pairFin pairFin
def thirdCenterInt : Int := 18*scale/10^6
def thirdRadiusInt : Int := 412*scale/10^8
def thirdCenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((thirdNetInt.re i j - (if i=j then thirdCenterInt else 0))^2 +
      (thirdNetInt.im i j)^2)

def thirdCenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => thirdNetInt.re i j - (if i=j then thirdCenterInt else 0),
   thirdNetInt.im⟩

theorem third_centered_value :
    value thirdCenteredInt = value thirdNetInt -
      (18/10^6 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [thirdCenteredInt,thirdCenterInt,value,raw,scale]
    ring
  · simp [thirdCenteredInt,thirdCenterInt,value,raw,scale,h]

theorem third_centered_square_lt :
    thirdCenteredSquareInt < thirdRadiusInt^2 := by decide +kernel

theorem third_centered_norm :
    ‖value thirdNetInt -
      (18/10^6 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (412/10^8 : ℝ) := by
  rw [← third_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((thirdCenteredInt.re i j)^2+(thirdCenteredInt.im i j)^2)) ≤
        thirdRadiusInt^2 := by
    simpa only [thirdCenteredInt,thirdCenteredSquareInt] using
      (le_of_lt third_centered_square_lt)
  have h := integer_operator_norm_bound thirdCenteredInt thirdRadiusInt
    (by norm_num [thirdRadiusInt,scale]) square
  convert h using 1
  norm_num [thirdRadiusInt,scale]

theorem third_qnet_centered_norm :
    ‖sourceOrdinaryQNet (0 : Basis) (3 : Basis) (by decide) -
      (18/10^6 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (4126/10^9 : ℝ) := by
  have source := source_ordinary_net_error (0 : Basis) (3 : Basis) (by decide)
  rw [third_source_net_matrix] at source
  change ‖value thirdNetInt - sourceOrdinaryQNet (0 : Basis) (3 : Basis) (by decide)‖ ≤ _ at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (0 : Basis) (3 : Basis) (by decide))
    (value thirdNetInt)
    ((18/10^6 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have sourceReverse :
      ‖sourceOrdinaryQNet (0 : Basis) (3 : Basis) (by decide) - value thirdNetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add sourceReverse third_centered_norm).trans (by norm_num))

theorem third_qnet_strict_floor :
    (138/10^7 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (0 : Basis) (3 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (0 : Basis) (3 : Basis) (by decide))
    (ordinary_qnet_hermitian (0 : Basis) (3 : Basis) (by decide))
    (18/10^6) (4126/10^9) third_qnet_centered_norm
  have compare : (138/10^7 : ℝ) ≤ 18/10^6-4126/10^9 := by norm_num
  have smaller : (138/10^7 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (18/10^6-4126/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
