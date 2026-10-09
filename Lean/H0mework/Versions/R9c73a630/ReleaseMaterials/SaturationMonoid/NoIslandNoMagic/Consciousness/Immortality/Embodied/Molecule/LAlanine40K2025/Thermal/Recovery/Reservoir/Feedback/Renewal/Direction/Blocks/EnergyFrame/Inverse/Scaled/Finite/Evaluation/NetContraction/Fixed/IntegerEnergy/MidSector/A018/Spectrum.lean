import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidSector.A018.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def midA018NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable midA018NetTable pairFin pairFin
def midA018CenterInt : Int := 11886*scale/10^9
def midA018RadiusInt : Int := 3872*scale/10^9
def midA018CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => midA018NetInt.re i j - (if i=j then midA018CenterInt else 0), midA018NetInt.im⟩
def midA018CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((midA018CenteredInt.re i j)^2+(midA018CenteredInt.im i j)^2)

theorem midA018_source_net_matrix :
    sourceOrdinaryNetInt (0 : Basis) (18 : Basis) (by decide) = midA018NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (0 : Basis) (18 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = midA018NetInt := by rw [midA018_source_net_literal]; rfl

theorem midA018_centered_square_lt :
    midA018CenteredSquareInt < midA018RadiusInt^2 := by decide +kernel

theorem midA018_centered_value :
    value midA018CenteredInt = value midA018NetInt -
      (11886/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [midA018CenteredInt,midA018CenterInt,value,raw,scale]
    ring
  · simp [midA018CenteredInt,midA018CenterInt,value,raw,scale,h]

theorem midA018_centered_norm :
    ‖value midA018NetInt -
      (11886/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3872/10^9 : ℝ) := by
  rw [← midA018_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((midA018CenteredInt.re i j)^2+(midA018CenteredInt.im i j)^2)) ≤
        midA018RadiusInt^2 := by
    simpa only [midA018CenteredSquareInt] using le_of_lt midA018_centered_square_lt
  have h := integer_operator_norm_bound midA018CenteredInt midA018RadiusInt
    (by norm_num [midA018RadiusInt,scale]) square
  convert h using 1
  norm_num [midA018RadiusInt,scale]

theorem midA018_qnet_centered_norm :
    ‖sourceOrdinaryQNet (0 : Basis) (18 : Basis) (by decide) -
      (11886/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3878/10^9 : ℝ) := by
  have source := source_ordinary_net_error (0 : Basis) (18 : Basis) (by decide)
  rw [midA018_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (0 : Basis) (18 : Basis) (by decide))
    (value midA018NetInt)
    ((11886/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (0 : Basis) (18 : Basis) (by decide) - value midA018NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse midA018_centered_norm).trans (by norm_num))

theorem midA018_qnet_floor :
    (8008/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (0 : Basis) (18 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (0 : Basis) (18 : Basis) (by decide))
    (ordinary_qnet_hermitian (0 : Basis) (18 : Basis) (by decide))
    (11886/10^9) (3878/10^9) midA018_qnet_centered_norm
  have compare : (8008/10^9 : ℝ) ≤ 11886/10^9-3878/10^9 := by norm_num
  have smaller : (8008/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (11886/10^9-3878/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
