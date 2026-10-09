import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidSector.A021.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def midA021NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable midA021NetTable pairFin pairFin
def midA021CenterInt : Int := 11800*scale/10^9
def midA021RadiusInt : Int := 3875*scale/10^9
def midA021CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => midA021NetInt.re i j - (if i=j then midA021CenterInt else 0), midA021NetInt.im⟩
def midA021CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((midA021CenteredInt.re i j)^2+(midA021CenteredInt.im i j)^2)

theorem midA021_source_net_matrix :
    sourceOrdinaryNetInt (0 : Basis) (21 : Basis) (by decide) = midA021NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (0 : Basis) (21 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = midA021NetInt := by rw [midA021_source_net_literal]; rfl

theorem midA021_centered_square_lt :
    midA021CenteredSquareInt < midA021RadiusInt^2 := by decide +kernel

theorem midA021_centered_value :
    value midA021CenteredInt = value midA021NetInt -
      (11800/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [midA021CenteredInt,midA021CenterInt,value,raw,scale]
    ring
  · simp [midA021CenteredInt,midA021CenterInt,value,raw,scale,h]

theorem midA021_centered_norm :
    ‖value midA021NetInt -
      (11800/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3875/10^9 : ℝ) := by
  rw [← midA021_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((midA021CenteredInt.re i j)^2+(midA021CenteredInt.im i j)^2)) ≤
        midA021RadiusInt^2 := by
    simpa only [midA021CenteredSquareInt] using le_of_lt midA021_centered_square_lt
  have h := integer_operator_norm_bound midA021CenteredInt midA021RadiusInt
    (by norm_num [midA021RadiusInt,scale]) square
  convert h using 1
  norm_num [midA021RadiusInt,scale]

theorem midA021_qnet_centered_norm :
    ‖sourceOrdinaryQNet (0 : Basis) (21 : Basis) (by decide) -
      (11800/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3881/10^9 : ℝ) := by
  have source := source_ordinary_net_error (0 : Basis) (21 : Basis) (by decide)
  rw [midA021_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (0 : Basis) (21 : Basis) (by decide))
    (value midA021NetInt)
    ((11800/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (0 : Basis) (21 : Basis) (by decide) - value midA021NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse midA021_centered_norm).trans (by norm_num))

theorem midA021_qnet_floor :
    (7919/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (0 : Basis) (21 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (0 : Basis) (21 : Basis) (by decide))
    (ordinary_qnet_hermitian (0 : Basis) (21 : Basis) (by decide))
    (11800/10^9) (3881/10^9) midA021_qnet_centered_norm
  have compare : (7919/10^9 : ℝ) ≤ 11800/10^9-3881/10^9 := by norm_num
  have smaller : (7919/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (11800/10^9-3881/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
