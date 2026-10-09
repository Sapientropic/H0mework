import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidSector.A122.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def midA122NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable midA122NetTable pairFin pairFin
def midA122CenterInt : Int := 11787*scale/10^9
def midA122RadiusInt : Int := 3875*scale/10^9
def midA122CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => midA122NetInt.re i j - (if i=j then midA122CenterInt else 0), midA122NetInt.im⟩
def midA122CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((midA122CenteredInt.re i j)^2+(midA122CenteredInt.im i j)^2)

theorem midA122_source_net_matrix :
    sourceOrdinaryNetInt (1 : Basis) (22 : Basis) (by decide) = midA122NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (1 : Basis) (22 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = midA122NetInt := by rw [midA122_source_net_literal]; rfl

theorem midA122_centered_square_lt :
    midA122CenteredSquareInt < midA122RadiusInt^2 := by decide +kernel

theorem midA122_centered_value :
    value midA122CenteredInt = value midA122NetInt -
      (11787/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [midA122CenteredInt,midA122CenterInt,value,raw,scale]
    ring
  · simp [midA122CenteredInt,midA122CenterInt,value,raw,scale,h]

theorem midA122_centered_norm :
    ‖value midA122NetInt -
      (11787/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3875/10^9 : ℝ) := by
  rw [← midA122_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((midA122CenteredInt.re i j)^2+(midA122CenteredInt.im i j)^2)) ≤
        midA122RadiusInt^2 := by
    simpa only [midA122CenteredSquareInt] using le_of_lt midA122_centered_square_lt
  have h := integer_operator_norm_bound midA122CenteredInt midA122RadiusInt
    (by norm_num [midA122RadiusInt,scale]) square
  convert h using 1
  norm_num [midA122RadiusInt,scale]

theorem midA122_qnet_centered_norm :
    ‖sourceOrdinaryQNet (1 : Basis) (22 : Basis) (by decide) -
      (11787/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3881/10^9 : ℝ) := by
  have source := source_ordinary_net_error (1 : Basis) (22 : Basis) (by decide)
  rw [midA122_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (1 : Basis) (22 : Basis) (by decide))
    (value midA122NetInt)
    ((11787/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (1 : Basis) (22 : Basis) (by decide) - value midA122NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse midA122_centered_norm).trans (by norm_num))

theorem midA122_qnet_floor :
    (7906/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (1 : Basis) (22 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (1 : Basis) (22 : Basis) (by decide))
    (ordinary_qnet_hermitian (1 : Basis) (22 : Basis) (by decide))
    (11787/10^9) (3881/10^9) midA122_qnet_centered_norm
  have compare : (7906/10^9 : ℝ) ≤ 11787/10^9-3881/10^9 := by norm_num
  have smaller : (7906/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (11787/10^9-3881/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
