import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidSector.A119.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def midA119NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable midA119NetTable pairFin pairFin
def midA119CenterInt : Int := 11857*scale/10^9
def midA119RadiusInt : Int := 3872*scale/10^9
def midA119CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => midA119NetInt.re i j - (if i=j then midA119CenterInt else 0), midA119NetInt.im⟩
def midA119CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((midA119CenteredInt.re i j)^2+(midA119CenteredInt.im i j)^2)

theorem midA119_source_net_matrix :
    sourceOrdinaryNetInt (1 : Basis) (19 : Basis) (by decide) = midA119NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (1 : Basis) (19 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = midA119NetInt := by rw [midA119_source_net_literal]; rfl

theorem midA119_centered_square_lt :
    midA119CenteredSquareInt < midA119RadiusInt^2 := by decide +kernel

theorem midA119_centered_value :
    value midA119CenteredInt = value midA119NetInt -
      (11857/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [midA119CenteredInt,midA119CenterInt,value,raw,scale]
    ring
  · simp [midA119CenteredInt,midA119CenterInt,value,raw,scale,h]

theorem midA119_centered_norm :
    ‖value midA119NetInt -
      (11857/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3872/10^9 : ℝ) := by
  rw [← midA119_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((midA119CenteredInt.re i j)^2+(midA119CenteredInt.im i j)^2)) ≤
        midA119RadiusInt^2 := by
    simpa only [midA119CenteredSquareInt] using le_of_lt midA119_centered_square_lt
  have h := integer_operator_norm_bound midA119CenteredInt midA119RadiusInt
    (by norm_num [midA119RadiusInt,scale]) square
  convert h using 1
  norm_num [midA119RadiusInt,scale]

theorem midA119_qnet_centered_norm :
    ‖sourceOrdinaryQNet (1 : Basis) (19 : Basis) (by decide) -
      (11857/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3878/10^9 : ℝ) := by
  have source := source_ordinary_net_error (1 : Basis) (19 : Basis) (by decide)
  rw [midA119_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (1 : Basis) (19 : Basis) (by decide))
    (value midA119NetInt)
    ((11857/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (1 : Basis) (19 : Basis) (by decide) - value midA119NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse midA119_centered_norm).trans (by norm_num))

theorem midA119_qnet_floor :
    (7979/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (1 : Basis) (19 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (1 : Basis) (19 : Basis) (by decide))
    (ordinary_qnet_hermitian (1 : Basis) (19 : Basis) (by decide))
    (11857/10^9) (3878/10^9) midA119_qnet_centered_norm
  have compare : (7979/10^9 : ℝ) ≤ 11857/10^9-3878/10^9 := by norm_num
  have smaller : (7979/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (11857/10^9-3878/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
