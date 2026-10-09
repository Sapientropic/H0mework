import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidSector.A114.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def midA114NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable midA114NetTable pairFin pairFin
def midA114CenterInt : Int := 11947*scale/10^9
def midA114RadiusInt : Int := 3869*scale/10^9
def midA114CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => midA114NetInt.re i j - (if i=j then midA114CenterInt else 0), midA114NetInt.im⟩
def midA114CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((midA114CenteredInt.re i j)^2+(midA114CenteredInt.im i j)^2)

theorem midA114_source_net_matrix :
    sourceOrdinaryNetInt (1 : Basis) (14 : Basis) (by decide) = midA114NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (1 : Basis) (14 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = midA114NetInt := by rw [midA114_source_net_literal]; rfl

theorem midA114_centered_square_lt :
    midA114CenteredSquareInt < midA114RadiusInt^2 := by decide +kernel

theorem midA114_centered_value :
    value midA114CenteredInt = value midA114NetInt -
      (11947/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [midA114CenteredInt,midA114CenterInt,value,raw,scale]
    ring
  · simp [midA114CenteredInt,midA114CenterInt,value,raw,scale,h]

theorem midA114_centered_norm :
    ‖value midA114NetInt -
      (11947/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3869/10^9 : ℝ) := by
  rw [← midA114_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((midA114CenteredInt.re i j)^2+(midA114CenteredInt.im i j)^2)) ≤
        midA114RadiusInt^2 := by
    simpa only [midA114CenteredSquareInt] using le_of_lt midA114_centered_square_lt
  have h := integer_operator_norm_bound midA114CenteredInt midA114RadiusInt
    (by norm_num [midA114RadiusInt,scale]) square
  convert h using 1
  norm_num [midA114RadiusInt,scale]

theorem midA114_qnet_centered_norm :
    ‖sourceOrdinaryQNet (1 : Basis) (14 : Basis) (by decide) -
      (11947/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3875/10^9 : ℝ) := by
  have source := source_ordinary_net_error (1 : Basis) (14 : Basis) (by decide)
  rw [midA114_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (1 : Basis) (14 : Basis) (by decide))
    (value midA114NetInt)
    ((11947/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (1 : Basis) (14 : Basis) (by decide) - value midA114NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse midA114_centered_norm).trans (by norm_num))

theorem midA114_qnet_floor :
    (8072/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (1 : Basis) (14 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (1 : Basis) (14 : Basis) (by decide))
    (ordinary_qnet_hermitian (1 : Basis) (14 : Basis) (by decide))
    (11947/10^9) (3875/10^9) midA114_qnet_centered_norm
  have compare : (8072/10^9 : ℝ) ≤ 11947/10^9-3875/10^9 := by norm_num
  have smaller : (8072/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (11947/10^9-3875/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
