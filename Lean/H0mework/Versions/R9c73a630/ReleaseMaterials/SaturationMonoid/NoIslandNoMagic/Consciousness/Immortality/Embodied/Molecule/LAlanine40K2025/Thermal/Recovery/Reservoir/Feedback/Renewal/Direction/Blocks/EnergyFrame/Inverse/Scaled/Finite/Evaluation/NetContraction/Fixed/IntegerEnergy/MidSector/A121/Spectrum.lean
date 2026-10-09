import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidSector.A121.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def midA121NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable midA121NetTable pairFin pairFin
def midA121CenterInt : Int := 11789*scale/10^9
def midA121RadiusInt : Int := 3875*scale/10^9
def midA121CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => midA121NetInt.re i j - (if i=j then midA121CenterInt else 0), midA121NetInt.im⟩
def midA121CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((midA121CenteredInt.re i j)^2+(midA121CenteredInt.im i j)^2)

theorem midA121_source_net_matrix :
    sourceOrdinaryNetInt (1 : Basis) (21 : Basis) (by decide) = midA121NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (1 : Basis) (21 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = midA121NetInt := by rw [midA121_source_net_literal]; rfl

theorem midA121_centered_square_lt :
    midA121CenteredSquareInt < midA121RadiusInt^2 := by decide +kernel

theorem midA121_centered_value :
    value midA121CenteredInt = value midA121NetInt -
      (11789/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [midA121CenteredInt,midA121CenterInt,value,raw,scale]
    ring
  · simp [midA121CenteredInt,midA121CenterInt,value,raw,scale,h]

theorem midA121_centered_norm :
    ‖value midA121NetInt -
      (11789/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3875/10^9 : ℝ) := by
  rw [← midA121_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((midA121CenteredInt.re i j)^2+(midA121CenteredInt.im i j)^2)) ≤
        midA121RadiusInt^2 := by
    simpa only [midA121CenteredSquareInt] using le_of_lt midA121_centered_square_lt
  have h := integer_operator_norm_bound midA121CenteredInt midA121RadiusInt
    (by norm_num [midA121RadiusInt,scale]) square
  convert h using 1
  norm_num [midA121RadiusInt,scale]

theorem midA121_qnet_centered_norm :
    ‖sourceOrdinaryQNet (1 : Basis) (21 : Basis) (by decide) -
      (11789/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3881/10^9 : ℝ) := by
  have source := source_ordinary_net_error (1 : Basis) (21 : Basis) (by decide)
  rw [midA121_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (1 : Basis) (21 : Basis) (by decide))
    (value midA121NetInt)
    ((11789/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (1 : Basis) (21 : Basis) (by decide) - value midA121NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse midA121_centered_norm).trans (by norm_num))

theorem midA121_qnet_floor :
    (7908/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (1 : Basis) (21 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (1 : Basis) (21 : Basis) (by decide))
    (ordinary_qnet_hermitian (1 : Basis) (21 : Basis) (by decide))
    (11789/10^9) (3881/10^9) midA121_qnet_centered_norm
  have compare : (7908/10^9 : ℝ) ≤ 11789/10^9-3881/10^9 := by norm_num
  have smaller : (7908/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (11789/10^9-3881/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
