import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.NearSector.A104.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def nearA104NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable nearA104NetTable pairFin pairFin
def nearA104CenterInt : Int := 17134*scale/10^9
def nearA104RadiusInt : Int := 3750*scale/10^9
def nearA104CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => nearA104NetInt.re i j - (if i=j then nearA104CenterInt else 0), nearA104NetInt.im⟩
def nearA104CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((nearA104CenteredInt.re i j)^2+(nearA104CenteredInt.im i j)^2)

theorem nearA104_source_net_matrix :
    sourceOrdinaryNetInt (1 : Basis) (4 : Basis) (by decide) = nearA104NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (1 : Basis) (4 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = nearA104NetInt := by rw [nearA104_source_net_literal]; rfl

theorem nearA104_centered_square_lt :
    nearA104CenteredSquareInt < nearA104RadiusInt^2 := by decide +kernel

theorem nearA104_centered_value :
    value nearA104CenteredInt = value nearA104NetInt -
      (17134/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [nearA104CenteredInt,nearA104CenterInt,value,raw,scale]
    ring
  · simp [nearA104CenteredInt,nearA104CenterInt,value,raw,scale,h]

theorem nearA104_centered_norm :
    ‖value nearA104NetInt -
      (17134/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3750/10^9 : ℝ) := by
  rw [← nearA104_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((nearA104CenteredInt.re i j)^2+(nearA104CenteredInt.im i j)^2)) ≤
        nearA104RadiusInt^2 := by
    simpa only [nearA104CenteredSquareInt] using le_of_lt nearA104_centered_square_lt
  have h := integer_operator_norm_bound nearA104CenteredInt nearA104RadiusInt
    (by norm_num [nearA104RadiusInt,scale]) square
  convert h using 1
  norm_num [nearA104RadiusInt,scale]

theorem nearA104_qnet_centered_norm :
    ‖sourceOrdinaryQNet (1 : Basis) (4 : Basis) (by decide) -
      (17134/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3756/10^9 : ℝ) := by
  have source := source_ordinary_net_error (1 : Basis) (4 : Basis) (by decide)
  rw [nearA104_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (1 : Basis) (4 : Basis) (by decide))
    (value nearA104NetInt)
    ((17134/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (1 : Basis) (4 : Basis) (by decide) - value nearA104NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse nearA104_centered_norm).trans (by norm_num))

theorem nearA104_qnet_floor :
    (13378/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (1 : Basis) (4 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (1 : Basis) (4 : Basis) (by decide))
    (ordinary_qnet_hermitian (1 : Basis) (4 : Basis) (by decide))
    (17134/10^9) (3756/10^9) nearA104_qnet_centered_norm
  have compare : (13378/10^9 : ℝ) ≤ 17134/10^9-3756/10^9 := by norm_num
  have smaller : (13378/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (17134/10^9-3756/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
