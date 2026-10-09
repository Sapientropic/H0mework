import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.NearSector.A105.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def nearA105NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable nearA105NetTable pairFin pairFin
def nearA105CenterInt : Int := 17101*scale/10^9
def nearA105RadiusInt : Int := 3750*scale/10^9
def nearA105CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => nearA105NetInt.re i j - (if i=j then nearA105CenterInt else 0), nearA105NetInt.im⟩
def nearA105CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((nearA105CenteredInt.re i j)^2+(nearA105CenteredInt.im i j)^2)

theorem nearA105_source_net_matrix :
    sourceOrdinaryNetInt (1 : Basis) (5 : Basis) (by decide) = nearA105NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (1 : Basis) (5 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = nearA105NetInt := by rw [nearA105_source_net_literal]; rfl

theorem nearA105_centered_square_lt :
    nearA105CenteredSquareInt < nearA105RadiusInt^2 := by decide +kernel

theorem nearA105_centered_value :
    value nearA105CenteredInt = value nearA105NetInt -
      (17101/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [nearA105CenteredInt,nearA105CenterInt,value,raw,scale]
    ring
  · simp [nearA105CenteredInt,nearA105CenterInt,value,raw,scale,h]

theorem nearA105_centered_norm :
    ‖value nearA105NetInt -
      (17101/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3750/10^9 : ℝ) := by
  rw [← nearA105_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((nearA105CenteredInt.re i j)^2+(nearA105CenteredInt.im i j)^2)) ≤
        nearA105RadiusInt^2 := by
    simpa only [nearA105CenteredSquareInt] using le_of_lt nearA105_centered_square_lt
  have h := integer_operator_norm_bound nearA105CenteredInt nearA105RadiusInt
    (by norm_num [nearA105RadiusInt,scale]) square
  convert h using 1
  norm_num [nearA105RadiusInt,scale]

theorem nearA105_qnet_centered_norm :
    ‖sourceOrdinaryQNet (1 : Basis) (5 : Basis) (by decide) -
      (17101/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3756/10^9 : ℝ) := by
  have source := source_ordinary_net_error (1 : Basis) (5 : Basis) (by decide)
  rw [nearA105_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (1 : Basis) (5 : Basis) (by decide))
    (value nearA105NetInt)
    ((17101/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (1 : Basis) (5 : Basis) (by decide) - value nearA105NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse nearA105_centered_norm).trans (by norm_num))

theorem nearA105_qnet_floor :
    (13345/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (1 : Basis) (5 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (1 : Basis) (5 : Basis) (by decide))
    (ordinary_qnet_hermitian (1 : Basis) (5 : Basis) (by decide))
    (17101/10^9) (3756/10^9) nearA105_qnet_centered_norm
  have compare : (13345/10^9 : ℝ) ≤ 17101/10^9-3756/10^9 := by norm_num
  have smaller : (13345/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (17101/10^9-3756/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
