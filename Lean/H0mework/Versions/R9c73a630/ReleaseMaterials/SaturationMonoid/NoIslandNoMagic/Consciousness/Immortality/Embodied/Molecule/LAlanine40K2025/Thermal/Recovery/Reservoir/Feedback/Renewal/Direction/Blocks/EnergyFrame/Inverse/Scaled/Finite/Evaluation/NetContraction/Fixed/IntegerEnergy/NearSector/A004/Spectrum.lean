import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.NearSector.A004.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def nearA004NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable nearA004NetTable pairFin pairFin
def nearA004CenterInt : Int := 17145*scale/10^9
def nearA004RadiusInt : Int := 3750*scale/10^9
def nearA004CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => nearA004NetInt.re i j - (if i=j then nearA004CenterInt else 0), nearA004NetInt.im⟩
def nearA004CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((nearA004CenteredInt.re i j)^2+(nearA004CenteredInt.im i j)^2)

theorem nearA004_source_net_matrix :
    sourceOrdinaryNetInt (0 : Basis) (4 : Basis) (by decide) = nearA004NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (0 : Basis) (4 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = nearA004NetInt := by rw [nearA004_source_net_literal]; rfl

theorem nearA004_centered_square_lt :
    nearA004CenteredSquareInt < nearA004RadiusInt^2 := by decide +kernel

theorem nearA004_centered_value :
    value nearA004CenteredInt = value nearA004NetInt -
      (17145/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [nearA004CenteredInt,nearA004CenterInt,value,raw,scale]
    ring
  · simp [nearA004CenteredInt,nearA004CenterInt,value,raw,scale,h]

theorem nearA004_centered_norm :
    ‖value nearA004NetInt -
      (17145/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3750/10^9 : ℝ) := by
  rw [← nearA004_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((nearA004CenteredInt.re i j)^2+(nearA004CenteredInt.im i j)^2)) ≤
        nearA004RadiusInt^2 := by
    simpa only [nearA004CenteredSquareInt] using le_of_lt nearA004_centered_square_lt
  have h := integer_operator_norm_bound nearA004CenteredInt nearA004RadiusInt
    (by norm_num [nearA004RadiusInt,scale]) square
  convert h using 1
  norm_num [nearA004RadiusInt,scale]

theorem nearA004_qnet_centered_norm :
    ‖sourceOrdinaryQNet (0 : Basis) (4 : Basis) (by decide) -
      (17145/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3756/10^9 : ℝ) := by
  have source := source_ordinary_net_error (0 : Basis) (4 : Basis) (by decide)
  rw [nearA004_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (0 : Basis) (4 : Basis) (by decide))
    (value nearA004NetInt)
    ((17145/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (0 : Basis) (4 : Basis) (by decide) - value nearA004NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse nearA004_centered_norm).trans (by norm_num))

theorem nearA004_qnet_floor :
    (13389/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (0 : Basis) (4 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (0 : Basis) (4 : Basis) (by decide))
    (ordinary_qnet_hermitian (0 : Basis) (4 : Basis) (by decide))
    (17145/10^9) (3756/10^9) nearA004_qnet_centered_norm
  have compare : (13389/10^9 : ℝ) ≤ 17145/10^9-3756/10^9 := by norm_num
  have smaller : (13389/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (17145/10^9-3756/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
