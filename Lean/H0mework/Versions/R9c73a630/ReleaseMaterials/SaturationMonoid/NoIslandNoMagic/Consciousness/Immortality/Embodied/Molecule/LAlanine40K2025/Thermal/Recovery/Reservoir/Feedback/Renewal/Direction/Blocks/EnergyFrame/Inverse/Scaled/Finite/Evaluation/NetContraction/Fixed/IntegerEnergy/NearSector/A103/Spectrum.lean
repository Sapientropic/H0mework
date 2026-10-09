import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.NearSector.A103.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def nearA103NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable nearA103NetTable pairFin pairFin
def nearA103CenterInt : Int := 17141*scale/10^9
def nearA103RadiusInt : Int := 3750*scale/10^9
def nearA103CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => nearA103NetInt.re i j - (if i=j then nearA103CenterInt else 0), nearA103NetInt.im⟩
def nearA103CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((nearA103CenteredInt.re i j)^2+(nearA103CenteredInt.im i j)^2)

theorem nearA103_source_net_matrix :
    sourceOrdinaryNetInt (1 : Basis) (3 : Basis) (by decide) = nearA103NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (1 : Basis) (3 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = nearA103NetInt := by rw [nearA103_source_net_literal]; rfl

theorem nearA103_centered_square_lt :
    nearA103CenteredSquareInt < nearA103RadiusInt^2 := by decide +kernel

theorem nearA103_centered_value :
    value nearA103CenteredInt = value nearA103NetInt -
      (17141/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [nearA103CenteredInt,nearA103CenterInt,value,raw,scale]
    ring
  · simp [nearA103CenteredInt,nearA103CenterInt,value,raw,scale,h]

theorem nearA103_centered_norm :
    ‖value nearA103NetInt -
      (17141/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3750/10^9 : ℝ) := by
  rw [← nearA103_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((nearA103CenteredInt.re i j)^2+(nearA103CenteredInt.im i j)^2)) ≤
        nearA103RadiusInt^2 := by
    simpa only [nearA103CenteredSquareInt] using le_of_lt nearA103_centered_square_lt
  have h := integer_operator_norm_bound nearA103CenteredInt nearA103RadiusInt
    (by norm_num [nearA103RadiusInt,scale]) square
  convert h using 1
  norm_num [nearA103RadiusInt,scale]

theorem nearA103_qnet_centered_norm :
    ‖sourceOrdinaryQNet (1 : Basis) (3 : Basis) (by decide) -
      (17141/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3756/10^9 : ℝ) := by
  have source := source_ordinary_net_error (1 : Basis) (3 : Basis) (by decide)
  rw [nearA103_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (1 : Basis) (3 : Basis) (by decide))
    (value nearA103NetInt)
    ((17141/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (1 : Basis) (3 : Basis) (by decide) - value nearA103NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse nearA103_centered_norm).trans (by norm_num))

theorem nearA103_qnet_floor :
    (13385/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (1 : Basis) (3 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (1 : Basis) (3 : Basis) (by decide))
    (ordinary_qnet_hermitian (1 : Basis) (3 : Basis) (by decide))
    (17141/10^9) (3756/10^9) nearA103_qnet_centered_norm
  have compare : (13385/10^9 : ℝ) ≤ 17141/10^9-3756/10^9 := by norm_num
  have smaller : (13385/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (17141/10^9-3756/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
