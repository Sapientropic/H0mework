import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.RestSector.A323.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def restA323NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable restA323NetTable pairFin pairFin
def restA323CenterInt : Int := 6917*scale/10^9
def restA323RadiusInt : Int := 3732*scale/10^9
def restA323CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => restA323NetInt.re i j - (if i=j then restA323CenterInt else 0), restA323NetInt.im⟩
def restA323CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((restA323CenteredInt.re i j)^2+(restA323CenteredInt.im i j)^2)

theorem restA323_source_net_matrix :
    sourceOrdinaryNetInt (3 : Basis) (23 : Basis) (by decide) = restA323NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (3 : Basis) (23 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = restA323NetInt := by rw [restA323_source_net_literal]; rfl

theorem restA323_centered_square_lt :
    restA323CenteredSquareInt < restA323RadiusInt^2 := by decide +kernel

theorem restA323_centered_value :
    value restA323CenteredInt = value restA323NetInt -
      (6917/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [restA323CenteredInt,restA323CenterInt,value,raw,scale]
    ring
  · simp [restA323CenteredInt,restA323CenterInt,value,raw,scale,h]

theorem restA323_centered_norm :
    ‖value restA323NetInt -
      (6917/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3732/10^9 : ℝ) := by
  rw [← restA323_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((restA323CenteredInt.re i j)^2+(restA323CenteredInt.im i j)^2)) ≤
        restA323RadiusInt^2 := by
    simpa only [restA323CenteredSquareInt] using le_of_lt restA323_centered_square_lt
  have h := integer_operator_norm_bound restA323CenteredInt restA323RadiusInt
    (by norm_num [restA323RadiusInt,scale]) square
  convert h using 1
  norm_num [restA323RadiusInt,scale]

theorem restA323_qnet_centered_norm :
    ‖sourceOrdinaryQNet (3 : Basis) (23 : Basis) (by decide) -
      (6917/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3738/10^9 : ℝ) := by
  have source := source_ordinary_net_error (3 : Basis) (23 : Basis) (by decide)
  rw [restA323_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (3 : Basis) (23 : Basis) (by decide))
    (value restA323NetInt)
    ((6917/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (3 : Basis) (23 : Basis) (by decide) - value restA323NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse restA323_centered_norm).trans (by norm_num))

theorem restA323_qnet_floor :
    (3179/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (3 : Basis) (23 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (3 : Basis) (23 : Basis) (by decide))
    (ordinary_qnet_hermitian (3 : Basis) (23 : Basis) (by decide))
    (6917/10^9) (3738/10^9) restA323_qnet_centered_norm
  have compare : (3179/10^9 : ℝ) ≤ 6917/10^9-3738/10^9 := by norm_num
  have smaller : (3179/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (6917/10^9-3738/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
