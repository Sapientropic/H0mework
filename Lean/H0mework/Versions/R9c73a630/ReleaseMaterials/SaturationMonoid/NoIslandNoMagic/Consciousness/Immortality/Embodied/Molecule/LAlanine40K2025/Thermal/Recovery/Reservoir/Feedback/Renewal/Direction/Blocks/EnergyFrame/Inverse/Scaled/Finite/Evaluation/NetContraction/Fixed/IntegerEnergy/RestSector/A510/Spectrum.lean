import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.RestSector.A510.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def restA510NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable restA510NetTable pairFin pairFin
def restA510CenterInt : Int := 7144*scale/10^9
def restA510RadiusInt : Int := 3727*scale/10^9
def restA510CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => restA510NetInt.re i j - (if i=j then restA510CenterInt else 0), restA510NetInt.im⟩
def restA510CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((restA510CenteredInt.re i j)^2+(restA510CenteredInt.im i j)^2)

theorem restA510_source_net_matrix :
    sourceOrdinaryNetInt (5 : Basis) (10 : Basis) (by decide) = restA510NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (5 : Basis) (10 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = restA510NetInt := by rw [restA510_source_net_literal]; rfl

theorem restA510_centered_square_lt :
    restA510CenteredSquareInt < restA510RadiusInt^2 := by decide +kernel

theorem restA510_centered_value :
    value restA510CenteredInt = value restA510NetInt -
      (7144/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [restA510CenteredInt,restA510CenterInt,value,raw,scale]
    ring
  · simp [restA510CenteredInt,restA510CenterInt,value,raw,scale,h]

theorem restA510_centered_norm :
    ‖value restA510NetInt -
      (7144/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3727/10^9 : ℝ) := by
  rw [← restA510_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((restA510CenteredInt.re i j)^2+(restA510CenteredInt.im i j)^2)) ≤
        restA510RadiusInt^2 := by
    simpa only [restA510CenteredSquareInt] using le_of_lt restA510_centered_square_lt
  have h := integer_operator_norm_bound restA510CenteredInt restA510RadiusInt
    (by norm_num [restA510RadiusInt,scale]) square
  convert h using 1
  norm_num [restA510RadiusInt,scale]

theorem restA510_qnet_centered_norm :
    ‖sourceOrdinaryQNet (5 : Basis) (10 : Basis) (by decide) -
      (7144/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3733/10^9 : ℝ) := by
  have source := source_ordinary_net_error (5 : Basis) (10 : Basis) (by decide)
  rw [restA510_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (5 : Basis) (10 : Basis) (by decide))
    (value restA510NetInt)
    ((7144/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (5 : Basis) (10 : Basis) (by decide) - value restA510NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse restA510_centered_norm).trans (by norm_num))

theorem restA510_qnet_floor :
    (3411/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (5 : Basis) (10 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (5 : Basis) (10 : Basis) (by decide))
    (ordinary_qnet_hermitian (5 : Basis) (10 : Basis) (by decide))
    (7144/10^9) (3733/10^9) restA510_qnet_centered_norm
  have compare : (3411/10^9 : ℝ) ≤ 7144/10^9-3733/10^9 := by norm_num
  have smaller : (3411/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (7144/10^9-3733/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
