import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.RestSector.A209.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def restA209NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable restA209NetTable pairFin pairFin
def restA209CenterInt : Int := 9530*scale/10^9
def restA209RadiusInt : Int := 3781*scale/10^9
def restA209CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => restA209NetInt.re i j - (if i=j then restA209CenterInt else 0), restA209NetInt.im⟩
def restA209CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((restA209CenteredInt.re i j)^2+(restA209CenteredInt.im i j)^2)

theorem restA209_source_net_matrix :
    sourceOrdinaryNetInt (2 : Basis) (9 : Basis) (by decide) = restA209NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (2 : Basis) (9 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = restA209NetInt := by rw [restA209_source_net_literal]; rfl

theorem restA209_centered_square_lt :
    restA209CenteredSquareInt < restA209RadiusInt^2 := by decide +kernel

theorem restA209_centered_value :
    value restA209CenteredInt = value restA209NetInt -
      (9530/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [restA209CenteredInt,restA209CenterInt,value,raw,scale]
    ring
  · simp [restA209CenteredInt,restA209CenterInt,value,raw,scale,h]

theorem restA209_centered_norm :
    ‖value restA209NetInt -
      (9530/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3781/10^9 : ℝ) := by
  rw [← restA209_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((restA209CenteredInt.re i j)^2+(restA209CenteredInt.im i j)^2)) ≤
        restA209RadiusInt^2 := by
    simpa only [restA209CenteredSquareInt] using le_of_lt restA209_centered_square_lt
  have h := integer_operator_norm_bound restA209CenteredInt restA209RadiusInt
    (by norm_num [restA209RadiusInt,scale]) square
  convert h using 1
  norm_num [restA209RadiusInt,scale]

theorem restA209_qnet_centered_norm :
    ‖sourceOrdinaryQNet (2 : Basis) (9 : Basis) (by decide) -
      (9530/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3787/10^9 : ℝ) := by
  have source := source_ordinary_net_error (2 : Basis) (9 : Basis) (by decide)
  rw [restA209_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (2 : Basis) (9 : Basis) (by decide))
    (value restA209NetInt)
    ((9530/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (2 : Basis) (9 : Basis) (by decide) - value restA209NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse restA209_centered_norm).trans (by norm_num))

theorem restA209_qnet_floor :
    (5743/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (2 : Basis) (9 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (2 : Basis) (9 : Basis) (by decide))
    (ordinary_qnet_hermitian (2 : Basis) (9 : Basis) (by decide))
    (9530/10^9) (3787/10^9) restA209_qnet_centered_norm
  have compare : (5743/10^9 : ℝ) ≤ 9530/10^9-3787/10^9 := by norm_num
  have smaller : (5743/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (9530/10^9-3787/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
