import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.RestSector.A406.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def restA406NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable restA406NetTable pairFin pairFin
def restA406CenterInt : Int := 7366*scale/10^9
def restA406RadiusInt : Int := 3725*scale/10^9
def restA406CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => restA406NetInt.re i j - (if i=j then restA406CenterInt else 0), restA406NetInt.im⟩
def restA406CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((restA406CenteredInt.re i j)^2+(restA406CenteredInt.im i j)^2)

theorem restA406_source_net_matrix :
    sourceOrdinaryNetInt (4 : Basis) (6 : Basis) (by decide) = restA406NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (4 : Basis) (6 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = restA406NetInt := by rw [restA406_source_net_literal]; rfl

theorem restA406_centered_square_lt :
    restA406CenteredSquareInt < restA406RadiusInt^2 := by decide +kernel

theorem restA406_centered_value :
    value restA406CenteredInt = value restA406NetInt -
      (7366/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [restA406CenteredInt,restA406CenterInt,value,raw,scale]
    ring
  · simp [restA406CenteredInt,restA406CenterInt,value,raw,scale,h]

theorem restA406_centered_norm :
    ‖value restA406NetInt -
      (7366/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3725/10^9 : ℝ) := by
  rw [← restA406_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((restA406CenteredInt.re i j)^2+(restA406CenteredInt.im i j)^2)) ≤
        restA406RadiusInt^2 := by
    simpa only [restA406CenteredSquareInt] using le_of_lt restA406_centered_square_lt
  have h := integer_operator_norm_bound restA406CenteredInt restA406RadiusInt
    (by norm_num [restA406RadiusInt,scale]) square
  convert h using 1
  norm_num [restA406RadiusInt,scale]

theorem restA406_qnet_centered_norm :
    ‖sourceOrdinaryQNet (4 : Basis) (6 : Basis) (by decide) -
      (7366/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3731/10^9 : ℝ) := by
  have source := source_ordinary_net_error (4 : Basis) (6 : Basis) (by decide)
  rw [restA406_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (4 : Basis) (6 : Basis) (by decide))
    (value restA406NetInt)
    ((7366/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (4 : Basis) (6 : Basis) (by decide) - value restA406NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse restA406_centered_norm).trans (by norm_num))

theorem restA406_qnet_floor :
    (3635/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (4 : Basis) (6 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (4 : Basis) (6 : Basis) (by decide))
    (ordinary_qnet_hermitian (4 : Basis) (6 : Basis) (by decide))
    (7366/10^9) (3731/10^9) restA406_qnet_centered_norm
  have compare : (3635/10^9 : ℝ) ≤ 7366/10^9-3731/10^9 := by norm_num
  have smaller : (3635/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (7366/10^9-3731/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
