import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.RestSector.A521.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def restA521NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable restA521NetTable pairFin pairFin
def restA521CenterInt : Int := 6893*scale/10^9
def restA521RadiusInt : Int := 3731*scale/10^9
def restA521CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => restA521NetInt.re i j - (if i=j then restA521CenterInt else 0), restA521NetInt.im⟩
def restA521CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((restA521CenteredInt.re i j)^2+(restA521CenteredInt.im i j)^2)

theorem restA521_source_net_matrix :
    sourceOrdinaryNetInt (5 : Basis) (21 : Basis) (by decide) = restA521NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (5 : Basis) (21 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = restA521NetInt := by rw [restA521_source_net_literal]; rfl

theorem restA521_centered_square_lt :
    restA521CenteredSquareInt < restA521RadiusInt^2 := by decide +kernel

theorem restA521_centered_value :
    value restA521CenteredInt = value restA521NetInt -
      (6893/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [restA521CenteredInt,restA521CenterInt,value,raw,scale]
    ring
  · simp [restA521CenteredInt,restA521CenterInt,value,raw,scale,h]

theorem restA521_centered_norm :
    ‖value restA521NetInt -
      (6893/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3731/10^9 : ℝ) := by
  rw [← restA521_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((restA521CenteredInt.re i j)^2+(restA521CenteredInt.im i j)^2)) ≤
        restA521RadiusInt^2 := by
    simpa only [restA521CenteredSquareInt] using le_of_lt restA521_centered_square_lt
  have h := integer_operator_norm_bound restA521CenteredInt restA521RadiusInt
    (by norm_num [restA521RadiusInt,scale]) square
  convert h using 1
  norm_num [restA521RadiusInt,scale]

theorem restA521_qnet_centered_norm :
    ‖sourceOrdinaryQNet (5 : Basis) (21 : Basis) (by decide) -
      (6893/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3737/10^9 : ℝ) := by
  have source := source_ordinary_net_error (5 : Basis) (21 : Basis) (by decide)
  rw [restA521_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (5 : Basis) (21 : Basis) (by decide))
    (value restA521NetInt)
    ((6893/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (5 : Basis) (21 : Basis) (by decide) - value restA521NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse restA521_centered_norm).trans (by norm_num))

theorem restA521_qnet_floor :
    (3156/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (5 : Basis) (21 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (5 : Basis) (21 : Basis) (by decide))
    (ordinary_qnet_hermitian (5 : Basis) (21 : Basis) (by decide))
    (6893/10^9) (3737/10^9) restA521_qnet_centered_norm
  have compare : (3156/10^9 : ℝ) ≤ 6893/10^9-3737/10^9 := by norm_num
  have smaller : (3156/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (6893/10^9-3737/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
