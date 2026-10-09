import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.RestSector.A214.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def restA214NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable restA214NetTable pairFin pairFin
def restA214CenterInt : Int := 9382*scale/10^9
def restA214RadiusInt : Int := 3785*scale/10^9
def restA214CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => restA214NetInt.re i j - (if i=j then restA214CenterInt else 0), restA214NetInt.im⟩
def restA214CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((restA214CenteredInt.re i j)^2+(restA214CenteredInt.im i j)^2)

theorem restA214_source_net_matrix :
    sourceOrdinaryNetInt (2 : Basis) (14 : Basis) (by decide) = restA214NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (2 : Basis) (14 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = restA214NetInt := by rw [restA214_source_net_literal]; rfl

theorem restA214_centered_square_lt :
    restA214CenteredSquareInt < restA214RadiusInt^2 := by decide +kernel

theorem restA214_centered_value :
    value restA214CenteredInt = value restA214NetInt -
      (9382/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [restA214CenteredInt,restA214CenterInt,value,raw,scale]
    ring
  · simp [restA214CenteredInt,restA214CenterInt,value,raw,scale,h]

theorem restA214_centered_norm :
    ‖value restA214NetInt -
      (9382/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3785/10^9 : ℝ) := by
  rw [← restA214_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((restA214CenteredInt.re i j)^2+(restA214CenteredInt.im i j)^2)) ≤
        restA214RadiusInt^2 := by
    simpa only [restA214CenteredSquareInt] using le_of_lt restA214_centered_square_lt
  have h := integer_operator_norm_bound restA214CenteredInt restA214RadiusInt
    (by norm_num [restA214RadiusInt,scale]) square
  convert h using 1
  norm_num [restA214RadiusInt,scale]

theorem restA214_qnet_centered_norm :
    ‖sourceOrdinaryQNet (2 : Basis) (14 : Basis) (by decide) -
      (9382/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3791/10^9 : ℝ) := by
  have source := source_ordinary_net_error (2 : Basis) (14 : Basis) (by decide)
  rw [restA214_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (2 : Basis) (14 : Basis) (by decide))
    (value restA214NetInt)
    ((9382/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (2 : Basis) (14 : Basis) (by decide) - value restA214NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse restA214_centered_norm).trans (by norm_num))

theorem restA214_qnet_floor :
    (5591/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (2 : Basis) (14 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (2 : Basis) (14 : Basis) (by decide))
    (ordinary_qnet_hermitian (2 : Basis) (14 : Basis) (by decide))
    (9382/10^9) (3791/10^9) restA214_qnet_centered_norm
  have compare : (5591/10^9 : ℝ) ≤ 9382/10^9-3791/10^9 := by norm_num
  have smaller : (5591/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (9382/10^9-3791/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
