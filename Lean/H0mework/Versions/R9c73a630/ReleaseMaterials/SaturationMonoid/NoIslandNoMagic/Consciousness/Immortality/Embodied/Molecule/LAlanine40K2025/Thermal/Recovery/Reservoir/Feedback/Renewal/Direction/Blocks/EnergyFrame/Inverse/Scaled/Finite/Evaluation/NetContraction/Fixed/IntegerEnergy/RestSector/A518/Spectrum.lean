import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.RestSector.A518.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def restA518NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable restA518NetTable pairFin pairFin
def restA518CenterInt : Int := 6977*scale/10^9
def restA518RadiusInt : Int := 3730*scale/10^9
def restA518CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => restA518NetInt.re i j - (if i=j then restA518CenterInt else 0), restA518NetInt.im⟩
def restA518CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((restA518CenteredInt.re i j)^2+(restA518CenteredInt.im i j)^2)

theorem restA518_source_net_matrix :
    sourceOrdinaryNetInt (5 : Basis) (18 : Basis) (by decide) = restA518NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (5 : Basis) (18 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = restA518NetInt := by rw [restA518_source_net_literal]; rfl

theorem restA518_centered_square_lt :
    restA518CenteredSquareInt < restA518RadiusInt^2 := by decide +kernel

theorem restA518_centered_value :
    value restA518CenteredInt = value restA518NetInt -
      (6977/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [restA518CenteredInt,restA518CenterInt,value,raw,scale]
    ring
  · simp [restA518CenteredInt,restA518CenterInt,value,raw,scale,h]

theorem restA518_centered_norm :
    ‖value restA518NetInt -
      (6977/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3730/10^9 : ℝ) := by
  rw [← restA518_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((restA518CenteredInt.re i j)^2+(restA518CenteredInt.im i j)^2)) ≤
        restA518RadiusInt^2 := by
    simpa only [restA518CenteredSquareInt] using le_of_lt restA518_centered_square_lt
  have h := integer_operator_norm_bound restA518CenteredInt restA518RadiusInt
    (by norm_num [restA518RadiusInt,scale]) square
  convert h using 1
  norm_num [restA518RadiusInt,scale]

theorem restA518_qnet_centered_norm :
    ‖sourceOrdinaryQNet (5 : Basis) (18 : Basis) (by decide) -
      (6977/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3736/10^9 : ℝ) := by
  have source := source_ordinary_net_error (5 : Basis) (18 : Basis) (by decide)
  rw [restA518_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (5 : Basis) (18 : Basis) (by decide))
    (value restA518NetInt)
    ((6977/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (5 : Basis) (18 : Basis) (by decide) - value restA518NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse restA518_centered_norm).trans (by norm_num))

theorem restA518_qnet_floor :
    (3241/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (5 : Basis) (18 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (5 : Basis) (18 : Basis) (by decide))
    (ordinary_qnet_hermitian (5 : Basis) (18 : Basis) (by decide))
    (6977/10^9) (3736/10^9) restA518_qnet_centered_norm
  have compare : (3241/10^9 : ℝ) ≤ 6977/10^9-3736/10^9 := by norm_num
  have smaller : (3241/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (6977/10^9-3736/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
