import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.RestSector.A312.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def restA312NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable restA312NetTable pairFin pairFin
def restA312CenterInt : Int := 7165*scale/10^9
def restA312RadiusInt : Int := 3728*scale/10^9
def restA312CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => restA312NetInt.re i j - (if i=j then restA312CenterInt else 0), restA312NetInt.im⟩
def restA312CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((restA312CenteredInt.re i j)^2+(restA312CenteredInt.im i j)^2)

theorem restA312_source_net_matrix :
    sourceOrdinaryNetInt (3 : Basis) (12 : Basis) (by decide) = restA312NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (3 : Basis) (12 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = restA312NetInt := by rw [restA312_source_net_literal]; rfl

theorem restA312_centered_square_lt :
    restA312CenteredSquareInt < restA312RadiusInt^2 := by decide +kernel

theorem restA312_centered_value :
    value restA312CenteredInt = value restA312NetInt -
      (7165/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [restA312CenteredInt,restA312CenterInt,value,raw,scale]
    ring
  · simp [restA312CenteredInt,restA312CenterInt,value,raw,scale,h]

theorem restA312_centered_norm :
    ‖value restA312NetInt -
      (7165/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3728/10^9 : ℝ) := by
  rw [← restA312_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((restA312CenteredInt.re i j)^2+(restA312CenteredInt.im i j)^2)) ≤
        restA312RadiusInt^2 := by
    simpa only [restA312CenteredSquareInt] using le_of_lt restA312_centered_square_lt
  have h := integer_operator_norm_bound restA312CenteredInt restA312RadiusInt
    (by norm_num [restA312RadiusInt,scale]) square
  convert h using 1
  norm_num [restA312RadiusInt,scale]

theorem restA312_qnet_centered_norm :
    ‖sourceOrdinaryQNet (3 : Basis) (12 : Basis) (by decide) -
      (7165/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3734/10^9 : ℝ) := by
  have source := source_ordinary_net_error (3 : Basis) (12 : Basis) (by decide)
  rw [restA312_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (3 : Basis) (12 : Basis) (by decide))
    (value restA312NetInt)
    ((7165/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (3 : Basis) (12 : Basis) (by decide) - value restA312NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse restA312_centered_norm).trans (by norm_num))

theorem restA312_qnet_floor :
    (3431/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (3 : Basis) (12 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (3 : Basis) (12 : Basis) (by decide))
    (ordinary_qnet_hermitian (3 : Basis) (12 : Basis) (by decide))
    (7165/10^9) (3734/10^9) restA312_qnet_centered_norm
  have compare : (3431/10^9 : ℝ) ≤ 7165/10^9-3734/10^9 := by norm_num
  have smaller : (3431/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (7165/10^9-3734/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
