import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.RestSector.A320.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def restA320NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable restA320NetTable pairFin pairFin
def restA320CenterInt : Int := 6993*scale/10^9
def restA320RadiusInt : Int := 3731*scale/10^9
def restA320CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => restA320NetInt.re i j - (if i=j then restA320CenterInt else 0), restA320NetInt.im⟩
def restA320CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((restA320CenteredInt.re i j)^2+(restA320CenteredInt.im i j)^2)

theorem restA320_source_net_matrix :
    sourceOrdinaryNetInt (3 : Basis) (20 : Basis) (by decide) = restA320NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (3 : Basis) (20 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = restA320NetInt := by rw [restA320_source_net_literal]; rfl

theorem restA320_centered_square_lt :
    restA320CenteredSquareInt < restA320RadiusInt^2 := by decide +kernel

theorem restA320_centered_value :
    value restA320CenteredInt = value restA320NetInt -
      (6993/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [restA320CenteredInt,restA320CenterInt,value,raw,scale]
    ring
  · simp [restA320CenteredInt,restA320CenterInt,value,raw,scale,h]

theorem restA320_centered_norm :
    ‖value restA320NetInt -
      (6993/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3731/10^9 : ℝ) := by
  rw [← restA320_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((restA320CenteredInt.re i j)^2+(restA320CenteredInt.im i j)^2)) ≤
        restA320RadiusInt^2 := by
    simpa only [restA320CenteredSquareInt] using le_of_lt restA320_centered_square_lt
  have h := integer_operator_norm_bound restA320CenteredInt restA320RadiusInt
    (by norm_num [restA320RadiusInt,scale]) square
  convert h using 1
  norm_num [restA320RadiusInt,scale]

theorem restA320_qnet_centered_norm :
    ‖sourceOrdinaryQNet (3 : Basis) (20 : Basis) (by decide) -
      (6993/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3737/10^9 : ℝ) := by
  have source := source_ordinary_net_error (3 : Basis) (20 : Basis) (by decide)
  rw [restA320_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (3 : Basis) (20 : Basis) (by decide))
    (value restA320NetInt)
    ((6993/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (3 : Basis) (20 : Basis) (by decide) - value restA320NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse restA320_centered_norm).trans (by norm_num))

theorem restA320_qnet_floor :
    (3256/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (3 : Basis) (20 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (3 : Basis) (20 : Basis) (by decide))
    (ordinary_qnet_hermitian (3 : Basis) (20 : Basis) (by decide))
    (6993/10^9) (3737/10^9) restA320_qnet_centered_norm
  have compare : (3256/10^9 : ℝ) ≤ 6993/10^9-3737/10^9 := by norm_num
  have smaller : (3256/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (6993/10^9-3737/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
