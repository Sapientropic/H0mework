import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.RestSector.A523.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def restA523NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable restA523NetTable pairFin pairFin
def restA523CenterInt : Int := 6879*scale/10^9
def restA523RadiusInt : Int := 3731*scale/10^9
def restA523CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => restA523NetInt.re i j - (if i=j then restA523CenterInt else 0), restA523NetInt.im⟩
def restA523CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((restA523CenteredInt.re i j)^2+(restA523CenteredInt.im i j)^2)

theorem restA523_source_net_matrix :
    sourceOrdinaryNetInt (5 : Basis) (23 : Basis) (by decide) = restA523NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (5 : Basis) (23 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = restA523NetInt := by rw [restA523_source_net_literal]; rfl

theorem restA523_centered_square_lt :
    restA523CenteredSquareInt < restA523RadiusInt^2 := by decide +kernel

theorem restA523_centered_value :
    value restA523CenteredInt = value restA523NetInt -
      (6879/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [restA523CenteredInt,restA523CenterInt,value,raw,scale]
    ring
  · simp [restA523CenteredInt,restA523CenterInt,value,raw,scale,h]

theorem restA523_centered_norm :
    ‖value restA523NetInt -
      (6879/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3731/10^9 : ℝ) := by
  rw [← restA523_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((restA523CenteredInt.re i j)^2+(restA523CenteredInt.im i j)^2)) ≤
        restA523RadiusInt^2 := by
    simpa only [restA523CenteredSquareInt] using le_of_lt restA523_centered_square_lt
  have h := integer_operator_norm_bound restA523CenteredInt restA523RadiusInt
    (by norm_num [restA523RadiusInt,scale]) square
  convert h using 1
  norm_num [restA523RadiusInt,scale]

theorem restA523_qnet_centered_norm :
    ‖sourceOrdinaryQNet (5 : Basis) (23 : Basis) (by decide) -
      (6879/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3737/10^9 : ℝ) := by
  have source := source_ordinary_net_error (5 : Basis) (23 : Basis) (by decide)
  rw [restA523_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (5 : Basis) (23 : Basis) (by decide))
    (value restA523NetInt)
    ((6879/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (5 : Basis) (23 : Basis) (by decide) - value restA523NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse restA523_centered_norm).trans (by norm_num))

theorem restA523_qnet_floor :
    (3142/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (5 : Basis) (23 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (5 : Basis) (23 : Basis) (by decide))
    (ordinary_qnet_hermitian (5 : Basis) (23 : Basis) (by decide))
    (6879/10^9) (3737/10^9) restA523_qnet_centered_norm
  have compare : (3142/10^9 : ℝ) ≤ 6879/10^9-3737/10^9 := by norm_num
  have smaller : (3142/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (6879/10^9-3737/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
