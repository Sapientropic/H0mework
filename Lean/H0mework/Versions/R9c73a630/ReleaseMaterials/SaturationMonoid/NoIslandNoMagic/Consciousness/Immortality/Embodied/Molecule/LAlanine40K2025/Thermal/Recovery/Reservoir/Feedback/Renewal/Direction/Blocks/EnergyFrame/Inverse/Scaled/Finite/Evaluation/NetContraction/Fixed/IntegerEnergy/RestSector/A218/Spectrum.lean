import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.RestSector.A218.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def restA218NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable restA218NetTable pairFin pairFin
def restA218CenterInt : Int := 9312*scale/10^9
def restA218RadiusInt : Int := 3786*scale/10^9
def restA218CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => restA218NetInt.re i j - (if i=j then restA218CenterInt else 0), restA218NetInt.im⟩
def restA218CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((restA218CenteredInt.re i j)^2+(restA218CenteredInt.im i j)^2)

theorem restA218_source_net_matrix :
    sourceOrdinaryNetInt (2 : Basis) (18 : Basis) (by decide) = restA218NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (2 : Basis) (18 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = restA218NetInt := by rw [restA218_source_net_literal]; rfl

theorem restA218_centered_square_lt :
    restA218CenteredSquareInt < restA218RadiusInt^2 := by decide +kernel

theorem restA218_centered_value :
    value restA218CenteredInt = value restA218NetInt -
      (9312/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [restA218CenteredInt,restA218CenterInt,value,raw,scale]
    ring
  · simp [restA218CenteredInt,restA218CenterInt,value,raw,scale,h]

theorem restA218_centered_norm :
    ‖value restA218NetInt -
      (9312/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3786/10^9 : ℝ) := by
  rw [← restA218_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((restA218CenteredInt.re i j)^2+(restA218CenteredInt.im i j)^2)) ≤
        restA218RadiusInt^2 := by
    simpa only [restA218CenteredSquareInt] using le_of_lt restA218_centered_square_lt
  have h := integer_operator_norm_bound restA218CenteredInt restA218RadiusInt
    (by norm_num [restA218RadiusInt,scale]) square
  convert h using 1
  norm_num [restA218RadiusInt,scale]

theorem restA218_qnet_centered_norm :
    ‖sourceOrdinaryQNet (2 : Basis) (18 : Basis) (by decide) -
      (9312/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3792/10^9 : ℝ) := by
  have source := source_ordinary_net_error (2 : Basis) (18 : Basis) (by decide)
  rw [restA218_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (2 : Basis) (18 : Basis) (by decide))
    (value restA218NetInt)
    ((9312/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (2 : Basis) (18 : Basis) (by decide) - value restA218NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse restA218_centered_norm).trans (by norm_num))

theorem restA218_qnet_floor :
    (5520/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (2 : Basis) (18 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (2 : Basis) (18 : Basis) (by decide))
    (ordinary_qnet_hermitian (2 : Basis) (18 : Basis) (by decide))
    (9312/10^9) (3792/10^9) restA218_qnet_centered_norm
  have compare : (5520/10^9 : ℝ) ≤ 9312/10^9-3792/10^9 := by norm_num
  have smaller : (5520/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (9312/10^9-3792/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
