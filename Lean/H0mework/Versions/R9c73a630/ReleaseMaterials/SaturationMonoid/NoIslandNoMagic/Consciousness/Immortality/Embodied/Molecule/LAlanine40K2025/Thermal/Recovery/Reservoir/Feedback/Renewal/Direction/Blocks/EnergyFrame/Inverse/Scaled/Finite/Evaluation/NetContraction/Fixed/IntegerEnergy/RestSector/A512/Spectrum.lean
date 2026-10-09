import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.RestSector.A512.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def restA512NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable restA512NetTable pairFin pairFin
def restA512CenterInt : Int := 7127*scale/10^9
def restA512RadiusInt : Int := 3727*scale/10^9
def restA512CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => restA512NetInt.re i j - (if i=j then restA512CenterInt else 0), restA512NetInt.im⟩
def restA512CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((restA512CenteredInt.re i j)^2+(restA512CenteredInt.im i j)^2)

theorem restA512_source_net_matrix :
    sourceOrdinaryNetInt (5 : Basis) (12 : Basis) (by decide) = restA512NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (5 : Basis) (12 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = restA512NetInt := by rw [restA512_source_net_literal]; rfl

theorem restA512_centered_square_lt :
    restA512CenteredSquareInt < restA512RadiusInt^2 := by decide +kernel

theorem restA512_centered_value :
    value restA512CenteredInt = value restA512NetInt -
      (7127/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [restA512CenteredInt,restA512CenterInt,value,raw,scale]
    ring
  · simp [restA512CenteredInt,restA512CenterInt,value,raw,scale,h]

theorem restA512_centered_norm :
    ‖value restA512NetInt -
      (7127/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3727/10^9 : ℝ) := by
  rw [← restA512_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((restA512CenteredInt.re i j)^2+(restA512CenteredInt.im i j)^2)) ≤
        restA512RadiusInt^2 := by
    simpa only [restA512CenteredSquareInt] using le_of_lt restA512_centered_square_lt
  have h := integer_operator_norm_bound restA512CenteredInt restA512RadiusInt
    (by norm_num [restA512RadiusInt,scale]) square
  convert h using 1
  norm_num [restA512RadiusInt,scale]

theorem restA512_qnet_centered_norm :
    ‖sourceOrdinaryQNet (5 : Basis) (12 : Basis) (by decide) -
      (7127/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3733/10^9 : ℝ) := by
  have source := source_ordinary_net_error (5 : Basis) (12 : Basis) (by decide)
  rw [restA512_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (5 : Basis) (12 : Basis) (by decide))
    (value restA512NetInt)
    ((7127/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (5 : Basis) (12 : Basis) (by decide) - value restA512NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse restA512_centered_norm).trans (by norm_num))

theorem restA512_qnet_floor :
    (3394/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (5 : Basis) (12 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (5 : Basis) (12 : Basis) (by decide))
    (ordinary_qnet_hermitian (5 : Basis) (12 : Basis) (by decide))
    (7127/10^9) (3733/10^9) restA512_qnet_centered_norm
  have compare : (3394/10^9 : ℝ) ≤ 7127/10^9-3733/10^9 := by norm_num
  have smaller : (3394/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (7127/10^9-3733/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
