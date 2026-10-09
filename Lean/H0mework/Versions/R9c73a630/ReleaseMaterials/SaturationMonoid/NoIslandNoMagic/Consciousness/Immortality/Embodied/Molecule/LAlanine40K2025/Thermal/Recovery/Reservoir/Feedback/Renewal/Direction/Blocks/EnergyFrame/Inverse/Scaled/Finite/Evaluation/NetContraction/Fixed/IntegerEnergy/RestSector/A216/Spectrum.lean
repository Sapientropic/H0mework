import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.RestSector.A216.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def restA216NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable restA216NetTable pairFin pairFin
def restA216CenterInt : Int := 9346*scale/10^9
def restA216RadiusInt : Int := 3786*scale/10^9
def restA216CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => restA216NetInt.re i j - (if i=j then restA216CenterInt else 0), restA216NetInt.im⟩
def restA216CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((restA216CenteredInt.re i j)^2+(restA216CenteredInt.im i j)^2)

theorem restA216_source_net_matrix :
    sourceOrdinaryNetInt (2 : Basis) (16 : Basis) (by decide) = restA216NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (2 : Basis) (16 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = restA216NetInt := by rw [restA216_source_net_literal]; rfl

theorem restA216_centered_square_lt :
    restA216CenteredSquareInt < restA216RadiusInt^2 := by decide +kernel

theorem restA216_centered_value :
    value restA216CenteredInt = value restA216NetInt -
      (9346/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [restA216CenteredInt,restA216CenterInt,value,raw,scale]
    ring
  · simp [restA216CenteredInt,restA216CenterInt,value,raw,scale,h]

theorem restA216_centered_norm :
    ‖value restA216NetInt -
      (9346/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3786/10^9 : ℝ) := by
  rw [← restA216_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((restA216CenteredInt.re i j)^2+(restA216CenteredInt.im i j)^2)) ≤
        restA216RadiusInt^2 := by
    simpa only [restA216CenteredSquareInt] using le_of_lt restA216_centered_square_lt
  have h := integer_operator_norm_bound restA216CenteredInt restA216RadiusInt
    (by norm_num [restA216RadiusInt,scale]) square
  convert h using 1
  norm_num [restA216RadiusInt,scale]

theorem restA216_qnet_centered_norm :
    ‖sourceOrdinaryQNet (2 : Basis) (16 : Basis) (by decide) -
      (9346/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3792/10^9 : ℝ) := by
  have source := source_ordinary_net_error (2 : Basis) (16 : Basis) (by decide)
  rw [restA216_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (2 : Basis) (16 : Basis) (by decide))
    (value restA216NetInt)
    ((9346/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (2 : Basis) (16 : Basis) (by decide) - value restA216NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse restA216_centered_norm).trans (by norm_num))

theorem restA216_qnet_floor :
    (5554/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (2 : Basis) (16 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (2 : Basis) (16 : Basis) (by decide))
    (ordinary_qnet_hermitian (2 : Basis) (16 : Basis) (by decide))
    (9346/10^9) (3792/10^9) restA216_qnet_centered_norm
  have compare : (5554/10^9 : ℝ) ≤ 9346/10^9-3792/10^9 := by norm_num
  have smaller : (5554/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (9346/10^9-3792/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
