import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.RestSector.A208.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def restA208NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable restA208NetTable pairFin pairFin
def restA208CenterInt : Int := 9556*scale/10^9
def restA208RadiusInt : Int := 3780*scale/10^9
def restA208CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => restA208NetInt.re i j - (if i=j then restA208CenterInt else 0), restA208NetInt.im⟩
def restA208CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((restA208CenteredInt.re i j)^2+(restA208CenteredInt.im i j)^2)

theorem restA208_source_net_matrix :
    sourceOrdinaryNetInt (2 : Basis) (8 : Basis) (by decide) = restA208NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (2 : Basis) (8 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = restA208NetInt := by rw [restA208_source_net_literal]; rfl

theorem restA208_centered_square_lt :
    restA208CenteredSquareInt < restA208RadiusInt^2 := by decide +kernel

theorem restA208_centered_value :
    value restA208CenteredInt = value restA208NetInt -
      (9556/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [restA208CenteredInt,restA208CenterInt,value,raw,scale]
    ring
  · simp [restA208CenteredInt,restA208CenterInt,value,raw,scale,h]

theorem restA208_centered_norm :
    ‖value restA208NetInt -
      (9556/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3780/10^9 : ℝ) := by
  rw [← restA208_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((restA208CenteredInt.re i j)^2+(restA208CenteredInt.im i j)^2)) ≤
        restA208RadiusInt^2 := by
    simpa only [restA208CenteredSquareInt] using le_of_lt restA208_centered_square_lt
  have h := integer_operator_norm_bound restA208CenteredInt restA208RadiusInt
    (by norm_num [restA208RadiusInt,scale]) square
  convert h using 1
  norm_num [restA208RadiusInt,scale]

theorem restA208_qnet_centered_norm :
    ‖sourceOrdinaryQNet (2 : Basis) (8 : Basis) (by decide) -
      (9556/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3786/10^9 : ℝ) := by
  have source := source_ordinary_net_error (2 : Basis) (8 : Basis) (by decide)
  rw [restA208_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (2 : Basis) (8 : Basis) (by decide))
    (value restA208NetInt)
    ((9556/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (2 : Basis) (8 : Basis) (by decide) - value restA208NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse restA208_centered_norm).trans (by norm_num))

theorem restA208_qnet_floor :
    (5770/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (2 : Basis) (8 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (2 : Basis) (8 : Basis) (by decide))
    (ordinary_qnet_hermitian (2 : Basis) (8 : Basis) (by decide))
    (9556/10^9) (3786/10^9) restA208_qnet_centered_norm
  have compare : (5770/10^9 : ℝ) ≤ 9556/10^9-3786/10^9 := by norm_num
  have smaller : (5770/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (9556/10^9-3786/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
