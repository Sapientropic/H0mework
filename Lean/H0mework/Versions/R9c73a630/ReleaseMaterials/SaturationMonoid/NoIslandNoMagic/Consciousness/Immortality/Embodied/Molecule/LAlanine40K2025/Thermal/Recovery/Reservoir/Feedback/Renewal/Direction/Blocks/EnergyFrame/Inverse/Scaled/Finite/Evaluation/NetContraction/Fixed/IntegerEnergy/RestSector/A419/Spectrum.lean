import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.RestSector.A419.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def restA419NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable restA419NetTable pairFin pairFin
def restA419CenterInt : Int := 6990*scale/10^9
def restA419RadiusInt : Int := 3731*scale/10^9
def restA419CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => restA419NetInt.re i j - (if i=j then restA419CenterInt else 0), restA419NetInt.im⟩
def restA419CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((restA419CenteredInt.re i j)^2+(restA419CenteredInt.im i j)^2)

theorem restA419_source_net_matrix :
    sourceOrdinaryNetInt (4 : Basis) (19 : Basis) (by decide) = restA419NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (4 : Basis) (19 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = restA419NetInt := by rw [restA419_source_net_literal]; rfl

theorem restA419_centered_square_lt :
    restA419CenteredSquareInt < restA419RadiusInt^2 := by decide +kernel

theorem restA419_centered_value :
    value restA419CenteredInt = value restA419NetInt -
      (6990/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [restA419CenteredInt,restA419CenterInt,value,raw,scale]
    ring
  · simp [restA419CenteredInt,restA419CenterInt,value,raw,scale,h]

theorem restA419_centered_norm :
    ‖value restA419NetInt -
      (6990/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3731/10^9 : ℝ) := by
  rw [← restA419_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((restA419CenteredInt.re i j)^2+(restA419CenteredInt.im i j)^2)) ≤
        restA419RadiusInt^2 := by
    simpa only [restA419CenteredSquareInt] using le_of_lt restA419_centered_square_lt
  have h := integer_operator_norm_bound restA419CenteredInt restA419RadiusInt
    (by norm_num [restA419RadiusInt,scale]) square
  convert h using 1
  norm_num [restA419RadiusInt,scale]

theorem restA419_qnet_centered_norm :
    ‖sourceOrdinaryQNet (4 : Basis) (19 : Basis) (by decide) -
      (6990/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3737/10^9 : ℝ) := by
  have source := source_ordinary_net_error (4 : Basis) (19 : Basis) (by decide)
  rw [restA419_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (4 : Basis) (19 : Basis) (by decide))
    (value restA419NetInt)
    ((6990/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (4 : Basis) (19 : Basis) (by decide) - value restA419NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse restA419_centered_norm).trans (by norm_num))

theorem restA419_qnet_floor :
    (3253/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (4 : Basis) (19 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (4 : Basis) (19 : Basis) (by decide))
    (ordinary_qnet_hermitian (4 : Basis) (19 : Basis) (by decide))
    (6990/10^9) (3737/10^9) restA419_qnet_centered_norm
  have compare : (3253/10^9 : ℝ) ≤ 6990/10^9-3737/10^9 := by norm_num
  have smaller : (3253/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (6990/10^9-3737/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
