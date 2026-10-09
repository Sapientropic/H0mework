import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.RestSector.A420.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def restA420NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable restA420NetTable pairFin pairFin
def restA420CenterInt : Int := 6987*scale/10^9
def restA420RadiusInt : Int := 3731*scale/10^9
def restA420CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => restA420NetInt.re i j - (if i=j then restA420CenterInt else 0), restA420NetInt.im⟩
def restA420CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((restA420CenteredInt.re i j)^2+(restA420CenteredInt.im i j)^2)

theorem restA420_source_net_matrix :
    sourceOrdinaryNetInt (4 : Basis) (20 : Basis) (by decide) = restA420NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (4 : Basis) (20 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = restA420NetInt := by rw [restA420_source_net_literal]; rfl

theorem restA420_centered_square_lt :
    restA420CenteredSquareInt < restA420RadiusInt^2 := by decide +kernel

theorem restA420_centered_value :
    value restA420CenteredInt = value restA420NetInt -
      (6987/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [restA420CenteredInt,restA420CenterInt,value,raw,scale]
    ring
  · simp [restA420CenteredInt,restA420CenterInt,value,raw,scale,h]

theorem restA420_centered_norm :
    ‖value restA420NetInt -
      (6987/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3731/10^9 : ℝ) := by
  rw [← restA420_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((restA420CenteredInt.re i j)^2+(restA420CenteredInt.im i j)^2)) ≤
        restA420RadiusInt^2 := by
    simpa only [restA420CenteredSquareInt] using le_of_lt restA420_centered_square_lt
  have h := integer_operator_norm_bound restA420CenteredInt restA420RadiusInt
    (by norm_num [restA420RadiusInt,scale]) square
  convert h using 1
  norm_num [restA420RadiusInt,scale]

theorem restA420_qnet_centered_norm :
    ‖sourceOrdinaryQNet (4 : Basis) (20 : Basis) (by decide) -
      (6987/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3737/10^9 : ℝ) := by
  have source := source_ordinary_net_error (4 : Basis) (20 : Basis) (by decide)
  rw [restA420_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (4 : Basis) (20 : Basis) (by decide))
    (value restA420NetInt)
    ((6987/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (4 : Basis) (20 : Basis) (by decide) - value restA420NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse restA420_centered_norm).trans (by norm_num))

theorem restA420_qnet_floor :
    (3250/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (4 : Basis) (20 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (4 : Basis) (20 : Basis) (by decide))
    (ordinary_qnet_hermitian (4 : Basis) (20 : Basis) (by decide))
    (6987/10^9) (3737/10^9) restA420_qnet_centered_norm
  have compare : (3250/10^9 : ℝ) ≤ 6987/10^9-3737/10^9 := by norm_num
  have smaller : (3250/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (6987/10^9-3737/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
