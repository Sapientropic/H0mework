import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.RestSector.A206.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def restA206NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable restA206NetTable pairFin pairFin
def restA206CenterInt : Int := 9673*scale/10^9
def restA206RadiusInt : Int := 3777*scale/10^9
def restA206CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => restA206NetInt.re i j - (if i=j then restA206CenterInt else 0), restA206NetInt.im⟩
def restA206CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((restA206CenteredInt.re i j)^2+(restA206CenteredInt.im i j)^2)

theorem restA206_source_net_matrix :
    sourceOrdinaryNetInt (2 : Basis) (6 : Basis) (by decide) = restA206NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (2 : Basis) (6 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = restA206NetInt := by rw [restA206_source_net_literal]; rfl

theorem restA206_centered_square_lt :
    restA206CenteredSquareInt < restA206RadiusInt^2 := by decide +kernel

theorem restA206_centered_value :
    value restA206CenteredInt = value restA206NetInt -
      (9673/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [restA206CenteredInt,restA206CenterInt,value,raw,scale]
    ring
  · simp [restA206CenteredInt,restA206CenterInt,value,raw,scale,h]

theorem restA206_centered_norm :
    ‖value restA206NetInt -
      (9673/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3777/10^9 : ℝ) := by
  rw [← restA206_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((restA206CenteredInt.re i j)^2+(restA206CenteredInt.im i j)^2)) ≤
        restA206RadiusInt^2 := by
    simpa only [restA206CenteredSquareInt] using le_of_lt restA206_centered_square_lt
  have h := integer_operator_norm_bound restA206CenteredInt restA206RadiusInt
    (by norm_num [restA206RadiusInt,scale]) square
  convert h using 1
  norm_num [restA206RadiusInt,scale]

theorem restA206_qnet_centered_norm :
    ‖sourceOrdinaryQNet (2 : Basis) (6 : Basis) (by decide) -
      (9673/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3783/10^9 : ℝ) := by
  have source := source_ordinary_net_error (2 : Basis) (6 : Basis) (by decide)
  rw [restA206_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (2 : Basis) (6 : Basis) (by decide))
    (value restA206NetInt)
    ((9673/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (2 : Basis) (6 : Basis) (by decide) - value restA206NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse restA206_centered_norm).trans (by norm_num))

theorem restA206_qnet_floor :
    (5890/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (2 : Basis) (6 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (2 : Basis) (6 : Basis) (by decide))
    (ordinary_qnet_hermitian (2 : Basis) (6 : Basis) (by decide))
    (9673/10^9) (3783/10^9) restA206_qnet_centered_norm
  have compare : (5890/10^9 : ℝ) ≤ 9673/10^9-3783/10^9 := by norm_num
  have smaller : (5890/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (9673/10^9-3783/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
