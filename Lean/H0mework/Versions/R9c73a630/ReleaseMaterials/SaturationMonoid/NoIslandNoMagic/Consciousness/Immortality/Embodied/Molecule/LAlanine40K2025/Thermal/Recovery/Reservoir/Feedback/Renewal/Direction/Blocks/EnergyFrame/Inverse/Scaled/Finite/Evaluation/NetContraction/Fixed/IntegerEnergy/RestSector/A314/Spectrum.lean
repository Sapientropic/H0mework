import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.RestSector.A314.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def restA314NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable restA314NetTable pairFin pairFin
def restA314CenterInt : Int := 7085*scale/10^9
def restA314RadiusInt : Int := 3729*scale/10^9
def restA314CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => restA314NetInt.re i j - (if i=j then restA314CenterInt else 0), restA314NetInt.im⟩
def restA314CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((restA314CenteredInt.re i j)^2+(restA314CenteredInt.im i j)^2)

theorem restA314_source_net_matrix :
    sourceOrdinaryNetInt (3 : Basis) (14 : Basis) (by decide) = restA314NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (3 : Basis) (14 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = restA314NetInt := by rw [restA314_source_net_literal]; rfl

theorem restA314_centered_square_lt :
    restA314CenteredSquareInt < restA314RadiusInt^2 := by decide +kernel

theorem restA314_centered_value :
    value restA314CenteredInt = value restA314NetInt -
      (7085/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [restA314CenteredInt,restA314CenterInt,value,raw,scale]
    ring
  · simp [restA314CenteredInt,restA314CenterInt,value,raw,scale,h]

theorem restA314_centered_norm :
    ‖value restA314NetInt -
      (7085/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3729/10^9 : ℝ) := by
  rw [← restA314_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((restA314CenteredInt.re i j)^2+(restA314CenteredInt.im i j)^2)) ≤
        restA314RadiusInt^2 := by
    simpa only [restA314CenteredSquareInt] using le_of_lt restA314_centered_square_lt
  have h := integer_operator_norm_bound restA314CenteredInt restA314RadiusInt
    (by norm_num [restA314RadiusInt,scale]) square
  convert h using 1
  norm_num [restA314RadiusInt,scale]

theorem restA314_qnet_centered_norm :
    ‖sourceOrdinaryQNet (3 : Basis) (14 : Basis) (by decide) -
      (7085/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3735/10^9 : ℝ) := by
  have source := source_ordinary_net_error (3 : Basis) (14 : Basis) (by decide)
  rw [restA314_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (3 : Basis) (14 : Basis) (by decide))
    (value restA314NetInt)
    ((7085/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (3 : Basis) (14 : Basis) (by decide) - value restA314NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse restA314_centered_norm).trans (by norm_num))

theorem restA314_qnet_floor :
    (3350/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (3 : Basis) (14 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (3 : Basis) (14 : Basis) (by decide))
    (ordinary_qnet_hermitian (3 : Basis) (14 : Basis) (by decide))
    (7085/10^9) (3735/10^9) restA314_qnet_centered_norm
  have compare : (3350/10^9 : ℝ) ≤ 7085/10^9-3735/10^9 := by norm_num
  have smaller : (3350/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (7085/10^9-3735/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
