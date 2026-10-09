import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.RestSector.A319.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def restA319NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable restA319NetTable pairFin pairFin
def restA319CenterInt : Int := 6997*scale/10^9
def restA319RadiusInt : Int := 3731*scale/10^9
def restA319CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => restA319NetInt.re i j - (if i=j then restA319CenterInt else 0), restA319NetInt.im⟩
def restA319CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((restA319CenteredInt.re i j)^2+(restA319CenteredInt.im i j)^2)

theorem restA319_source_net_matrix :
    sourceOrdinaryNetInt (3 : Basis) (19 : Basis) (by decide) = restA319NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (3 : Basis) (19 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = restA319NetInt := by rw [restA319_source_net_literal]; rfl

theorem restA319_centered_square_lt :
    restA319CenteredSquareInt < restA319RadiusInt^2 := by decide +kernel

theorem restA319_centered_value :
    value restA319CenteredInt = value restA319NetInt -
      (6997/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [restA319CenteredInt,restA319CenterInt,value,raw,scale]
    ring
  · simp [restA319CenteredInt,restA319CenterInt,value,raw,scale,h]

theorem restA319_centered_norm :
    ‖value restA319NetInt -
      (6997/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3731/10^9 : ℝ) := by
  rw [← restA319_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((restA319CenteredInt.re i j)^2+(restA319CenteredInt.im i j)^2)) ≤
        restA319RadiusInt^2 := by
    simpa only [restA319CenteredSquareInt] using le_of_lt restA319_centered_square_lt
  have h := integer_operator_norm_bound restA319CenteredInt restA319RadiusInt
    (by norm_num [restA319RadiusInt,scale]) square
  convert h using 1
  norm_num [restA319RadiusInt,scale]

theorem restA319_qnet_centered_norm :
    ‖sourceOrdinaryQNet (3 : Basis) (19 : Basis) (by decide) -
      (6997/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3737/10^9 : ℝ) := by
  have source := source_ordinary_net_error (3 : Basis) (19 : Basis) (by decide)
  rw [restA319_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (3 : Basis) (19 : Basis) (by decide))
    (value restA319NetInt)
    ((6997/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (3 : Basis) (19 : Basis) (by decide) - value restA319NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse restA319_centered_norm).trans (by norm_num))

theorem restA319_qnet_floor :
    (3260/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (3 : Basis) (19 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (3 : Basis) (19 : Basis) (by decide))
    (ordinary_qnet_hermitian (3 : Basis) (19 : Basis) (by decide))
    (6997/10^9) (3737/10^9) restA319_qnet_centered_norm
  have compare : (3260/10^9 : ℝ) ≤ 6997/10^9-3737/10^9 := by norm_num
  have smaller : (3260/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (6997/10^9-3737/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
