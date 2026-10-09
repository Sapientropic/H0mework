import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.RestSector.A219.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def restA219NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable restA219NetTable pairFin pairFin
def restA219CenterInt : Int := 9293*scale/10^9
def restA219RadiusInt : Int := 3787*scale/10^9
def restA219CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => restA219NetInt.re i j - (if i=j then restA219CenterInt else 0), restA219NetInt.im⟩
def restA219CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((restA219CenteredInt.re i j)^2+(restA219CenteredInt.im i j)^2)

theorem restA219_source_net_matrix :
    sourceOrdinaryNetInt (2 : Basis) (19 : Basis) (by decide) = restA219NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (2 : Basis) (19 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = restA219NetInt := by rw [restA219_source_net_literal]; rfl

theorem restA219_centered_square_lt :
    restA219CenteredSquareInt < restA219RadiusInt^2 := by decide +kernel

theorem restA219_centered_value :
    value restA219CenteredInt = value restA219NetInt -
      (9293/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [restA219CenteredInt,restA219CenterInt,value,raw,scale]
    ring
  · simp [restA219CenteredInt,restA219CenterInt,value,raw,scale,h]

theorem restA219_centered_norm :
    ‖value restA219NetInt -
      (9293/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3787/10^9 : ℝ) := by
  rw [← restA219_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((restA219CenteredInt.re i j)^2+(restA219CenteredInt.im i j)^2)) ≤
        restA219RadiusInt^2 := by
    simpa only [restA219CenteredSquareInt] using le_of_lt restA219_centered_square_lt
  have h := integer_operator_norm_bound restA219CenteredInt restA219RadiusInt
    (by norm_num [restA219RadiusInt,scale]) square
  convert h using 1
  norm_num [restA219RadiusInt,scale]

theorem restA219_qnet_centered_norm :
    ‖sourceOrdinaryQNet (2 : Basis) (19 : Basis) (by decide) -
      (9293/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3793/10^9 : ℝ) := by
  have source := source_ordinary_net_error (2 : Basis) (19 : Basis) (by decide)
  rw [restA219_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (2 : Basis) (19 : Basis) (by decide))
    (value restA219NetInt)
    ((9293/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (2 : Basis) (19 : Basis) (by decide) - value restA219NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse restA219_centered_norm).trans (by norm_num))

theorem restA219_qnet_floor :
    (5500/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (2 : Basis) (19 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (2 : Basis) (19 : Basis) (by decide))
    (ordinary_qnet_hermitian (2 : Basis) (19 : Basis) (by decide))
    (9293/10^9) (3793/10^9) restA219_qnet_centered_norm
  have compare : (5500/10^9 : ℝ) ≤ 9293/10^9-3793/10^9 := by norm_num
  have smaller : (5500/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (9293/10^9-3793/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
