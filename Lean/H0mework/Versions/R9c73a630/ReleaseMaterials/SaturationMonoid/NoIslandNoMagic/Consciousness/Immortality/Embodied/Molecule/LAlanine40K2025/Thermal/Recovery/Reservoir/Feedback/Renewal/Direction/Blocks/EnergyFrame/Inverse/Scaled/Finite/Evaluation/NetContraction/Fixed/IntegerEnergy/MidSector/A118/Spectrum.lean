import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidSector.A118.NetEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def midA118NetInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  fromTable midA118NetTable pairFin pairFin
def midA118CenterInt : Int := 11876*scale/10^9
def midA118RadiusInt : Int := 3872*scale/10^9
def midA118CenteredInt : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => midA118NetInt.re i j - (if i=j then midA118CenterInt else 0), midA118NetInt.im⟩
def midA118CenteredSquareInt : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    ((midA118CenteredInt.re i j)^2+(midA118CenteredInt.im i j)^2)

theorem midA118_source_net_matrix :
    sourceOrdinaryNetInt (1 : Basis) (18 : Basis) (by decide) = midA118NetInt := by
  calc
    _ = fromTable (toTable (sourceOrdinaryNetInt (1 : Basis) (18 : Basis) (by decide))
      pairFin pairFin) pairFin pairFin := (from_to_table _ _ _).symm
    _ = midA118NetInt := by rw [midA118_source_net_literal]; rfl

theorem midA118_centered_square_lt :
    midA118CenteredSquareInt < midA118RadiusInt^2 := by decide +kernel

theorem midA118_centered_value :
    value midA118CenteredInt = value midA118NetInt -
      (11876/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [midA118CenteredInt,midA118CenterInt,value,raw,scale]
    ring
  · simp [midA118CenteredInt,midA118CenterInt,value,raw,scale,h]

theorem midA118_centered_norm :
    ‖value midA118NetInt -
      (11876/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3872/10^9 : ℝ) := by
  rw [← midA118_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        ((midA118CenteredInt.re i j)^2+(midA118CenteredInt.im i j)^2)) ≤
        midA118RadiusInt^2 := by
    simpa only [midA118CenteredSquareInt] using le_of_lt midA118_centered_square_lt
  have h := integer_operator_norm_bound midA118CenteredInt midA118RadiusInt
    (by norm_num [midA118RadiusInt,scale]) square
  convert h using 1
  norm_num [midA118RadiusInt,scale]

theorem midA118_qnet_centered_norm :
    ‖sourceOrdinaryQNet (1 : Basis) (18 : Basis) (by decide) -
      (11876/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (3878/10^9 : ℝ) := by
  have source := source_ordinary_net_error (1 : Basis) (18 : Basis) (by decide)
  rw [midA118_source_net_matrix] at source
  have split := norm_sub_le_norm_sub_add_norm_sub
    (sourceOrdinaryQNet (1 : Basis) (18 : Basis) (by decide))
    (value midA118NetInt)
    ((11876/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
  have reverse :
      ‖sourceOrdinaryQNet (1 : Basis) (18 : Basis) (by decide) - value midA118NetInt‖ ≤
        (6/10^9 : ℝ) := by simpa only [norm_sub_rev] using source
  exact split.trans ((add_le_add reverse midA118_centered_norm).trans (by norm_num))

theorem midA118_qnet_floor :
    (7998/10^9 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet (1 : Basis) (18 : Basis) (by decide) := by
  have source := hermitian_lower_from_center
    (sourceOrdinaryQNet (1 : Basis) (18 : Basis) (by decide))
    (ordinary_qnet_hermitian (1 : Basis) (18 : Basis) (by decide))
    (11876/10^9) (3878/10^9) midA118_qnet_centered_norm
  have compare : (7998/10^9 : ℝ) ≤ 11876/10^9-3878/10^9 := by norm_num
  have smaller : (7998/10^9 : ℝ) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      (11876/10^9-3878/10^9 : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right compare (zero_le_one :
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤ 1)
  exact smaller.trans source

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
