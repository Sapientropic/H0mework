import H0mework.Chemistry.LAlanineElectronicFrame.ProducerSourceGeneratedElectronicFramePolar
import H0mework.Chemistry.LAlanineElectronicFrame.DynamicsMatrixFrobeniusOperatorBound

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.ElectronicFrame.Producer

open Propagation.Interface
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

def heldMatrix : Matrix Basis Basis ℂ := initialDensityMatrix Source.currentElectronicSource
def scfBenchmark : Matrix Basis Basis ℂ := initialDensityMatrix Source.targetElectronicSource
def heldNumerator (i j : Basis) : Int := symmetricEntry Source.currentElectronicSource.d0Q i j
def scfNumerator (i j : Basis) : Int := symmetricEntry Source.targetElectronicSource.d0Q i j
def heldSquareSum : Int := ∑ i : Basis, ∑ j : Basis, heldNumerator i j ^ 2

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem heldSquareSum_exact : heldSquareSum = 95999999999993451236866761 := by decide

theorem held_entry (i j : Basis) : heldMatrix i j = (heldNumerator i j : ℂ) / 1000000000000 := rfl
theorem scf_entry (i j : Basis) : scfBenchmark i j = (scfNumerator i j : ℂ) / 1000000000000 := rfl

attribute [local irreducible] heldMatrix heldNumerator scfBenchmark scfNumerator

theorem held_squared_entry_sum :
    (∑ i : Basis, ∑ j : Basis, ‖heldMatrix i j‖ ^ 2) = (heldSquareSum : ℝ) / 10 ^ 24 := by
  simp only [heldSquareSum, Int.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [held_entry]
  norm_num [norm_div, Complex.norm_intCast, div_pow, sq_abs]

theorem heldMatrix_norm_le_ten : ‖heldMatrix‖ ≤ 10 := by
  apply MatrixNorm.l2_norm_le_of_sq_sum_le heldMatrix (by norm_num)
  rw [held_squared_entry_sum, heldSquareSum_exact]
  norm_num

end
end LAlanine40K2025.ElectronicFrame.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
