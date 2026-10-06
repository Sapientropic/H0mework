import H0mework.Versions.AB.Chemistry.LAlanineJointNext.SourceSourceBoundJointStep

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.JointNext.Producer

open Propagation.Interface
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

theorem hamiltonianNumerator_swap (i j : Basis) : Source.hamiltonianNumerator i j = Source.hamiltonianNumerator j i := by
  change SourceReification.symmetricRead _ i j = SourceReification.symmetricRead _ j i
  exact SourceReification.symmetricRead_swap _ i j

theorem sourceHamiltonian_hermitian : Source.hamiltonian.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  change star ((Source.hamiltonianNumerator j i : ℂ) / 1000000000000) =
    (Source.hamiltonianNumerator i j : ℂ) / 1000000000000
  rw [hamiltonianNumerator_swap j i]
  simp

theorem targetReal_swap (i j : Basis) : Source.targetRealNumerator i j = Source.targetRealNumerator j i := by
  change SourceReification.symmetricRead _ i j = SourceReification.symmetricRead _ j i
  exact SourceReification.symmetricRead_swap _ i j

theorem targetImag_swap (i j : Basis) : Source.targetImagNumerator i j = -Source.targetImagNumerator j i := by
  change SourceReification.antisymmetricRead _ i j = -SourceReification.antisymmetricRead _ j i
  exact SourceReification.antisymmetricRead_swap _ i j

theorem targetRealized_hermitian : Source.targetRealized.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  change star (((Source.targetRealNumerator j i : ℂ) + Complex.I * (Source.targetImagNumerator j i : ℂ)) /
    1000000000000000) = ((Source.targetRealNumerator i j : ℂ) +
      Complex.I * (Source.targetImagNumerator i j : ℂ)) / 1000000000000000
  rw [targetReal_swap j i, targetImag_swap j i]
  simp

def crossDelta (i j : Basis) : Int := Source.crossNumerator i j - if i = j then 1000000000000000 else 0
def crossMagnitude : Nat := ∑ i : Basis, ∑ j : Basis, (crossDelta i j).natAbs

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem crossMagnitude_exact : crossMagnitude = 1052822 := by decide +kernel

theorem crossDelta_entry (i j : Basis) :
    (Source.crossMatrix - 1) i j = (crossDelta i j : ℂ) / 1000000000000000 := by
  by_cases same : i = j <;>
    simp [Source.crossMatrix, Interface.JointStepReadout.crossMatrix, Source.stepReadout, crossDelta, same]
  ring

theorem sourceCross_norm : ‖Source.crossMatrix - 1‖ ≤ (1052822 : ℝ) / 1000000000000000 := by
  have bound := Propagation.Dynamics.NativeDuration.matrixOperator_norm_le_entrySum (Source.crossMatrix - 1)
  change ‖Source.crossMatrix - 1‖ ≤ _ at bound
  have entries : (∑ i : Basis, ∑ j : Basis, ‖(Source.crossMatrix - 1) i j‖) =
      (crossMagnitude : ℝ) / 1000000000000000 := by
    simp only [crossMagnitude, Nat.cast_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [crossDelta_entry]
    norm_num [norm_div, Complex.norm_intCast, Nat.cast_natAbs]
  rw [entries, crossMagnitude_exact] at bound
  exact bound

theorem sourceCross_close : ‖Source.crossMatrix - 1‖ < 1 := sourceCross_norm.trans_lt (by norm_num)

theorem actual_imaginary_coordinate : Source.targetImagNumerator 4 7 = 2517 := by decide +kernel

theorem targetRealized_not_real_only : ∃ i j, (Source.targetRealized i j).im ≠ 0 := by
  refine ⟨4, 7, ?_⟩
  change (((Source.targetRealNumerator 4 7 : ℂ) + Complex.I * (Source.targetImagNumerator 4 7 : ℂ)) /
    1000000000000000).im ≠ 0
  rw [actual_imaginary_coordinate]
  simp

end
end LAlanine40K2025.JointNext.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
