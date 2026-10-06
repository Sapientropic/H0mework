import H0mework.Versions.AB.Chemistry.LAlanineReentry.SourceSourceBoundReentry

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Reentry.Producer

open Propagation.Interface
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

theorem hamiltonianNumerator_swap (i j : Basis) : Source.hamiltonianNumerator i j = Source.hamiltonianNumerator j i := by
  change JointNext.SourceReification.symmetricRead _ i j = JointNext.SourceReification.symmetricRead _ j i
  exact JointNext.SourceReification.symmetricRead_swap _ i j

theorem sourceHamiltonian_hermitian : Source.hamiltonian.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  change star ((Source.hamiltonianNumerator j i : ℂ) / 1000000000000) =
    (Source.hamiltonianNumerator i j : ℂ) / 1000000000000
  rw [hamiltonianNumerator_swap j i]
  simp

theorem targetReal_swap (i j : Basis) : Source.targetRealNumerator i j = Source.targetRealNumerator j i := by
  change JointNext.SourceReification.symmetricRead _ i j = JointNext.SourceReification.symmetricRead _ j i
  exact JointNext.SourceReification.symmetricRead_swap _ i j

theorem targetImag_swap (i j : Basis) : Source.targetImagNumerator i j = -Source.targetImagNumerator j i := by
  change JointNext.SourceReification.antisymmetricRead _ i j = -JointNext.SourceReification.antisymmetricRead _ j i
  exact JointNext.SourceReification.antisymmetricRead_swap _ i j

theorem targetRealized_hermitian : Source.targetRealized.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  change star (((Source.targetRealNumerator j i : ℂ) + Complex.I * (Source.targetImagNumerator j i : ℂ)) /
    1000000000000000) = ((Source.targetRealNumerator i j : ℂ) +
      Complex.I * (Source.targetImagNumerator i j : ℂ)) / 1000000000000000
  rw [targetReal_swap j i, targetImag_swap j i]
  simp

def crossDelta (i j : Basis) : Int := Source.crossNumerator i j - if i = j then 1000000000000000 else 0
theorem crossDelta_entry (i j : Basis) :
    (Source.crossMatrix - 1) i j = (crossDelta i j : ℂ) / 1000000000000000 := by
  by_cases same : i = j <;>
    simp [Source.crossMatrix, JointNext.Interface.JointStepReadout.crossMatrix, Source.stepReadout, crossDelta, same]
  ring

theorem actual_imaginary_coordinate : Source.targetImagNumerator 4 7 = 5034 := by decide +kernel

theorem targetRealized_not_real_only : ∃ i j, (Source.targetRealized i j).im ≠ 0 := by
  refine ⟨4, 7, ?_⟩
  change (((Source.targetRealNumerator 4 7 : ℂ) + Complex.I * (Source.targetImagNumerator 4 7 : ℂ)) /
    1000000000000000).im ≠ 0
  rw [actual_imaginary_coordinate]
  simp

end
end LAlanine40K2025.Reentry.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
