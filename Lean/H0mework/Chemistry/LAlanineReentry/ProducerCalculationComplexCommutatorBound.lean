import H0mework.Chemistry.LAlanineReentry.ProducerNormData
import H0mework.Chemistry.LAlanineReentry.ProducerCalculationComplexCommutatorFormula
import H0mework.Chemistry.LAlanineReentry.ProducerCalculationCommutatorChannelExact

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Reentry.Producer

open Propagation.Interface
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

theorem actual_commutator_entry (i j : Basis) :
    (Source.hamiltonian * Source.currentRealized - Source.currentRealized * Source.hamiltonian) i j =
      ((commutatorRealNumerator i j : ℂ) + Complex.I * (commutatorImagNumerator i j : ℂ)) / 10 ^ 27 := by
  have current : Source.currentRealized = Matrix.of (fun i j =>
      ((Source.currentRealNumerator i j : ℂ) + Complex.I * (Source.currentImagNumerator i j : ℂ)) /
        1000000000000000) := by
    ext i j
    exact Source.currentRealized_channels i j
  rw [current]
  have formula := Arithmetic.scaled_commutator_entry Source.hamiltonianNumerator
    Source.currentRealNumerator Source.currentImagNumerator
    (1000000000000 : ℂ) (1000000000000000 : ℂ) i j
  have denominator : (1000000000000 : ℂ) * 1000000000000000 = 10 ^ 27 := by norm_num
  rw [denominator] at formula
  exact formula

theorem actual_commutator_entry_bound (i j : Basis) :
    ‖(Source.hamiltonian * Source.currentRealized - Source.currentRealized * Source.hamiltonian) i j‖ ≤
      ((commutatorRealNumerator i j).natAbs + (commutatorImagNumerator i j).natAbs : ℝ) / 10 ^ 27 := by
  rw [actual_commutator_entry, norm_div]
  have normTen : ‖(10 : ℂ)‖ = (10 : ℝ) := by norm_num
  rw [norm_pow, normTen]
  exact div_le_div_of_nonneg_right (c := (10 : ℝ) ^ 27)
    (Arithmetic.complex_integer_norm_le (commutatorRealNumerator i j) (commutatorImagNumerator i j))
    (by positivity)

set_option maxRecDepth 4096 in
private theorem commutator_sum_account : (∑ i : Basis, ∑ j : Basis,
    ((commutatorRealNumerator i j).natAbs + (commutatorImagNumerator i j).natAbs : ℝ) / 10 ^ 27) =
    (commutatorRealMagnitude : ℝ) / 10 ^ 27 + (commutatorImagMagnitude : ℝ) / 10 ^ 27 := by
  simp only [commutatorRealMagnitude, commutatorImagMagnitude, Nat.cast_sum,
    Finset.sum_div, Finset.sum_add_distrib, add_div]

set_option maxRecDepth 4096 in
theorem actual_commutator_norm_le :
    ‖Source.hamiltonian * Source.currentRealized - Source.currentRealized * Source.hamiltonian‖ ≤
      (commutatorRealMagnitude : ℝ) / 10 ^ 27 + (commutatorImagMagnitude : ℝ) / 10 ^ 27 := by
  have bound := Propagation.Dynamics.NativeDuration.matrixOperator_norm_le_entrySum
    (Source.hamiltonian * Source.currentRealized - Source.currentRealized * Source.hamiltonian)
  change ‖Source.hamiltonian * Source.currentRealized - Source.currentRealized * Source.hamiltonian‖ ≤ _ at bound
  have summed : (∑ i : Basis, ∑ j : Basis,
      ‖(Source.hamiltonian * Source.currentRealized - Source.currentRealized * Source.hamiltonian) i j‖) ≤
      ∑ i : Basis, ∑ j : Basis,
        ((commutatorRealNumerator i j).natAbs + (commutatorImagNumerator i j).natAbs : ℝ) / 10 ^ 27 :=
    Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => actual_commutator_entry_bound i j))
  exact bound.trans (summed.trans_eq commutator_sum_account)

theorem actual_commutator_bound :
    ‖Source.hamiltonian * Source.currentRealized - Source.currentRealized * Source.hamiltonian‖ <
      (863 : ℝ) / 10 ^ 9 := by
  have real := congrArg (fun n : Nat => (n : ℝ) / 10 ^ 27) commutatorRealMagnitude_exact
  have imaginary := congrArg (fun n : Nat => (n : ℝ) / 10 ^ 27) commutatorImagMagnitude_exact
  have paired := congrArg₂ (fun x y : ℝ => x + y) real imaginary
  exact actual_commutator_norm_le.trans_lt (paired.trans_lt (by norm_num))

end
end LAlanine40K2025.Reentry.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
