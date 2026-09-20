import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Fintype.Card
import H0mework.Foundation.Finite.FibreDisposition

/-!
# Finite effectivity-preserving coefficient kernel

An actual finite evaluator generates a polynomial over `Nat` by contributing
one monomial for every candidate.  The target coefficient is therefore the
number of actual candidates in the target fibre.  In particular, positivity
is equivalent to an inhabited fibre and zero is equivalent to an empty fibre;
there is no signed cancellation or loss of mass-one effectivity.

For a pair evaluator obtained by adding two coordinates, the generated
polynomial is exactly the square of the one-coordinate polynomial.  The
evaluator and target are the only inputs.  Positivity, a fibre witness, and a
zero residual are all downstream readouts.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedFiniteEffectiveCoefficient

open Polynomial
open SourceGeneratedEffectiveFibreDisposition

universe u

variable {Candidate : Type u} [Fintype Candidate]

/-- The exact finite generating polynomial.  Repeated evaluations retain
their multiplicity because the coefficient semiring is `Nat`. -/
noncomputable def countingPolynomial
    (evaluation : Candidate → Nat) : Polynomial Nat :=
  ∑ candidate : Candidate, X ^ evaluation candidate

/-- The generated target coefficient. -/
noncomputable def effectiveCoefficient
    (evaluation : Candidate → Nat) (target : Nat) : Nat :=
  (countingPolynomial evaluation).coeff target

theorem effectiveCoefficient_eq_card_filter
    (evaluation : Candidate → Nat) (target : Nat) :
    effectiveCoefficient evaluation target =
      (Finset.univ.filter fun candidate ↦
        evaluation candidate = target).card := by
  classical
  rw [effectiveCoefficient, countingPolynomial,
    Polynomial.finsetSum_coeff, Finset.card_eq_sum_ones,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro candidate _candidateMem
  by_cases evaluates : evaluation candidate = target
  · simp [Polynomial.coeff_X_pow, evaluates]
  · simp [Polynomial.coeff_X_pow, evaluates, Ne.symm evaluates]

theorem effectiveCoefficient_eq_card_fibre
    (evaluation : Candidate → Nat) (target : Nat) :
    effectiveCoefficient evaluation target =
      Fintype.card (Fibre evaluation target) := by
  classical
  rw [effectiveCoefficient_eq_card_filter]
  symm
  apply Fintype.card_of_subtype
    (Finset.univ.filter fun candidate ↦ evaluation candidate = target)
  intro candidate
  simp

theorem effectiveCoefficient_pos_iff_fibre
    (evaluation : Candidate → Nat) (target : Nat) :
    0 < effectiveCoefficient evaluation target ↔
      Nonempty (Fibre evaluation target) := by
  classical
  rw [effectiveCoefficient_eq_card_filter, Finset.card_pos]
  constructor
  · rintro ⟨candidate, candidateMem⟩
    exact ⟨⟨candidate, (Finset.mem_filter.mp candidateMem).2⟩⟩
  · rintro ⟨⟨candidate, evaluates⟩⟩
    exact ⟨candidate, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, evaluates⟩⟩

theorem effectiveCoefficient_eq_zero_iff_fibre_empty
    (evaluation : Candidate → Nat) (target : Nat) :
    effectiveCoefficient evaluation target = 0 ↔
      ¬ Nonempty (Fibre evaluation target) := by
  constructor
  · intro coefficientZero fibre
    have coefficientPositive :=
      (effectiveCoefficient_pos_iff_fibre evaluation target).2 fibre
    omega
  · intro fibreEmpty
    by_contra coefficientNonzero
    have coefficientPositive :
        0 < effectiveCoefficient evaluation target := by
      omega
    exact fibreEmpty
      ((effectiveCoefficient_pos_iff_fibre evaluation target).1
        coefficientPositive)

/-- Exact finite convolution identity. -/
theorem pairCountingPolynomial_eq_square
    (coordinate : Candidate → Nat) :
    countingPolynomial
        (fun pair : Candidate × Candidate ↦
          coordinate pair.1 + coordinate pair.2) =
      countingPolynomial coordinate * countingPolynomial coordinate := by
  classical
  simp only [countingPolynomial]
  rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
  simp [pow_add]

end SourceGeneratedFiniteEffectiveCoefficient
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
