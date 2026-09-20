import H0mework.Physics.MotherLaws.FiniteSource
import Mathlib.Algebra.MvPolynomial.Eval

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFiniteLaws

open MotherFamilyOccurrence Stage9C.Revision

noncomputable section

def Term.monomial {n m : ℕ} (term : Term n m) (output : Fin m) : MvPolynomial (Fin n) ℚ :=
  MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm term.exponent) (term.coefficient output)

def polynomialOf {n m : ℕ} (data : List (Term n m)) (output : Fin m) : MvPolynomial (Fin n) ℚ :=
  (data.map (fun term => term.monomial output)).sum

def polynomial (n m : ℕ) (visit : MotherVisit) : Fin m → MvPolynomial (Fin n) ℚ :=
  polynomialOf (terms n m visit)

theorem every_polynomial_expression {n m : ℕ} (target : Fin m → MvPolynomial (Fin n) ℚ) :
    ∃ data : List (Term n m), polynomialOf data = target := by
  classical
  let support : Finset (Fin n →₀ ℕ) := Finset.univ.biUnion (fun output => (target output).support)
  let term : (Fin n →₀ ℕ) → Term n m := fun exponent =>
    ⟨fun input => exponent input, fun output => MvPolynomial.coeff exponent (target output)⟩
  refine ⟨support.toList.map term, ?_⟩
  funext output
  have restored (exponent : Fin n →₀ ℕ) :
      (term exponent).monomial output = MvPolynomial.monomial exponent (MvPolynomial.coeff exponent (target output)) := by
    unfold term Term.monomial
    rw [show Finsupp.equivFunOnFinite.symm (fun input => exponent input) = exponent from
      Finsupp.equivFunOnFinite.symm_apply_apply exponent]
  change ((support.toList.map term).map (fun term => term.monomial output)).sum = target output
  rw [List.map_map]
  simp_rw [Function.comp_def, restored]
  rw [Finset.sum_map_toList]
  have included : (target output).support ⊆ support := by
    intro exponent member
    exact Finset.mem_biUnion.mpr ⟨output, Finset.mem_univ _, member⟩
  calc
    _ = ∑ exponent ∈ (target output).support,
        MvPolynomial.monomial exponent (MvPolynomial.coeff exponent (target output)) := by
      symm
      apply Finset.sum_subset included
      intro exponent _ absent
      rw [MvPolynomial.notMem_support_iff.mp absent, MvPolynomial.monomial_zero]
    _ = target output := MvPolynomial.support_sum_monomial_coeff _

/-- The target polynomial family occurs only in this coverage conclusion. -/
theorem every_polynomial {n m : ℕ} (target : Fin m → MvPolynomial (Fin n) ℚ) :
    ∃ code, polynomial n m (SpinPair.visit (10 + code)) = target := by
  obtain ⟨data, expressed⟩ := every_polynomial_expression target
  obtain ⟨code, generated⟩ := every_terms data
  exact ⟨code, (congrArg polynomialOf generated).trans expressed⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFiniteLaws
