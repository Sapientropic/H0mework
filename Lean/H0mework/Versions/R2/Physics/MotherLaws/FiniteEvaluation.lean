import H0mework.Versions.R2.Physics.MotherLaws.FinitePolynomial
import Mathlib.Topology.Algebra.MvPolynomial

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFiniteLaws

open MotherFamilyOccurrence MotherCoordinateCompletion

noncomputable section

def termEval {n m : ℕ} (term : Term n m) (input : Fin n → ℝ) (output : Fin m) : ℝ :=
  (term.coefficient output : ℝ) * ∏ coordinate : Fin n, input coordinate ^ term.exponent coordinate

def evalTerms {n m : ℕ} : List (Term n m) → (Fin n → ℝ) → Fin m → ℝ
  | [], _, _ => 0
  | term :: rest, input, output => termEval term input output + evalTerms rest input output

/-- The factory evaluates only its finite products, rational coefficients and finite sums. -/
def eval (n m : ℕ) (visit : MotherVisit) (input : Fin n → ℝ) : Fin m → ℝ :=
  evalTerms (terms n m visit) input

theorem termEval_polynomial {n m : ℕ} (term : Term n m) (input : Fin n → ℝ) (output : Fin m) :
    termEval term input output =
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) input (term.monomial output) := by
  rw [Term.monomial, MvPolynomial.eval₂_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rfl

theorem evalTerms_polynomial {n m : ℕ} (data : List (Term n m))
    (input : Fin n → ℝ) (output : Fin m) :
    evalTerms data input output =
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) input (polynomialOf data output) := by
  induction data with
  | nil => simp only [evalTerms, polynomialOf, List.map_nil, List.sum_nil, MvPolynomial.eval₂_zero]
  | cons term rest induction =>
      change termEval term input output + evalTerms rest input output =
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) input (term.monomial output + polynomialOf rest output)
      rw [MvPolynomial.eval₂_add, ← termEval_polynomial, ← induction]

theorem eval_polynomial (n m : ℕ) (visit : MotherVisit) (input : Fin n → ℝ) (output : Fin m) :
    eval n m visit input output =
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) input (polynomial n m visit output) :=
  evalTerms_polynomial _ input output

theorem eval_continuous (n m : ℕ) (visit : MotherVisit) : Continuous (eval n m visit) := by
  apply continuous_pi
  intro output
  simp_rw [eval_polynomial, MvPolynomial.eval₂_eq_eval_map]
  exact MvPolynomial.continuous_eval _

def finiteLaw (n m : ℕ) (visit : MotherVisit) : C((Fin n → ℝ), (Fin m → ℝ)) :=
  ⟨eval n m visit, eval_continuous n m visit⟩

/-- Evaluation forms a value in the existing source-coordinate completion. -/
def output (n m : ℕ) (visit : MotherVisit) (input : Completed n) : Completed m :=
  (realEquiv m).symm (eval n m visit (coordinates n input))

theorem output_coordinates (n m : ℕ) (visit : MotherVisit) (input : Completed n) :
    coordinates m (output n m visit input) = eval n m visit (coordinates n input) :=
  (realEquiv m).apply_symm_apply _

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFiniteLaws
