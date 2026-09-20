import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import H0mework.Realization.FiniteCell.FrontierDeterminant

/-!
# Root-generated action determinant on a canonical perfect frontier

A positive canonical-frontier settlement already owns a bounded finite-free
candidate and its graded determinant line.  An actual endomorphism occurrence
on that candidate therefore has a basis-free reverse characteristic
polynomial in every generated degree.  The universal finite fold places even
degrees in the numerator and odd degrees in the denominator.

The mouth accepts one dependent occurrence carrying the exact root together
with the actual chain endomorphism.  It accepts no basis, matrix, freeness,
finite generation, determinant polynomial, quotient, analytic function or
settlement branch.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalFrontierActionDeterminant

open CategoryTheory
open CanonicalFiniteFrontierCompression
open CanonicalFiniteFrontierCompression.RootGeneratedCanonicalFiniteFrontierCompressionAt
open CanonicalFrontierDeterminant

noncomputable section

universe w

/-- The numerator/denominator carrier of an alternating determinant.  Keeping
the two integral polynomials separate avoids choosing a localization normal
form. -/
structure IntegralDeterminantFractionAt where
  numerator : Polynomial ℤ
  denominator : Polynomial ℤ

namespace IntegralDeterminantFractionAt

def one : IntegralDeterminantFractionAt := ⟨1, 1⟩

def multiplyEven (factor : Polynomial ℤ)
    (fraction : IntegralDeterminantFractionAt) :
    IntegralDeterminantFractionAt :=
  ⟨factor * fraction.numerator, fraction.denominator⟩

def multiplyOdd (factor : Polynomial ℤ)
    (fraction : IntegralDeterminantFractionAt) :
    IntegralDeterminantFractionAt :=
  ⟨fraction.numerator, factor * fraction.denominator⟩

end IntegralDeterminantFractionAt

/-- One same-occurrence chain action on the generated perfect candidate. -/
structure RootGeneratedCanonicalFrontierActionDeterminantAt
    {Root : Type w}
    {rootOccurrence : RootedAccountedUnfolding Root}
    {actualComplexOccurrence : RootedAccountedUnfolding
      (DerivedAdicCofiber.IntegralCochainComplex ℤ)}
    {compression : RootGeneratedCanonicalFiniteFrontierCompressionAt
      rootOccurrence actualComplexOccurrence}
    {settlement : ClassifiedAdequateFrontierAt compression}
    (determinantFace : RootGeneratedCanonicalFrontierDeterminantAt
      compression settlement)
    (dependentActionOccurrence : RootedAccountedUnfolding
      (Root × (determinantFace.candidate ⟶ determinantFace.candidate)))
    (projects : dependentActionOccurrence.map Prod.fst =
      determinantFace.root) : Type w where
  private mk ::

namespace RootGeneratedCanonicalFrontierActionDeterminantAt

variable {Root : Type w}
variable {rootOccurrence : RootedAccountedUnfolding Root}
variable {actualComplexOccurrence : RootedAccountedUnfolding
  (DerivedAdicCofiber.IntegralCochainComplex ℤ)}
variable {compression : RootGeneratedCanonicalFiniteFrontierCompressionAt
  rootOccurrence actualComplexOccurrence}
variable {settlement : ClassifiedAdequateFrontierAt compression}
variable {determinantFace : RootGeneratedCanonicalFrontierDeterminantAt
  compression settlement}
variable {dependentActionOccurrence : RootedAccountedUnfolding
  (Root × (determinantFace.candidate ⟶ determinantFace.candidate))}
variable {projects : dependentActionOccurrence.map Prod.fst =
  determinantFace.root}

def generate : RootGeneratedCanonicalFrontierActionDeterminantAt
    determinantFace dependentActionOccurrence projects :=
  ⟨⟩

def root
    (_face : RootGeneratedCanonicalFrontierActionDeterminantAt
      determinantFace dependentActionOccurrence projects) :=
  dependentActionOccurrence.map Prod.fst

def actionOccurrence
    (_face : RootGeneratedCanonicalFrontierActionDeterminantAt
      determinantFace dependentActionOccurrence projects) :=
  dependentActionOccurrence.map Prod.snd

def actualAction
    (face : RootGeneratedCanonicalFrontierActionDeterminantAt
      determinantFace dependentActionOccurrence projects) :
    determinantFace.candidate ⟶ determinantFace.candidate :=
  face.actionOccurrence.root

/-- Basis-free `det(1 - X F)` in one actual cochain degree. -/
noncomputable def degreeDeterminantPolynomial
    (face : RootGeneratedCanonicalFrontierActionDeterminantAt
      determinantFace dependentActionOccurrence projects)
    (degree : ℤ) : Polynomial ℤ := by
  letI : Module.Free ℤ (determinantFace.candidate.X degree) :=
    candidateTermFree settlement.frontier settlement.coverage degree
  letI : Module.Finite ℤ (determinantFace.candidate.X degree) :=
    candidateTermFinite settlement.frontier settlement.coverage degree
  exact (face.actualAction.f degree).hom.charpoly.reverse

@[simp] theorem degreeDeterminantPolynomial_coeff_zero
    (face : RootGeneratedCanonicalFrontierActionDeterminantAt
      determinantFace dependentActionOccurrence projects)
    (degree : ℤ) :
    (face.degreeDeterminantPolynomial degree).coeff 0 = 1 := by
  letI : Module.Free ℤ (determinantFace.candidate.X degree) :=
    candidateTermFree settlement.frontier settlement.coverage degree
  letI : Module.Finite ℤ (determinantFace.candidate.X degree) :=
    candidateTermFinite settlement.frontier settlement.coverage degree
  change ((face.actualAction.f degree).hom.charpoly.reverse).coeff 0 = 1
  rw [Polynomial.coeff_zero_reverse]
  exact LinearMap.charpoly_monic _ |>.leadingCoeff

private def foldDegree
    (face : RootGeneratedCanonicalFrontierActionDeterminantAt
      determinantFace dependentActionOccurrence projects)
    (degree : ℤ) (fraction : IntegralDeterminantFractionAt) :
    IntegralDeterminantFractionAt :=
  if degree % 2 = 0 then
    fraction.multiplyEven (face.degreeDeterminantPolynomial degree)
  else
    fraction.multiplyOdd (face.degreeDeterminantPolynomial degree)

/-- Alternating determinant fold over the exact degree support already used
by the determinant line. -/
noncomputable def determinantFraction
    (face : RootGeneratedCanonicalFrontierActionDeterminantAt
      determinantFace dependentActionOccurrence projects) :
    IntegralDeterminantFractionAt :=
  determinantFace.degrees.foldr face.foldDegree
    IntegralDeterminantFractionAt.one

theorem determinantFraction_coeff_zero
    (face : RootGeneratedCanonicalFrontierActionDeterminantAt
      determinantFace dependentActionOccurrence projects) :
    face.determinantFraction.numerator.coeff 0 = 1 ∧
      face.determinantFraction.denominator.coeff 0 = 1 := by
  unfold determinantFraction
  induction determinantFace.degrees with
  | nil => simp [IntegralDeterminantFractionAt.one]
  | cons degree tail inductionHypothesis =>
      simp only [List.foldr_cons]
      by_cases parity : degree % 2 = 0
      · rw [foldDegree, if_pos parity]
        simp only [IntegralDeterminantFractionAt.multiplyEven]
        constructor
        · calc
            (face.degreeDeterminantPolynomial degree *
                (List.foldr face.foldDegree
                  IntegralDeterminantFractionAt.one tail).numerator).coeff 0 =
                (face.degreeDeterminantPolynomial degree).coeff 0 *
                  (List.foldr face.foldDegree
                    IntegralDeterminantFractionAt.one tail).numerator.coeff 0 := by
              simp [Polynomial.coeff_zero_eq_eval_zero]
            _ = 1 := by rw [face.degreeDeterminantPolynomial_coeff_zero,
              inductionHypothesis.1, one_mul]
        · exact inductionHypothesis.2
      · rw [foldDegree, if_neg parity]
        simp only [IntegralDeterminantFractionAt.multiplyOdd]
        constructor
        · exact inductionHypothesis.1
        · calc
            (face.degreeDeterminantPolynomial degree *
                (List.foldr face.foldDegree
                  IntegralDeterminantFractionAt.one tail).denominator).coeff 0 =
                (face.degreeDeterminantPolynomial degree).coeff 0 *
                  (List.foldr face.foldDegree
                    IntegralDeterminantFractionAt.one tail).denominator.coeff 0 := by
              simp [Polynomial.coeff_zero_eq_eval_zero]
            _ = 1 := by rw [face.degreeDeterminantPolynomial_coeff_zero,
              inductionHypothesis.2, one_mul]

theorem preserves_same_root_action_and_determinant
    (face : RootGeneratedCanonicalFrontierActionDeterminantAt
      determinantFace dependentActionOccurrence projects) :
    face.root = determinantFace.root ∧
      face.actualAction = dependentActionOccurrence.root.2 ∧
      determinantFace.candidate =
        finitePerfectCandidate settlement.frontier settlement.coverage := by
  refine ⟨projects, ?_, rfl⟩
  simp [actualAction, actionOccurrence]

end RootGeneratedCanonicalFrontierActionDeterminantAt

end

end CanonicalFrontierActionDeterminant
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
