import H0mework.Arithmetic.PrimeProjection.P333

/-!
# Proposition 334: arbitrary-sigma rate/headroom dual coordinates

P331 specialized the closed atomic rate formula to the self-dual point
`sigma = 1/2`.  P332/P333 then exposed the direct Goldbach coefficient
frontend at that point.

This file pulls the coordinate theorem back to the full nondegenerate interval
`0 < sigma < 1`.

For any such `sigma`:

* a sigma-atomic rate has the closed form `1 - (1 - sigma)^p`;
* its headroom is `(1 - sigma)^p`;
* the atomic position map is faithful in the prime exponent;
* the rate/satOr Goldbach face, the headroom-multiplication Goldbach face, and
  the finite prime-indicator coefficient frontend are all the same pointwise
  predicate.

Boundary: this is a coordinate-faithfulness and frontend-equivalence theorem.
It does not prove the global Goldbach statement, RH, or any physical parameter
claim.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace SaturationMonoid
namespace AffineRelaxation

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ## Pointwise dual-front-end equivalences -/

/-- THEOREM 1: on the nondegenerate sigma interval, the rate/satOr Goldbach
face and the headroom-multiplication Goldbach face are the same pointwise
predicate. -/
theorem sigmaGoldbachDecomposition_iff_headroomPrimeTwoFactorization_of_mem_Ioo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1) {n : ℕ} :
    SigmaGoldbachDecomposition σ n ↔
      HeadroomPrimeTwoFactorization σ n := by
  exact
    (sigmaGoldbachDecomposition_iff_goldbach_of_mem_Ioo
      (σ := σ) hσ0 hσ1 (n := n)).trans
      (headroomPrimeTwoFactorization_iff_goldbach_of_mem_Ioo
        (σ := σ) hσ0 hσ1 (n := n)).symm

/-- THEOREM 2: on the nondegenerate sigma interval, the headroom
length-two factorization frontend is exactly positivity of the direct
prime-indicator convolution coefficient. -/
theorem headroomPrimeTwoFactorization_iff_convolutionCoefficient_pos_of_mem_Ioo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1) {n : ℕ} :
    HeadroomPrimeTwoFactorization σ n ↔
      0 < goldbachConvolutionCoefficient n := by
  exact
    (headroomPrimeTwoFactorization_iff_goldbach_of_mem_Ioo
      (σ := σ) hσ0 hσ1 (n := n)).trans
      (goldbachConvolutionCoefficient_pos_iff n).symm

/-- THEOREM 3: on the nondegenerate sigma interval, the rate/satOr Goldbach
frontend is exactly positivity of the same direct convolution coefficient. -/
theorem sigmaGoldbachDecomposition_iff_convolutionCoefficient_pos_of_mem_Ioo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1) {n : ℕ} :
    SigmaGoldbachDecomposition σ n ↔
      0 < goldbachConvolutionCoefficient n := by
  exact
    (sigmaGoldbachDecomposition_iff_goldbach_of_mem_Ioo
      (σ := σ) hσ0 hσ1 (n := n)).trans
      (goldbachConvolutionCoefficient_pos_iff n).symm

/-- THEOREM 4: the arbitrary-sigma even-rate statement is exactly the global
coefficient-positivity statement. -/
theorem sigmaEvenGoldbach_iff_coefficientStatement_of_mem_Ioo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    SigmaEvenGoldbachStatement σ ↔
      EvenGoldbachCoefficientStatement := by
  exact
    (sigmaEvenGoldbach_iff_evenGoldbach_of_mem_Ioo
      (σ := σ) hσ0 hσ1).trans
      evenGoldbachCoefficientStatement_iff_evenGoldbach.symm

/-- THEOREM 5: the arbitrary-sigma even-headroom statement is exactly the
global coefficient-positivity statement. -/
theorem headroomEvenGoldbach_iff_coefficientStatement_of_mem_Ioo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    (∀ n : ℕ, 2 ≤ n -> HeadroomPrimeTwoFactorization σ (2 * n)) ↔
      EvenGoldbachCoefficientStatement := by
  exact
    (headroomEvenLengthTwo_iff_evenGoldbach_of_mem_Ioo
      (σ := σ) hσ0 hσ1).trans
      evenGoldbachCoefficientStatement_iff_evenGoldbach.symm

/-! ## Packaged arbitrary-sigma coordinate certificate -/

/-- A compact certificate that the full nondegenerate sigma interval carries
the same closed rate/headroom coordinates and the same pointwise Goldbach
frontends.

The coefficient fields are deliberately pointwise/global-equivalence fields;
they do not assert that the coefficient is positive for all even inputs. -/
structure P334SigmaRateHeadroomDualCertificate
    (σ : K) (hσ0 : 0 < σ) (hσ1 : σ < 1) where
  rate_closed_form :
    ∀ p : PrimeExponent,
      sigmaAtomicClosedPosition σ p = 1 - (1 - σ) ^ p.1
  iterated_rate_position :
    ∀ p : PrimeExponent,
      sigmaAtomicClosedPosition σ p = iteratedRate σ p.1
  headroom_closed_form :
    ∀ p : PrimeExponent,
      1 - sigmaAtomicClosedPosition σ p = (1 - σ) ^ p.1
  tagged_support_value_closed_form :
    ∀ p : PrimeExponent,
      ((primeToSigmaAtomicRateSupport σ (ne_of_lt hσ1) p).1.1 : K) =
        sigmaAtomicClosedPosition σ p
  atomic_position_faithful :
    Function.Injective (sigmaAtomicClosedPosition σ)
  atomic_position_eq_iff :
    ∀ p q : PrimeExponent,
      sigmaAtomicClosedPosition σ p = sigmaAtomicClosedPosition σ q ↔
        p = q
  rate_headroom_pointwise :
    ∀ n : ℕ,
      SigmaGoldbachDecomposition σ n ↔
        HeadroomPrimeTwoFactorization σ n
  headroom_coefficient_pointwise :
    ∀ n : ℕ,
      HeadroomPrimeTwoFactorization σ n ↔
        0 < goldbachConvolutionCoefficient n
  rate_coefficient_pointwise :
    ∀ n : ℕ,
      SigmaGoldbachDecomposition σ n ↔
        0 < goldbachConvolutionCoefficient n
  rate_even_global :
    SigmaEvenGoldbachStatement σ ↔ EvenGoldbachCoefficientStatement
  headroom_even_global :
    (∀ n : ℕ, 2 ≤ n -> HeadroomPrimeTwoFactorization σ (2 * n)) ↔
      EvenGoldbachCoefficientStatement

/-- THEOREM 6: the canonical arbitrary-sigma rate/headroom dual-coordinate
certificate. -/
theorem p334SigmaRateHeadroomDualCertificate
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    P334SigmaRateHeadroomDualCertificate σ hσ0 hσ1 where
  rate_closed_form := by
    intro p
    rfl
  iterated_rate_position := by
    intro p
    exact sigmaAtomicClosedPosition_eq_iteratedRate σ p
  headroom_closed_form := by
    intro p
    exact keep_sigmaAtomicClosedPosition σ p
  tagged_support_value_closed_form := by
    intro p
    exact primeToSigmaAtomicRateSupport_val_closedForm σ (ne_of_lt hσ1) p
  atomic_position_faithful :=
    sigmaAtomicClosedPosition_injective_of_mem_Ioo hσ0 hσ1
  atomic_position_eq_iff := by
    intro p q
    exact sigmaAtomicClosedPosition_eq_iff_of_mem_Ioo hσ0 hσ1
  rate_headroom_pointwise := by
    intro n
    exact sigmaGoldbachDecomposition_iff_headroomPrimeTwoFactorization_of_mem_Ioo
      (σ := σ) hσ0 hσ1 (n := n)
  headroom_coefficient_pointwise := by
    intro n
    exact headroomPrimeTwoFactorization_iff_convolutionCoefficient_pos_of_mem_Ioo
      (σ := σ) hσ0 hσ1 (n := n)
  rate_coefficient_pointwise := by
    intro n
    exact sigmaGoldbachDecomposition_iff_convolutionCoefficient_pos_of_mem_Ioo
      (σ := σ) hσ0 hσ1 (n := n)
  rate_even_global :=
    sigmaEvenGoldbach_iff_coefficientStatement_of_mem_Ioo hσ0 hσ1
  headroom_even_global :=
    headroomEvenGoldbach_iff_coefficientStatement_of_mem_Ioo hσ0 hσ1

end AffineRelaxation
end SaturationMonoid
