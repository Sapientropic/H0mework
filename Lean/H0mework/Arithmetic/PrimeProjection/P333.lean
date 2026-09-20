import H0mework.Arithmetic.PrimeShadow.P332

/-!
# Proposition 333: the global Goldbach boundary as coefficient positivity

P332 gives the pointwise coefficient formula

`0 < G(n) ↔ n` has a two-prime additive decomposition.

This file lifts that to the even/global statement:

`∀ n ≥ 2, 0 < G(2*n)` is exactly ordinary Goldbach for even numbers at least
four, and hence exactly the half-sigma carrier statement already isolated in
P320/P330.

Boundary: this is an equivalent global formulation, not a proof of the global
statement.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace SaturationMonoid
namespace AffineRelaxation

/-- The global even-Goldbach statement expressed as positivity of the
prime-indicator convolution coefficient. -/
def EvenGoldbachCoefficientStatement : Prop :=
  ∀ n : ℕ, 2 ≤ n → 0 < goldbachConvolutionCoefficient (2 * n)

/-- THEOREM 1: the coefficient-positivity global statement is exactly the
ordinary even Goldbach statement. -/
theorem evenGoldbachCoefficientStatement_iff_evenGoldbach :
    EvenGoldbachCoefficientStatement ↔ EvenGoldbachStatement := by
  constructor
  · intro h n hn
    exact (goldbachConvolutionCoefficient_pos_iff (2 * n)).mp (h n hn)
  · intro h n hn
    exact (goldbachConvolutionCoefficient_pos_iff (2 * n)).mpr (h n hn)

/-- THEOREM 2: the half-sigma carrier global statement is exactly global
coefficient positivity. -/
theorem halfSigmaEvenGoldbach_iff_coefficientStatement :
    SigmaEvenGoldbachStatement (1 / 2 : ℝ) ↔
      EvenGoldbachCoefficientStatement := by
  exact halfSigmaEvenGoldbach_iff_evenGoldbach.trans
    evenGoldbachCoefficientStatement_iff_evenGoldbach.symm

/-- THEOREM 3: a proposed FTA-to-coefficient theorem is exactly as strong as
a proposed FTA-to-Goldbach theorem.  The coefficient surface is faithful; it
does not make the global theorem easier by definition. -/
theorem fta_to_coefficientStatement_iff_fta_to_goldbach :
    (PrimeMultiplicativeFactorizationStatement →
        EvenGoldbachCoefficientStatement) ↔
      (PrimeMultiplicativeFactorizationStatement →
        EvenGoldbachStatement) := by
  constructor
  · intro h hfta
    exact evenGoldbachCoefficientStatement_iff_evenGoldbach.mp (h hfta)
  · intro h hfta
    exact evenGoldbachCoefficientStatement_iff_evenGoldbach.mpr (h hfta)

/-- THEOREM 4: with an FTA certificate in hand, proving the coefficient
positivity statement is exactly proving ordinary even Goldbach. -/
theorem fta_bridge_reduces_coefficientStatement_to_goldbach
    (hfta : PrimeMultiplicativeFactorizationStatement) :
    (PrimeMultiplicativeFactorizationStatement →
        EvenGoldbachCoefficientStatement) ↔
      EvenGoldbachStatement := by
  constructor
  · intro h
    exact evenGoldbachCoefficientStatement_iff_evenGoldbach.mp (h hfta)
  · intro h _
    exact evenGoldbachCoefficientStatement_iff_evenGoldbach.mpr h

/-- Compact certificate for the coefficient-form global boundary. -/
structure P333GoldbachCoefficientGlobalBoundaryCertificate where
  coefficient_global_iff_goldbach :
    EvenGoldbachCoefficientStatement ↔ EvenGoldbachStatement
  half_sigma_even_iff_coefficient_global :
    SigmaEvenGoldbachStatement (1 / 2 : ℝ) ↔
      EvenGoldbachCoefficientStatement
  fta_to_coefficient_iff_fta_to_goldbach :
    (PrimeMultiplicativeFactorizationStatement →
        EvenGoldbachCoefficientStatement) ↔
      (PrimeMultiplicativeFactorizationStatement →
        EvenGoldbachStatement)
  fta_bridge_reduces_to_goldbach :
    PrimeMultiplicativeFactorizationStatement →
      ((PrimeMultiplicativeFactorizationStatement →
          EvenGoldbachCoefficientStatement) ↔
        EvenGoldbachStatement)

/-- THEOREM 5: the canonical coefficient-form global boundary certificate. -/
theorem p333GoldbachCoefficientGlobalBoundaryCertificate :
    P333GoldbachCoefficientGlobalBoundaryCertificate where
  coefficient_global_iff_goldbach :=
    evenGoldbachCoefficientStatement_iff_evenGoldbach
  half_sigma_even_iff_coefficient_global :=
    halfSigmaEvenGoldbach_iff_coefficientStatement
  fta_to_coefficient_iff_fta_to_goldbach :=
    fta_to_coefficientStatement_iff_fta_to_goldbach
  fta_bridge_reduces_to_goldbach :=
    fta_bridge_reduces_coefficientStatement_to_goldbach

end AffineRelaxation
end SaturationMonoid
