import H0mework.Versions.Y.Arithmetic.SonineCoupling.ConjugateTateQuarterMellinTestEquivalence

/-!
# Actual conjugate--Tate equivalence of Schwartz relations

The forward relation map is Fourier after Schwartz conjugation.  Its explicit
inverse is Schwartz conjugation after inverse Fourier.  Fourier inversion and
conjugation involutivity prove both inverse laws and the backward relation
square; no quotient equivalence is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual

open FourierTransform
open scoped SchwartzMap

noncomputable section

def schwartzTateConjugationInverseValue
    (test : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  schwartzConjugation (FourierTransform.fourierInv test)

theorem schwartzTateConjugationInverseValue_add
    (left right : SchwartzMap ℝ ℂ) :
    schwartzTateConjugationInverseValue (left + right) =
      schwartzTateConjugationInverseValue left +
        schwartzTateConjugationInverseValue right := by
  rw [schwartzTateConjugationInverseValue, fourierInv_add, map_add]
  rfl

theorem schwartzTateConjugationInverseValue_smul
    (scalar : ℂ) (test : SchwartzMap ℝ ℂ) :
    schwartzTateConjugationInverseValue (scalar • test) =
      star scalar • schwartzTateConjugationInverseValue test := by
  rw [schwartzTateConjugationInverseValue, fourierInv_smul,
    schwartzConjugation_smul]
  rfl

theorem schwartzTateConjugation_leftInverse :
    Function.LeftInverse schwartzTateConjugationInverseValue
      schwartzTateConjugation := by
  intro test
  change schwartzConjugation
      (FourierTransform.fourierInv
        (FourierTransform.fourier (schwartzConjugation test))) = test
  rw [fourierInv_fourier_eq, schwartzConjugation_involutive]

theorem schwartzTateConjugation_rightInverse :
    Function.RightInverse schwartzTateConjugationInverseValue
      schwartzTateConjugation := by
  intro test
  change FourierTransform.fourier (schwartzConjugation
      (schwartzConjugation (FourierTransform.fourierInv test))) = test
  rw [schwartzConjugation_involutive, fourier_fourierInv_eq]

/-- Actual semilinear equivalence of complete Schwartz relation carriers. -/
def schwartzTateConjugationEquiv :
    SchwartzMap ℝ ℂ ≃ₛₗ[starRingEnd ℂ] SchwartzMap ℝ ℂ where
  toFun := schwartzTateConjugation
  invFun := schwartzTateConjugationInverseValue
  left_inv := schwartzTateConjugation_leftInverse
  right_inv := schwartzTateConjugation_rightInverse
  map_add' := schwartzTateConjugation.map_add
  map_smul' := schwartzTateConjugation.map_smulₛₗ

theorem conjugateTateQuarterMellinRelation_forward
    (z : ℂ) (positive : 0 < z.re)
    (belowHalf : z.re < (1 / 2 : ℝ))
    (test : SchwartzMap ℝ ℂ) :
    conjugateTateQuarterMellinTestEquiv z
        (coPoissonQuarterMellinConvergentMap
          z positive belowHalf test) =
      coPoissonQuarterMellinConvergentMap
        (conjugateTateMellinParameter z)
        (conjugateTateMellinParameter_re_pos z belowHalf)
        (conjugateTateMellinParameter_re_lt_half z positive)
        (schwartzTateConjugationEquiv test) := by
  exact conjugateTateQuarterMellinTest_relation
    z positive belowHalf test

theorem conjugateTateQuarterMellinRelation_backward
    (z : ℂ) (positive : 0 < z.re)
    (belowHalf : z.re < (1 / 2 : ℝ))
    (test : SchwartzMap ℝ ℂ) :
    (conjugateTateQuarterMellinTestEquiv z).symm
        (coPoissonQuarterMellinConvergentMap
          (conjugateTateMellinParameter z)
          (conjugateTateMellinParameter_re_pos z belowHalf)
          (conjugateTateMellinParameter_re_lt_half z positive) test) =
      coPoissonQuarterMellinConvergentMap z positive belowHalf
        (schwartzTateConjugationEquiv.symm test) := by
  apply (conjugateTateQuarterMellinTestEquiv z).injective
  rw [(conjugateTateQuarterMellinTestEquiv z).apply_symm_apply,
    conjugateTateQuarterMellinRelation_forward,
    schwartzTateConjugationEquiv.apply_symm_apply]

end

end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
