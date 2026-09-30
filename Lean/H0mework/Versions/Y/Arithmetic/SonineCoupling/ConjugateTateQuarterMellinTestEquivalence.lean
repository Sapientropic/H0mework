import H0mework.Versions.Y.Arithmetic.SonineCoupling.ConjugateTateQuarterMellinInverseValueLaws

/-!
# Conjugate--Tate equivalence of quarter-Mellin tests
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

noncomputable section

theorem conjugateTateQuarterMellinTest_leftInverse (z : ℂ) :
    Function.LeftInverse (conjugateTateQuarterMellinInverseValue z)
      (conjugateTateQuarterMellinTest z) := by
  intro value
  apply Subtype.ext
  rw [conjugateTateQuarterMellinInverseValue_coe]
  exact conjugateTateQuarterMellinTest_involutive_value z value

theorem conjugateTateQuarterMellinTest_rightInverse (z : ℂ) :
    Function.RightInverse (conjugateTateQuarterMellinInverseValue z)
      (conjugateTateQuarterMellinTest z) := by
  intro value
  apply Subtype.ext
  change positiveTateInvolution
      (positiveMellinPointwiseConjugation
        (conjugateTateQuarterMellinInverseValue z value).1) = value.1
  rw [conjugateTateQuarterMellinInverseValue_coe]
  change positiveTateInvolution
      (positiveMellinPointwiseConjugation
        (positiveTateInvolution
          (positiveMellinPointwiseConjugation value.1))) = value.1
  rw [positiveMellinPointwiseConjugation_tate_commutes,
    positiveMellinPointwiseConjugation_involutive,
    positiveTateInvolution_involutive]

def conjugateTateQuarterMellinTestEquiv (z : ℂ) :
    QuarterMellinL2Test z ≃ₛₗ[starRingEnd ℂ]
      QuarterMellinL2Test (conjugateTateMellinParameter z) where
  toFun := conjugateTateQuarterMellinTest z
  invFun := conjugateTateQuarterMellinInverseValue z
  left_inv := conjugateTateQuarterMellinTest_leftInverse z
  right_inv := conjugateTateQuarterMellinTest_rightInverse z
  map_add' := (conjugateTateQuarterMellinTest z).map_add
  map_smul' := (conjugateTateQuarterMellinTest z).map_smulₛₗ

end

end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
