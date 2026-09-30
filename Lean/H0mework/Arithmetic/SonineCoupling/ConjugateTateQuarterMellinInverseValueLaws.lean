import H0mework.Arithmetic.SonineCoupling.ConjugateTateQuarterMellinInverseValue

/-!
# Semilinear laws of the inverse quarter-Mellin value
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

theorem conjugateTateQuarterMellinInverseValue_add
    (z : ℂ)
    (left right : QuarterMellinL2Test
      (conjugateTateMellinParameter z)) :
  conjugateTateQuarterMellinInverseValue z (left + right) =
      conjugateTateQuarterMellinInverseValue z left +
        conjugateTateQuarterMellinInverseValue z right := by
  apply Subtype.ext
  change positiveTateInvolution
      (positiveMellinPointwiseConjugation (left.1 + right.1)) =
    positiveTateInvolution (positiveMellinPointwiseConjugation left.1) +
      positiveTateInvolution (positiveMellinPointwiseConjugation right.1)
  rw [map_add, map_add]

theorem conjugateTateQuarterMellinInverseValue_smul
    (z : ℂ) (scalar : ℂ)
    (value : QuarterMellinL2Test
      (conjugateTateMellinParameter z)) :
    conjugateTateQuarterMellinInverseValue z (scalar • value) =
      star scalar • conjugateTateQuarterMellinInverseValue z value := by
  apply Subtype.ext
  change positiveTateInvolution
      (positiveMellinPointwiseConjugation (scalar • value.1)) =
    star scalar •
      positiveTateInvolution (positiveMellinPointwiseConjugation value.1)
  rw [map_smulₛₗ, map_smul]
  rfl

end

end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
