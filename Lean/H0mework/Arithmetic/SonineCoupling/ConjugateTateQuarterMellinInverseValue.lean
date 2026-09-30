import H0mework.Arithmetic.SonineCoupling.ConjugateTateParameterInvolution

/-!
# Inverse conjugate--Tate quarter-Mellin value

The target subtype is rebuilt directly.  Its L2 witness is unchanged and its
Mellin convergence witness is transported only through `J (J z) = z`.
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

def conjugateTateQuarterMellinInverseValue
    (z : ℂ)
    (value : QuarterMellinL2Test (conjugateTateMellinParameter z)) :
    QuarterMellinL2Test z :=
  ⟨(conjugateTateQuarterMellinTest
      (conjugateTateMellinParameter z) value).1,
    ⟨(conjugateTateQuarterMellinTest
        (conjugateTateMellinParameter z) value).2.1,
      by
        simpa only [conjugateTateMellinParameter_involutive] using
          (conjugateTateQuarterMellinTest
            (conjugateTateMellinParameter z) value).2.2⟩⟩

@[simp]
theorem conjugateTateQuarterMellinInverseValue_coe
    (z : ℂ)
    (value : QuarterMellinL2Test (conjugateTateMellinParameter z)) :
    (conjugateTateQuarterMellinInverseValue z value).1 =
      ((conjugateTateQuarterMellinTest
        (conjugateTateMellinParameter z)) value).1 :=
  rfl

end

end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
