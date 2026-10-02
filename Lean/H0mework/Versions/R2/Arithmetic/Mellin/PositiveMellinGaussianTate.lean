import H0mework.Versions.R2.Arithmetic.Mellin.GaussianRemainderKernel
import H0mework.Arithmetic.Mellin.TateInvolution

/-!
# Gaussian relation in the narrow positive Tate involution

The scalar Gaussian remainder is fixed by the function-level Tate involution.
No convergent-carrier, q-rich, zero, endpoint, or separator module is needed.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann

open Complex

noncomputable section

theorem positiveTateInvolution_clozelRelation
    (owner : GlobalGermOwner) :
    positiveTateInvolution
        (fun t : PositiveMellinReal =>
          generatedClozelGaussianRemainderKernel owner t.1) =
      (fun t : PositiveMellinReal =>
        generatedClozelGaussianRemainderKernel owner t.1) := by
  funext t
  change (t.1 : ℂ) ^ (-(1 / 2 : ℂ)) *
      generatedClozelGaussianRemainderKernel owner t.1⁻¹ =
    generatedClozelGaussianRemainderKernel owner t.1
  simpa only [one_div] using
    (generatedClozelGaussianRemainderKernel_selfReciprocal
      owner t.1 t.2).symm

end

end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
