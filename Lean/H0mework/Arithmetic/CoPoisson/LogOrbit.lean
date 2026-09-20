import H0mework.Arithmetic.Tempered.VariableCoPoisson

/-!
# Narrow co-Poisson logarithmic orbit core

This source-only module defines the logarithmic orbit and its Fourier
reflection law.  It deliberately does not import contact, whole-`L²`, radial,
fixedness, or witness modules.
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

open Complex FourierTransform
open ClozelEndpointSourceEffect
open scoped SchwartzMap

noncomputable section

def coPoissonLogOrbitMap :
    SchwartzMap ℝ ℂ →ₗ[ℂ] (ℝ → ℂ) where
  toFun test x := coPoissonOrbitMap test ⟨Real.exp x, Real.exp_pos x⟩
  map_add' left right := by
    funext x
    exact congrFun (map_add coPoissonOrbitMap left right) _
  map_smul' coefficient test := by
    funext x
    exact congrFun (map_smul coPoissonOrbitMap coefficient test) _

theorem coPoissonLogOrbitMap_fourier_reflection
    (test : SchwartzMap ℝ ℂ) (x : ℝ) :
    coPoissonLogOrbitMap (FourierTransform.fourier test) (-x) =
      coPoissonLogOrbitMap test x := by
  have source := coPoissonOrbitMap_tate test
    ⟨Real.exp x, Real.exp_pos x⟩
  simpa [coPoissonLogOrbitMap, Real.exp_neg] using source.symm

end


end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
