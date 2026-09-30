import H0mework.Versions.Y.Arithmetic.MellinConductor.Source.LivingLawCanonicalCoPoissonHalfPositionGraph

/-!
# One-way half-position mapping-cone projection

The closed half-position relation graph generates its own graph cokernel.
The bounded first-coordinate morphism descends it canonically to the existing
Müntz graph cokernel and preserves every canonical source class.  No inverse
map or quotient equivalence is asserted.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual
namespace MuntzConductor
namespace HalfPositionSource

open SourceGeneratedFunctionalGraphCokernel
open scoped SchwartzMap

noncomputable section

abbrev HalfPositionMuntzGraphCokernel
    (z : ℂ) (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ)) :=
  ClosedRangeQuotient
    (C := quarterMellinHalfPositionSourceDomain z)
    (H := HalfPositionGraphCarrier)
    (Rel := SchwartzMap ℝ ℂ)
    (halfPositionGraphFeature z) (halfPositionGraphFunctional z)
    (coPoissonQuarterHalfPositionRelation z positive belowHalf)

def halfPositionMuntzGraphSourceMap
    (z : ℂ) (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ)) :=
  canonicalSourceMap
    (C := quarterMellinHalfPositionSourceDomain z)
    (H := HalfPositionGraphCarrier)
    (Rel := SchwartzMap ℝ ℂ)
    (halfPositionGraphFeature z) (halfPositionGraphFunctional z)
    (coPoissonQuarterHalfPositionRelation z positive belowHalf)

def halfPositionMuntzGraphProjection
    (z : ℂ) (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ)) :=
  (halfPositionRelationGraphSourceMorphism z positive belowHalf).quotientMap

@[simp] theorem halfPositionMuntzGraphProjection_source_readback
    (z : ℂ) (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (value : quarterMellinHalfPositionSourceDomain z) :
    halfPositionMuntzGraphProjection z positive belowHalf
        (halfPositionMuntzGraphSourceMap z positive belowHalf value) =
      coPoissonMuntzGraphSourceMap z positive belowHalf value.1 := by
  exact (halfPositionRelationGraphSourceMorphism
    z positive belowHalf).quotientMap_source_readback value

end
end HalfPositionSource
end MuntzConductor
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
