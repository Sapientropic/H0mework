import H0mework.Arithmetic.PoleOrbit.OriginMappingCone
import H0mework.Arithmetic.MuntzAction.CoPoissonTranslationCarrier

/-!
# Complete all-place origin orbit carrier

The old all-place carrier retained only the arithmetic counterterm at scale
zero.  The source actually generates its complete co-Poisson log orbit.  This
file restores that orbit as the sibling of the quarter-Mellin state and shows
that the old scalar carrier is exactly its zero-coordinate projection.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace AllPlaceOriginDefect
namespace Orbit

open ClozelEndpointSourceEffect
open ClozelGeneralizedDual
open scoped SchwartzMap

noncomputable section

/-- Source map into the literal complete co-Poisson orbit range. -/
def coPoissonLogOrbitSourceMap :
    SchwartzMap ℝ ℂ →ₗ[ℂ] CoPoissonLogTranslationCarrier :=
  LinearMap.codRestrict CoPoissonLogTranslationCarrier
    coPoissonLogOrbitMap (fun test => ⟨test, rfl⟩)

abbrev AllPlaceOriginOrbitJointCarrier (z : ℂ) :=
  QuarterMellinL2Test z × CoPoissonLogTranslationCarrier

/-- One source test writes both its quarter-Mellin relation state and the
complete arithmetic/co-Poisson orbit that produced the old counterterm. -/
def allPlaceOriginOrbitRelationMap
    (z : ℂ) (positive : 0 < z.re)
    (belowHalf : z.re < (1 / 2 : ℝ)) :
    SchwartzMap ℝ ℂ →ₗ[ℂ] AllPlaceOriginOrbitJointCarrier z :=
  (coPoissonQuarterMellinConvergentMap z positive belowHalf).prod
    coPoissonLogOrbitSourceMap

def quarterLogOrbitRead (z : ℂ) :
    QuarterMellinL2Test z →ₗ[ℂ] (ℝ → ℂ) where
  toFun value := positiveMellinLogQuarterTransform value.1
  map_add' left right := by
    exact map_add positiveMellinLogQuarterTransform left.1 right.1
  map_smul' coefficient value := by
    exact map_smul positiveMellinLogQuarterTransform coefficient value.1

/-- Full-coordinate defect.  The factor `x/2` is the already generated
quarter-Mellin rechart, not a new comparison scalar. -/
def allPlaceOriginOrbitDefect (z : ℂ) :
    AllPlaceOriginOrbitJointCarrier z →ₗ[ℂ] (ℝ → ℂ) where
  toFun value x := quarterLogOrbitRead z value.1 x - value.2.1 (x / 2)
  map_add' left right := by
    funext x
    change quarterLogOrbitRead z (left.1 + right.1) x -
        (left.2.1 + right.2.1) (x / 2) = _
    rw [map_add]
    simp only [Pi.add_apply]
    ring
  map_smul' coefficient value := by
    funext x
    change quarterLogOrbitRead z (coefficient • value.1) x -
        (coefficient • value.2.1) (x / 2) = _
    rw [map_smul]
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring

/-- The complete relation writes zero at every scale coordinate, not only
at the old origin scalar. -/
theorem allPlaceOriginOrbitDefect_relation_eq_zero
    (z : ℂ) (positive : 0 < z.re)
    (belowHalf : z.re < (1 / 2 : ℝ))
    (test : SchwartzMap ℝ ℂ) :
    allPlaceOriginOrbitDefect z
        (allPlaceOriginOrbitRelationMap z positive belowHalf test) = 0 := by
  funext x
  change positiveMellinLogQuarterTransform
        (coPoissonQuarterMellinConvergentMap
          z positive belowHalf test).1 x -
      coPoissonLogOrbitMap test (x / 2) = 0
  rw [coPoissonQuarterMellinConvergentMap_value,
    positiveMellinLogQuarterTransform_coPoissonQuarterMellinMap,
    sub_self]

/-- Evaluation at scale zero is the lawful projection to the old scalar
joint carrier. -/
def allPlaceOriginOrbitEvaluationZero (z : ℂ) :
    AllPlaceOriginOrbitJointCarrier z →ₗ[ℂ]
      AllPlaceOriginJointCarrier z where
  toFun value := (value.1, coPoissonCarrierEvaluationZero value.2)
  map_add' left right := by
    apply Prod.ext <;> rfl
  map_smul' coefficient value := by
    apply Prod.ext <;> rfl

/-- On a source relation, the zero-coordinate projection is literally the
existing owner-generated all-place relation map. -/
theorem allPlaceOriginOrbitEvaluationZero_relation
    (owner : GlobalGermOwner)
    (z : ℂ) (positive : 0 < z.re)
    (belowHalf : z.re < (1 / 2 : ℝ))
    (test : SchwartzMap ℝ ℂ) :
    allPlaceOriginOrbitEvaluationZero z
        (allPlaceOriginOrbitRelationMap z positive belowHalf test) =
      allPlaceOriginRelationMap owner z positive belowHalf test := by
  apply Prod.ext
  · rfl
  · change coPoissonLogOrbitMap test 0 =
      ownerArithmeticCounterterm owner test
    rw [coPoissonLogOrbitMap_zero,
      ownerArithmeticCounterterm_eq_remainder]

/-- The old repaired defect is exactly the zero-coordinate restriction of
the complete orbit defect. -/
theorem allPlaceOriginDefect_eq_orbitDefect_zero
    (owner : GlobalGermOwner) (z : ℂ)
    (value : AllPlaceOriginOrbitJointCarrier z) :
    allPlaceOriginDefect owner z
        (allPlaceOriginOrbitEvaluationZero z value) =
      allPlaceOriginOrbitDefect z value 0 := by
  change quarterLogOriginRead z value.1 - value.2.1 0 =
    positiveMellinLogQuarterTransform value.1.1 0 - value.2.1 (0 / 2)
  norm_num [quarterLogOriginRead, quarterLogOrbitRead]

end
end Orbit
end AllPlaceOriginDefect
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
