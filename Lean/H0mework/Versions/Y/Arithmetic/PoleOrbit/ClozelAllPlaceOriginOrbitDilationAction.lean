import H0mework.Versions.Y.Arithmetic.PoleOrbit.OriginOrbitCarrier
import H0mework.Versions.Y.Arithmetic.MuntzAction.CoPoissonMuntzDilationRelationSquare

/-!
# Dilation action on the complete all-place origin orbit

The restored orbit carrier is closed under the actual quarter-Mellin source
dilation.  Its first face is the existing relation action; its second face is
the complete counterterm-orbit translation.  Evaluation at zero recovers the
old scalar joint update only after the source occurrence is retained.
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

/-- Complete-orbit face of the quarter-Mellin dilation.  The extra scalar is
the source action's quarter-density weight; the carrier translation already
accounts for the co-Poisson half-density covariance. -/
def quarterMuntzOrbitDilationAction
    (scale : ℝ) (_positive : 0 < scale) :
    CoPoissonLogTranslationCarrier →ₗ[ℂ]
      CoPoissonLogTranslationCarrier :=
  (positiveMellinQuarterDilationWeight scale : ℂ) •
    coPoissonCarrierTranslation (Real.log (Real.sqrt scale))

theorem quarterMuntzOrbitDilationAction_source
    (scale : ℝ) (positive : 0 < scale)
    (test : SchwartzMap ℝ ℂ) :
    quarterMuntzOrbitDilationAction scale positive
        (coPoissonLogOrbitSourceMap test) =
      coPoissonLogOrbitSourceMap
        (quarterMuntzSchwartzDilationAction scale positive test) := by
  unfold quarterMuntzOrbitDilationAction
  rw [LinearMap.smul_apply]
  change (positiveMellinQuarterDilationWeight scale : ℂ) •
      coPoissonCarrierTranslation (Real.log (Real.sqrt scale))
        ⟨coPoissonLogOrbitMap test, ⟨test, rfl⟩⟩ = _
  rw [coPoissonCarrierTranslation_orbit]
  apply Subtype.ext
  change (positiveMellinQuarterDilationWeight scale : ℂ) •
      coPoissonLogOrbitMap
        (scaledSchwartzTest (Real.exp (Real.log (Real.sqrt scale)))
          (Real.exp_ne_zero _) test) =
    coPoissonLogOrbitMap
      ((positiveMellinQuarterDilationWeight scale : ℂ) •
        scaledSchwartzTest (Real.sqrt scale)
          (Real.sqrt_pos.2 positive).ne' test)
  rw [map_smul]
  congr 1
  apply congrArg (fun source : SchwartzMap ℝ ℂ =>
    coPoissonLogOrbitMap source)
  apply SchwartzMap.ext
  intro x
  simp only [scaledSchwartzTest_apply]
  rw [Real.exp_log (Real.sqrt_pos.2 positive)]

def allPlaceOriginOrbitDilationAction
    (z : ℂ) (scale : ℝ) (positive : 0 < scale) :
    AllPlaceOriginOrbitJointCarrier z →ₗ[ℂ]
      AllPlaceOriginOrbitJointCarrier z where
  toFun value :=
    (quarterDilationTestAction z scale positive value.1,
      quarterMuntzOrbitDilationAction scale positive value.2)
  map_add' left right := by
    apply Prod.ext
    · exact map_add (quarterDilationTestAction z scale positive)
        left.1 right.1
    · exact map_add (quarterMuntzOrbitDilationAction scale positive)
        left.2 right.2
  map_smul' coefficient value := by
    apply Prod.ext
    · exact map_smul (quarterDilationTestAction z scale positive)
        coefficient value.1
    · exact map_smul (quarterMuntzOrbitDilationAction scale positive)
        coefficient value.2

/-- The complete joint action commutes with the actual source relation map. -/
theorem allPlaceOriginOrbitDilationAction_relation
    (z : ℂ) (positiveZ : 0 < z.re)
    (belowHalf : z.re < (1 / 2 : ℝ))
    (scale : ℝ) (positive : 0 < scale)
    (test : SchwartzMap ℝ ℂ) :
    allPlaceOriginOrbitDilationAction z scale positive
        (allPlaceOriginOrbitRelationMap z positiveZ belowHalf test) =
      allPlaceOriginOrbitRelationMap z positiveZ belowHalf
        (quarterMuntzSchwartzDilationAction scale positive test) := by
  apply Prod.ext
  · exact LinearMap.congr_fun
      (quarterDilation_muntzRelation_square
        z positiveZ belowHalf scale positive) test
  · exact quarterMuntzOrbitDilationAction_source scale positive test

/-- Every generated dilation update remains in the complete relation-zero
face. -/
theorem allPlaceOriginOrbitDilationAction_relation_defect_zero
    (z : ℂ) (positiveZ : 0 < z.re)
    (belowHalf : z.re < (1 / 2 : ℝ))
    (scale : ℝ) (positive : 0 < scale)
    (test : SchwartzMap ℝ ℂ) :
    allPlaceOriginOrbitDefect z
        (allPlaceOriginOrbitDilationAction z scale positive
          (allPlaceOriginOrbitRelationMap z positiveZ belowHalf test)) = 0 := by
  rw [allPlaceOriginOrbitDilationAction_relation]
  exact allPlaceOriginOrbitDefect_relation_eq_zero
    z positiveZ belowHalf _

/-- Once the complete source orbit is kept, its action projects to the old
all-place scalar carrier as a source-generated update.  No endomorphism of a
bare caller-supplied scalar is assumed. -/
theorem allPlaceOriginOrbitDilationAction_evaluationZero_relation
    (owner : GlobalGermOwner)
    (z : ℂ) (positiveZ : 0 < z.re)
    (belowHalf : z.re < (1 / 2 : ℝ))
    (scale : ℝ) (positive : 0 < scale)
    (test : SchwartzMap ℝ ℂ) :
    allPlaceOriginOrbitEvaluationZero z
        (allPlaceOriginOrbitDilationAction z scale positive
          (allPlaceOriginOrbitRelationMap z positiveZ belowHalf test)) =
      allPlaceOriginRelationMap owner z positiveZ belowHalf
        (quarterMuntzSchwartzDilationAction scale positive test) := by
  rw [allPlaceOriginOrbitDilationAction_relation]
  exact allPlaceOriginOrbitEvaluationZero_relation
    owner z positiveZ belowHalf _

end
end Orbit
end AllPlaceOriginDefect
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
