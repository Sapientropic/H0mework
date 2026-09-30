import H0mework.Versions.Y.Arithmetic.CoPoisson.QuarterMellinGraphCovariance
import H0mework.Versions.Y.Arithmetic.MellinConductor.Graph.Action.LivingLawCanonicalCoPoissonHalfPositionConductorAction

/-!
# Joint covariance of half-position, energy and Mellin measurement

One source dilation now acts simultaneously on the maximal half-position
domain, its bounded triangular closed-graph coordinate, and the Mellin
measurement.  Forgetting the half-position coordinate strictly commutes with
the pre-existing Quarter-Mellin graph action.  Thus the two graph carriers
are dependent faces of one action, not separately generated shadows.
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
namespace GraphAction

open SourceGeneratedFunctionalGraphPerfectification
open SourcePrefix

noncomputable section

def halfPositionDilationGraphCovariance
    (z : ℂ) (scale : ℝ) (positive : 0 < scale) :
    GraphCovariance (C := quarterMellinHalfPositionSourceDomain z)
      (H := HalfPositionGraphCarrier) (halfPositionGraphFeature z)
      (halfPositionGraphFunctional z) where
  sourceAction := halfPositionSourceDilation z scale positive
  hilbertAction := halfPositionGraphTriangularAction (Real.log scale)
  character := quarterDilationCharacter z scale
  feature_covariance := by
    apply LinearMap.ext
    intro value
    exact halfPositionGraphTriangularAction_sourceDilation
      z scale positive value
  functional_eigenlaw := by
    apply LinearMap.ext
    intro value
    exact LinearMap.congr_fun
      (quarterDilationFunctional_eigenlaw z scale positive) value.1

/-- The forgetful graph morphism preserves the whole action, including its
Mellin character coordinate.  Only the conductor shear is forgotten. -/
theorem halfPositionDilationGraphTargetAction_projects
    (z : ℂ) (scale : ℝ) (positive : 0 < scale)
    (value : GraphTarget HalfPositionGraphCarrier) :
    graphTargetMap (halfPositionGraphSourceMorphism z)
        (graphTargetAction
          (halfPositionDilationGraphCovariance z scale positive) value) =
      graphTargetAction (quarterDilationGraphCovariance z scale positive)
        (graphTargetMap (halfPositionGraphSourceMorphism z) value) := by
  rw [WithLp.ext_iff]
  apply Prod.ext
  · change halfPositionGraphFst
        (halfPositionGraphTriangularAction (Real.log scale) value.fst) =
      positiveMellinQuarterEnergyTranslation (Real.log scale)
        (halfPositionGraphFst value.fst)
    rw [halfPositionGraphFst_triangularAction]
  · rfl

/-- Direct source consumer of the same graph covariance. -/
theorem halfPositionDilationGraphTargetAction_source
    (z : ℂ) (scale : ℝ) (positive : 0 < scale)
    (value : quarterMellinHalfPositionSourceDomain z) :
    graphTargetAction
        (halfPositionDilationGraphCovariance z scale positive)
        (graphFeature (halfPositionGraphFeature z)
          (halfPositionGraphFunctional z) value) =
      graphFeature (halfPositionGraphFeature z)
        (halfPositionGraphFunctional z)
        (halfPositionSourceDilation z scale positive value) := by
  exact graphTargetAction_source
    (halfPositionDilationGraphCovariance z scale positive) value

end
end GraphAction
end HalfPositionSource
end MuntzConductor
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
