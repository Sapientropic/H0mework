import H0mework.Realization.Graph.Action
import H0mework.Arithmetic.MuntzAction.CoPoissonMuntzDilationActionLaws

/-!
# Source covariance of the quarter-Mellin graph

The source dilation, energy translation, and Mellin character already act on
the same functional graph.  This covariance belongs below every all-place or
conductor runtime: those runtimes consume it, but do not generate it.
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

noncomputable section

def quarterMellinEnergyTranslationCLM (shift : ℝ) :
    PositiveMellinQuarterEnergy →L[ℂ] PositiveMellinQuarterEnergy :=
  (positiveMellinQuarterEnergyTranslationIsometry shift
    ).toLinearIsometry.toContinuousLinearMap

def quarterDilationGraphCovariance
    (z : ℂ) (scale : ℝ) (positive : 0 < scale) :
    GraphCovariance (C := QuarterMellinL2Test z)
      (H := PositiveMellinQuarterEnergy) (quarterMellinL2Feature z)
      (quarterMellinL2Functional z) where
  sourceAction := quarterDilationTestAction z scale positive
  hilbertAction := quarterMellinEnergyTranslationCLM (Real.log scale)
  character := quarterDilationCharacter z scale
  feature_covariance := quarterDilationFeature_covariance z scale positive
  functional_eigenlaw := quarterDilationFunctional_eigenlaw z scale positive

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
