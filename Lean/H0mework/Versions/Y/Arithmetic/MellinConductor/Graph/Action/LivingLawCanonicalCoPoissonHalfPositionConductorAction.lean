import H0mework.Versions.Y.Arithmetic.MellinConductor.Graph.Action.LivingLawCanonicalCoPoissonHalfPositionTriangularActionLaws

/-!
# Euler-conductor prefixes as one closed-graph action

Every normalized source dilation term is the restriction of the bounded
triangular half-position action at its generated logarithmic shift.  Finite
Euler-conductor prefixes therefore act on the same closed graph carrier;
there is no later comparison between an arithmetic prefix and an analytic
shadow.
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

open GraphLogPositionCone
open SourcePrefix
open scoped ArithmeticFunction

noncomputable section

def graphNormalizedHalfPositionActionTerm
    (coefficients : ArithmeticFunction ℝ) (index : Nat) :
    HalfPositionGraphCarrier →L[ℂ] HalfPositionGraphCarrier :=
  ((coefficients (index + 1) : ℂ) *
      (graphHalfDensityWeight index : ℂ)) •
    halfPositionGraphTriangularAction (graphLogTranslationShift index)

def graphNormalizedHalfPositionActionPrefix
    (coefficients : ArithmeticFunction ℝ) (cutoff : Nat) :
    HalfPositionGraphCarrier →L[ℂ] HalfPositionGraphCarrier :=
  ∑ index ∈ Finset.range cutoff,
    graphNormalizedHalfPositionActionTerm coefficients index

theorem halfPositionGraphFeature_normalizedSourceDilationTerm
    (z : ℂ) (coefficients : ArithmeticFunction ℝ) (index : Nat)
    (value : quarterMellinHalfPositionSourceDomain z) :
    halfPositionGraphFeature z
        (graphNormalizedSourceDilationTerm z coefficients index value) =
      graphNormalizedHalfPositionActionTerm coefficients index
        (halfPositionGraphFeature z value) := by
  unfold graphNormalizedSourceDilationTerm
    graphNormalizedHalfPositionActionTerm
  rw [LinearMap.smul_apply, map_smul, smul_apply]
  rw [← graphIntegerDilationScale_log]
  rw [halfPositionGraphTriangularAction_sourceDilation]

theorem halfPositionGraphFeature_normalizedSourceDilationPrefix
    (z : ℂ) (coefficients : ArithmeticFunction ℝ) (cutoff : Nat)
    (value : quarterMellinHalfPositionSourceDomain z) :
    halfPositionGraphFeature z
        (graphNormalizedSourceDilationPrefix z coefficients cutoff value) =
      graphNormalizedHalfPositionActionPrefix coefficients cutoff
        (halfPositionGraphFeature z value) := by
  unfold graphNormalizedSourceDilationPrefix
    graphNormalizedHalfPositionActionPrefix
  rw [LinearMap.sum_apply, map_sum, sum_apply]
  apply Finset.sum_congr rfl
  intro index membership
  exact halfPositionGraphFeature_normalizedSourceDilationTerm
    z coefficients index value

/-- Full linear naturality square between the maximal source domain and the
bounded graph action prefix. -/
theorem halfPositionGraphFeature_normalizedSourceDilationPrefix_naturality
    (z : ℂ) (coefficients : ArithmeticFunction ℝ) (cutoff : Nat) :
    (halfPositionGraphFeature z).comp
        (graphNormalizedSourceDilationPrefix z coefficients cutoff) =
      (graphNormalizedHalfPositionActionPrefix coefficients cutoff
        ).toLinearMap.comp (halfPositionGraphFeature z) := by
  apply LinearMap.ext
  intro value
  exact halfPositionGraphFeature_normalizedSourceDilationPrefix
    z coefficients cutoff value

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
