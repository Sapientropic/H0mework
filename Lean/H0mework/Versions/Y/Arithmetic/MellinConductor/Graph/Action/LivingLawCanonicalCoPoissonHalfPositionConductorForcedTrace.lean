import H0mework.Versions.Y.Arithmetic.MellinConductor.Graph.Action.LivingLawCanonicalCoPoissonHalfPositionConductorAction

/-!
# The Euler conductor is the forced graph-action trace

The triangular correction at integer scale `(n + 1)^2` is exactly
`log (n + 1)`.  Therefore the complete finite forced-trace prefix is the
first-coordinate read of the same action prefix with logarithmically derived
arithmetic coefficients.  For the generated global owner this is precisely
the existing Euler whole coefficient family, not an inserted analytic law.
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

open CanonicalArithmeticState.AllPlaceEulerLog
open GenericFoundation.Arithmetic.DirichletLogPosition
open GraphLogPositionCone
open SourcePrefix
open scoped ArithmeticFunction

noncomputable section

def graphNormalizedHalfPositionForcedTraceTerm
    (coefficients : ArithmeticFunction ℝ) (index : Nat) :
    HalfPositionGraphCarrier →L[ℂ] PositiveMellinQuarterEnergy :=
  ((coefficients (index + 1) : ℂ) *
      (graphHalfDensityWeight index : ℂ)) •
    halfPositionGraphForcedTrace (graphLogTranslationShift index)

def graphNormalizedHalfPositionForcedTracePrefix
    (coefficients : ArithmeticFunction ℝ) (cutoff : Nat) :
    HalfPositionGraphCarrier →L[ℂ] PositiveMellinQuarterEnergy :=
  ∑ index ∈ Finset.range cutoff,
    graphNormalizedHalfPositionForcedTraceTerm coefficients index

/-- Termwise conductor identification before any owner specialization. -/
theorem graphNormalizedHalfPositionForcedTraceTerm_eq_logPosition
    (coefficients : ArithmeticFunction ℝ) (index : Nat) :
    graphNormalizedHalfPositionForcedTraceTerm coefficients index =
      halfPositionGraphFst.comp
        (graphNormalizedHalfPositionActionTerm
          (logPosition coefficients) index) := by
  apply ContinuousLinearMap.ext
  intro value
  unfold graphNormalizedHalfPositionForcedTraceTerm
    graphNormalizedHalfPositionActionTerm
  rw [smul_apply, halfPositionGraphForcedTrace_apply,
    ContinuousLinearMap.comp_apply, smul_apply, map_smul,
    halfPositionGraphFst_triangularAction]
  simp only [smul_smul]
  unfold graphLogTranslationShift
  rw [logPosition_apply]
  push_cast
  module

theorem graphNormalizedHalfPositionForcedTracePrefix_eq_logPosition
    (coefficients : ArithmeticFunction ℝ) (cutoff : Nat) :
    graphNormalizedHalfPositionForcedTracePrefix coefficients cutoff =
      halfPositionGraphFst.comp
        (graphNormalizedHalfPositionActionPrefix
          (logPosition coefficients) cutoff) := by
  apply ContinuousLinearMap.ext
  intro value
  unfold graphNormalizedHalfPositionForcedTracePrefix
    graphNormalizedHalfPositionActionPrefix
  simp only [sum_apply, ContinuousLinearMap.comp_apply, map_sum]
  apply Finset.sum_congr rfl
  intro index membership
  exact congrArg
    (fun action : HalfPositionGraphCarrier →L[ℂ]
        PositiveMellinQuarterEnergy => action value)
    (graphNormalizedHalfPositionForcedTraceTerm_eq_logPosition
      coefficients index)

/-- Owner specialization: the root-generated logarithmic derivation turns
the forced trace into the already installed Euler whole action prefix. -/
theorem ownerHalfPositionForcedTracePrefix_eq_eulerWhole
    (owner : GlobalGermOwner) (cutoff : Nat) :
    graphNormalizedHalfPositionForcedTracePrefix
        (ownerRealCoefficients owner) cutoff =
      halfPositionGraphFst.comp
        (graphNormalizedHalfPositionActionPrefix
          ((GeneratedEulerLogFaceAt.generate owner).coefficients *
            ownerRealCoefficients owner) cutoff) := by
  rw [graphNormalizedHalfPositionForcedTracePrefix_eq_logPosition]
  congr 2
  exact CanonicalArithmeticState.AllPlaceEulerLog.Conductor.logPosition_ownerRealCoefficients_eq_log
      owner |>.trans
    (GeneratedEulerLogFaceAt.generate_convolution_eq_log owner).symm

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
