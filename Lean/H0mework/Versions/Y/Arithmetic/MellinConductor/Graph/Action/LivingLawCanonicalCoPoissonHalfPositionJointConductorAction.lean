import H0mework.Versions.Y.Arithmetic.MellinConductor.Graph.Action.LivingLawCanonicalCoPoissonHalfPositionGraphCovariance
import H0mework.Versions.Y.Arithmetic.MellinConductor.Graph.Action.LivingLawCanonicalCoPoissonHalfPositionConductorForcedTrace

/-!
# Joint conductor action and its Riesz measurement sibling

The weighted finite conductor action acts on the complete half-position graph
target, not only on its Hilbert coordinate.  Its first coordinate is the
closed-graph action prefix, while its second coordinate is the same source
Mellin measurement.  For the canonical owner, the first coordinate recovers
the conductor forced trace and the second is read by the already generated
Müntz Riesz state.  This is a sibling-coordinate construction, not a map from
the vertical trace through the forgetful kernel.
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
open SourceGeneratedFunctionalGraphPerfectification
open SourcePrefix
open scoped ArithmeticFunction

noncomputable section

def graphNormalizedHalfPositionJointActionTerm
    (z : ℂ) (coefficients : ArithmeticFunction ℝ) (index : Nat) :
    GraphTarget HalfPositionGraphCarrier →L[ℂ]
      GraphTarget HalfPositionGraphCarrier :=
  ((coefficients (index + 1) : ℂ) *
      (graphHalfDensityWeight index : ℂ)) •
    graphTargetAction
      (halfPositionDilationGraphCovariance z
        (graphIntegerDilationScale index)
        (graphIntegerDilationScale_pos index))

def graphNormalizedHalfPositionJointActionPrefix
    (z : ℂ) (coefficients : ArithmeticFunction ℝ) (cutoff : Nat) :
    GraphTarget HalfPositionGraphCarrier →L[ℂ]
      GraphTarget HalfPositionGraphCarrier :=
  ∑ index ∈ Finset.range cutoff,
    graphNormalizedHalfPositionJointActionTerm z coefficients index

theorem graphNormalizedHalfPositionJointActionPrefix_add
    (z : ℂ) (left right : ArithmeticFunction ℝ) (cutoff : Nat) :
    graphNormalizedHalfPositionJointActionPrefix z (left + right) cutoff =
      graphNormalizedHalfPositionJointActionPrefix z left cutoff +
        graphNormalizedHalfPositionJointActionPrefix z right cutoff := by
  apply ContinuousLinearMap.ext
  intro value
  unfold graphNormalizedHalfPositionJointActionPrefix
    graphNormalizedHalfPositionJointActionTerm
  simp only [ArithmeticFunction.add_apply, sum_apply, add_apply, smul_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro index membership
  push_cast
  rw [add_mul, add_smul]

theorem graphNormalizedHalfPositionJointActionTerm_fst
    (z : ℂ) (coefficients : ArithmeticFunction ℝ) (index : Nat)
    (value : GraphTarget HalfPositionGraphCarrier) :
    (graphNormalizedHalfPositionJointActionTerm
      z coefficients index value).fst =
      graphNormalizedHalfPositionActionTerm coefficients index value.fst := by
  change ((coefficients (index + 1) : ℂ) *
      (graphHalfDensityWeight index : ℂ)) •
        halfPositionGraphTriangularAction
          (Real.log (graphIntegerDilationScale index)) value.fst = _
  unfold graphNormalizedHalfPositionActionTerm
  rw [← graphIntegerDilationScale_log]
  rfl

theorem graphNormalizedHalfPositionJointActionTerm_snd
    (z : ℂ) (coefficients : ArithmeticFunction ℝ) (index : Nat)
    (value : GraphTarget HalfPositionGraphCarrier) :
    (graphNormalizedHalfPositionJointActionTerm
      z coefficients index value).snd =
      ((coefficients (index + 1) : ℂ) *
        (graphHalfDensityWeight index : ℂ)) *
        quarterDilationCharacter z (graphIntegerDilationScale index) *
          value.snd := by
  unfold graphNormalizedHalfPositionJointActionTerm
  rw [smul_apply, WithLp.smul_snd, graphTargetAction_snd]
  change ((coefficients (index + 1) : ℂ) *
      (graphHalfDensityWeight index : ℂ)) *
        (quarterDilationCharacter z (graphIntegerDilationScale index) *
          value.snd) = _
  ring

theorem graphNormalizedHalfPositionJointActionTerm_source
    (z : ℂ) (coefficients : ArithmeticFunction ℝ) (index : Nat)
    (value : quarterMellinHalfPositionSourceDomain z) :
    graphNormalizedHalfPositionJointActionTerm z coefficients index
        (graphFeature (halfPositionGraphFeature z)
          (halfPositionGraphFunctional z) value) =
      graphFeature (halfPositionGraphFeature z)
        (halfPositionGraphFunctional z)
        (graphNormalizedSourceDilationTerm
          z coefficients index value) := by
  unfold graphNormalizedHalfPositionJointActionTerm
    graphNormalizedSourceDilationTerm
  rw [smul_apply, LinearMap.smul_apply, map_smul]
  exact congrArg
    (fun target : GraphTarget HalfPositionGraphCarrier =>
      ((coefficients (index + 1) : ℂ) *
        (graphHalfDensityWeight index : ℂ)) • target)
    (halfPositionDilationGraphTargetAction_source z
      (graphIntegerDilationScale index)
      (graphIntegerDilationScale_pos index) value)

theorem graphNormalizedHalfPositionJointActionPrefix_source
    (z : ℂ) (coefficients : ArithmeticFunction ℝ) (cutoff : Nat)
    (value : quarterMellinHalfPositionSourceDomain z) :
    graphNormalizedHalfPositionJointActionPrefix z coefficients cutoff
        (graphFeature (halfPositionGraphFeature z)
          (halfPositionGraphFunctional z) value) =
      graphFeature (halfPositionGraphFeature z)
        (halfPositionGraphFunctional z)
        (graphNormalizedSourceDilationPrefix
          z coefficients cutoff value) := by
  unfold graphNormalizedHalfPositionJointActionPrefix
    graphNormalizedSourceDilationPrefix
  rw [sum_apply, LinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro index membership
  exact graphNormalizedHalfPositionJointActionTerm_source
    z coefficients index value

theorem graphNormalizedHalfPositionJointActionPrefix_fst
    (z : ℂ) (coefficients : ArithmeticFunction ℝ) (cutoff : Nat)
    (value : GraphTarget HalfPositionGraphCarrier) :
    (graphNormalizedHalfPositionJointActionPrefix
      z coefficients cutoff value).fst =
      graphNormalizedHalfPositionActionPrefix
        coefficients cutoff value.fst := by
  unfold graphNormalizedHalfPositionJointActionPrefix
    graphNormalizedHalfPositionActionPrefix
  simp only [sum_apply]
  change (WithLp.fstₗ 2 ℂ HalfPositionGraphCarrier ℂ)
      (∑ i ∈ Finset.range cutoff,
        graphNormalizedHalfPositionJointActionTerm z coefficients i value) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro index membership
  exact graphNormalizedHalfPositionJointActionTerm_fst
    z coefficients index value

/-- The owner logarithmic action is already the sum of the retained Euler
action and the explicit convolution residual before either graph coordinate
is measured. -/
theorem ownerConductorJointActionPrefix_decomposition
    (z : ℂ) (owner : GlobalGermOwner) (cutoff : Nat) :
    graphNormalizedHalfPositionJointActionPrefix z
        ((CanonicalArithmeticState.AllPlaceEulerLog.GeneratedEulerLogFaceAt.generate
          owner).coefficients *
            CanonicalArithmeticState.AllPlaceEulerLog.ownerRealCoefficients owner)
        cutoff =
      graphNormalizedHalfPositionJointActionPrefix z
          (CanonicalArithmeticState.AllPlaceEulerLog.GeneratedEulerLogFaceAt.generate
            owner).coefficients cutoff +
        graphNormalizedHalfPositionJointActionPrefix z
          (LogPositionCone.ownerEulerConvolutionResidualCoefficients owner)
          cutoff := by
  rw [LogPositionCone.ownerEulerConvolutionCoefficients_decomposition,
    graphNormalizedHalfPositionJointActionPrefix_add]

theorem ownerConductorJointActionPrefix_decomposition_apply
    (z : ℂ) (owner : GlobalGermOwner) (cutoff : Nat)
    (value : GraphTarget HalfPositionGraphCarrier) :
    graphNormalizedHalfPositionJointActionPrefix z
        ((CanonicalArithmeticState.AllPlaceEulerLog.GeneratedEulerLogFaceAt.generate
          owner).coefficients *
            CanonicalArithmeticState.AllPlaceEulerLog.ownerRealCoefficients owner)
        cutoff value =
      graphNormalizedHalfPositionJointActionPrefix z
          (CanonicalArithmeticState.AllPlaceEulerLog.GeneratedEulerLogFaceAt.generate
            owner).coefficients cutoff value +
        graphNormalizedHalfPositionJointActionPrefix z
          (LogPositionCone.ownerEulerConvolutionResidualCoefficients owner)
          cutoff value := by
  have decomposition := congrArg
    (fun action : GraphTarget HalfPositionGraphCarrier →L[ℂ]
        GraphTarget HalfPositionGraphCarrier => action value)
    (ownerConductorJointActionPrefix_decomposition z owner cutoff)
  simpa only [add_apply] using decomposition

/-- The canonical owner forced trace and Mellin read are the two coordinates
of one joint action prefix. -/
theorem ownerConductorForcedTrace_jointMeasurement_siblings
    (z : ℂ) (owner : GlobalGermOwner) (cutoff : Nat)
    (value : quarterMellinHalfPositionSourceDomain z) :
    let joint := graphNormalizedHalfPositionJointActionPrefix z
      ((CanonicalArithmeticState.AllPlaceEulerLog.GeneratedEulerLogFaceAt.generate
        owner).coefficients *
          CanonicalArithmeticState.AllPlaceEulerLog.ownerRealCoefficients owner)
      cutoff
      (graphFeature (halfPositionGraphFeature z)
        (halfPositionGraphFunctional z) value)
    graphNormalizedHalfPositionForcedTracePrefix
        (CanonicalArithmeticState.AllPlaceEulerLog.ownerRealCoefficients owner)
        cutoff (halfPositionGraphFeature z value) =
      halfPositionGraphFst joint.fst ∧
    joint.snd = halfPositionGraphFunctional z
      (ownerEulerGraphWholeSourcePrefix z owner cutoff value) := by
  dsimp only
  constructor
  · have forced := congrArg
      (fun action : HalfPositionGraphCarrier →L[ℂ]
          PositiveMellinQuarterEnergy =>
        action (halfPositionGraphFeature z value))
      (ownerHalfPositionForcedTracePrefix_eq_eulerWhole owner cutoff)
    rw [ContinuousLinearMap.comp_apply] at forced
    rw [graphNormalizedHalfPositionJointActionPrefix_fst]
    exact forced
  · have source := graphNormalizedHalfPositionJointActionPrefix_source z
      ((CanonicalArithmeticState.AllPlaceEulerLog.GeneratedEulerLogFaceAt.generate
        owner).coefficients *
          CanonicalArithmeticState.AllPlaceEulerLog.ownerRealCoefficients owner)
      cutoff value
    exact congrArg WithLp.snd source

/-- On a zero occurrence the scalar sibling is exactly the existing Müntz
Riesz read of the same source prefix. -/
theorem ownerConductorJointMeasurement_eq_rieszRead
    (z : ℂ) (positiveZ : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (zero : riemannZeta (2 * z) = 0)
    (owner : GlobalGermOwner) (cutoff : Nat)
    (value : quarterMellinHalfPositionSourceDomain z) :
    let joint := graphNormalizedHalfPositionJointActionPrefix z
      ((CanonicalArithmeticState.AllPlaceEulerLog.GeneratedEulerLogFaceAt.generate
        owner).coefficients *
          CanonicalArithmeticState.AllPlaceEulerLog.ownerRealCoefficients owner)
      cutoff
      (graphFeature (halfPositionGraphFeature z)
        (halfPositionGraphFunctional z) value)
    joint.snd =
      inner ℂ (coPoissonMuntzRieszVector z positiveZ belowHalf zero)
        (coPoissonMuntzGraphSourceMap z positiveZ belowHalf
          (ownerEulerGraphWholeSourcePrefix z owner cutoff value).1) := by
  dsimp only
  rw [(ownerConductorForcedTrace_jointMeasurement_siblings
    z owner cutoff value).2]
  exact (coPoissonMuntzRieszVector_source_readback
    z positiveZ belowHalf zero
      (ownerEulerGraphWholeSourcePrefix z owner cutoff value).1).symm

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
