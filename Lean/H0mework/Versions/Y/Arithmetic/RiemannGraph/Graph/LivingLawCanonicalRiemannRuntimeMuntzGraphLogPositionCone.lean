import H0mework.Versions.Y.Arithmetic.RiemannGraph.RuntimeMuntzConductorCofinalCurrent
import H0mework.Versions.Y.Arithmetic.MellinConductor.GraphLogPosition

/-!
# Installed Quarter-Mellin graph log-position cone

The selected and reversal source-test orbits already installed in one runtime
occurrence are read in the square-root Quarter-Mellin chart.  Their graph
position commutators split into the installed Euler conductor current and the
same owner-generated forward convolution residual.  The existing quotient
source-map squares are retained in the same theorem.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace AllPlace
namespace WeilQuadratic
namespace Runtime
namespace MuntzGraph
namespace Conductor
namespace Graph

open ClozelGeneralizedDual
open ClozelGeneralizedDual.MuntzConductor
open ClozelGeneralizedDual.MuntzConductor.GraphLogPositionCone
open Character.GlobalCoPoissonCurrent
open Material
open NoIslandNoMagic.CanonicalArithmeticState.AllPlaceEulerLog.Conductor
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Runtime.MuntzGraph.Consumer

noncomputable section

/-- The graph prefix uses exactly the squared unit scale already carried by
the installed integral dilation orbit. -/
theorem graphIntegerDilationScale_eq_scaleSquare (index : Nat) :
    graphIntegerDilationScale index =
      scaleSquare (graphIntegerScaleUnit index) := by
  rfl

def runtimeSelectedGraphLogState
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence : JointRuntimeOccurrenceAt observation nontrivial current}
    (face : GeneratedRuntimeAllPlaceWeilFaceAt
      observation nontrivial occurrence) :
    GenericFoundation.Analysis.LogPositionTranslationCone.RawLogState :=
  quarterMellinGraphLogState
    (face.muntzSourceCurrentGraph.selectedTestOrbit
      (runtimeFaceIntegralSourceBoundary face))

def runtimeReversalGraphLogState
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence : JointRuntimeOccurrenceAt observation nontrivial current}
    (face : GeneratedRuntimeAllPlaceWeilFaceAt
      observation nontrivial occurrence) :
    GenericFoundation.Analysis.LogPositionTranslationCone.RawLogState :=
  quarterMellinGraphLogState
    (face.muntzSourceCurrentGraph.reversalTestOrbit
      (runtimeFaceIntegralSourceBoundary face))

theorem runtimeSelectedGraphDilationTerm_eq_sourceAction
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence : JointRuntimeOccurrenceAt observation nontrivial current}
    (face : GeneratedRuntimeAllPlaceWeilFaceAt
      observation nontrivial occurrence)
    (coefficients : ArithmeticFunction ℝ) (index : Nat) (x : ℝ) :
    graphNormalizedLogDilationTerm coefficients index
        (runtimeSelectedGraphLogState face) x =
      (coefficients (index + 1) : ℂ) *
        (graphHalfDensityWeight index : ℂ) *
          quarterMellinGraphLogState
            (quarterDilationTestAction
              (selectedCoPoissonMuntzParameter observation)
              (scaleSquare (graphIntegerScaleUnit index))
              (scaleSquare_pos (graphIntegerScaleUnit index))
              (face.muntzSourceCurrentGraph.selectedTestOrbit
                (runtimeFaceIntegralSourceBoundary face))) x := by
  simpa only [runtimeSelectedGraphLogState,
    graphIntegerDilationScale_eq_scaleSquare] using
    (graphNormalizedLogDilationTerm_eq_sourceAction
      coefficients index
      (face.muntzSourceCurrentGraph.selectedTestOrbit
        (runtimeFaceIntegralSourceBoundary face)) x)

theorem runtimeReversalGraphDilationTerm_eq_sourceAction
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence : JointRuntimeOccurrenceAt observation nontrivial current}
    (face : GeneratedRuntimeAllPlaceWeilFaceAt
      observation nontrivial occurrence)
    (coefficients : ArithmeticFunction ℝ) (index : Nat) (x : ℝ) :
    graphNormalizedLogDilationTerm coefficients index
        (runtimeReversalGraphLogState face) x =
      (coefficients (index + 1) : ℂ) *
        (graphHalfDensityWeight index : ℂ) *
          quarterMellinGraphLogState
            (quarterDilationTestAction
              (reversalCoPoissonMuntzParameter observation)
              (scaleSquare (graphIntegerScaleUnit index))
              (scaleSquare_pos (graphIntegerScaleUnit index))
              (face.muntzSourceCurrentGraph.reversalTestOrbit
                (runtimeFaceIntegralSourceBoundary face))) x := by
  simpa only [runtimeReversalGraphLogState,
    graphIntegerDilationScale_eq_scaleSquare] using
    (graphNormalizedLogDilationTerm_eq_sourceAction
      coefficients index
      (face.muntzSourceCurrentGraph.reversalTestOrbit
        (runtimeFaceIntegralSourceBoundary face)) x)

theorem globalOwnerEulerGraphRetainedPrefix_eq_runtime
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence : JointRuntimeOccurrenceAt observation nontrivial current}
    (face : GeneratedRuntimeAllPlaceWeilFaceAt
      observation nontrivial occurrence)
    (cutoff : Nat)
    (state : GenericFoundation.Analysis.LogPositionTranslationCone.RawLogState) :
    ownerEulerGraphRetainedPrefix
        globalEulerConductorOccurrence.root.1.1 cutoff state =
      graphNormalizedLogDilationPrefix
        face.eulerConductorCurrent cutoff state := by
  unfold ownerEulerGraphRetainedPrefix
  rw [face.eulerConductorCurrent_eq_global,
    globalEulerConductorOccurrence.root.2.conductorCurrent_eq,
    generatedEulerConductorCurrent_eq_eulerFace]

theorem runtimeSelectedMuntzGraphLogCone_decomposition
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence : JointRuntimeOccurrenceAt observation nontrivial current}
    (face : GeneratedRuntimeAllPlaceWeilFaceAt
      observation nontrivial occurrence)
    (cutoff : Nat) :
    ownerGraphLogDilationPrefix globalEulerConductorOccurrence.root.1.1
          cutoff (graphLogPosition (runtimeSelectedGraphLogState face)) -
        graphLogPosition
          (ownerGraphLogDilationPrefix
            globalEulerConductorOccurrence.root.1.1 cutoff
            (runtimeSelectedGraphLogState face)) =
      graphNormalizedLogDilationPrefix face.eulerConductorCurrent cutoff
          (runtimeSelectedGraphLogState face) +
        ownerEulerGraphResidualPrefix
          globalEulerConductorOccurrence.root.1.1 cutoff
          (runtimeSelectedGraphLogState face) := by
  rw [ownerGraphLogPositionCone_decomposition,
    globalOwnerEulerGraphRetainedPrefix_eq_runtime face]

theorem runtimeReversalMuntzGraphLogCone_decomposition
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence : JointRuntimeOccurrenceAt observation nontrivial current}
    (face : GeneratedRuntimeAllPlaceWeilFaceAt
      observation nontrivial occurrence)
    (cutoff : Nat) :
    ownerGraphLogDilationPrefix globalEulerConductorOccurrence.root.1.1
          cutoff (graphLogPosition (runtimeReversalGraphLogState face)) -
        graphLogPosition
          (ownerGraphLogDilationPrefix
            globalEulerConductorOccurrence.root.1.1 cutoff
            (runtimeReversalGraphLogState face)) =
      graphNormalizedLogDilationPrefix face.eulerConductorCurrent cutoff
          (runtimeReversalGraphLogState face) +
        ownerEulerGraphResidualPrefix
          globalEulerConductorOccurrence.root.1.1 cutoff
          (runtimeReversalGraphLogState face) := by
  rw [ownerGraphLogPositionCone_decomposition,
    globalOwnerEulerGraphRetainedPrefix_eq_runtime face]

/-- The installed occurrence exposes both source-map quotient squares and
both corrected graph-position current decompositions at once. -/
theorem runtimeMuntzGraphLogCone_projection
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence : JointRuntimeOccurrenceAt observation nontrivial current}
    (face : GeneratedRuntimeAllPlaceWeilFaceAt
      observation nontrivial occurrence)
    (cutoff : Nat) :
    let boundary := runtimeFaceIntegralSourceBoundary face
    face.muntzSourceCurrentGraph.selectedQuotientOrbit boundary =
        coPoissonMuntzGraphSourceMap
          (selectedCoPoissonMuntzParameter observation)
          (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
          (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial)
          (face.muntzSourceCurrentGraph.selectedTestOrbit boundary) ∧
      (ownerGraphLogDilationPrefix globalEulerConductorOccurrence.root.1.1
            cutoff (graphLogPosition (runtimeSelectedGraphLogState face)) -
          graphLogPosition
            (ownerGraphLogDilationPrefix
              globalEulerConductorOccurrence.root.1.1 cutoff
              (runtimeSelectedGraphLogState face)) =
        graphNormalizedLogDilationPrefix face.eulerConductorCurrent cutoff
            (runtimeSelectedGraphLogState face) +
          ownerEulerGraphResidualPrefix
            globalEulerConductorOccurrence.root.1.1 cutoff
            (runtimeSelectedGraphLogState face)) ∧
      face.muntzSourceCurrentGraph.reversalQuotientOrbit boundary =
        coPoissonMuntzGraphSourceMap
          (reversalCoPoissonMuntzParameter observation)
          (reversalCoPoissonMuntzParameter_re_pos observation nontrivial)
          (reversalCoPoissonMuntzParameter_re_lt_half observation nontrivial)
          (face.muntzSourceCurrentGraph.reversalTestOrbit boundary) ∧
      (ownerGraphLogDilationPrefix globalEulerConductorOccurrence.root.1.1
            cutoff (graphLogPosition (runtimeReversalGraphLogState face)) -
          graphLogPosition
            (ownerGraphLogDilationPrefix
              globalEulerConductorOccurrence.root.1.1 cutoff
              (runtimeReversalGraphLogState face)) =
        graphNormalizedLogDilationPrefix face.eulerConductorCurrent cutoff
            (runtimeReversalGraphLogState face) +
          ownerEulerGraphResidualPrefix
            globalEulerConductorOccurrence.root.1.1 cutoff
            (runtimeReversalGraphLogState face)) := by
  dsimp only
  exact ⟨
    GeneratedRuntimeMuntzSourceCurrentGraphAt.selected_graph_apply _ _,
    runtimeSelectedMuntzGraphLogCone_decomposition face cutoff,
    GeneratedRuntimeMuntzSourceCurrentGraphAt.reversal_graph_apply _ _,
    runtimeReversalMuntzGraphLogCone_decomposition face cutoff⟩

end
end Graph
end Conductor
end MuntzGraph
end Runtime
end WeilQuadratic
end AllPlace
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
