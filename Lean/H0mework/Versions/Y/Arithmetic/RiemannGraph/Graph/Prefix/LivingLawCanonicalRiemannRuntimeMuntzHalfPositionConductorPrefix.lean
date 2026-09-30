import H0mework.Versions.Y.Arithmetic.MellinConductor.Prefix.Source.LivingLawCanonicalCoPoissonHalfPositionConductorPrefix

/-!
# Runtime specialization of the half-position conductor prefix

The selected and reversal tests stored by one installed all-place face consume
the source-level whole/retained/residual decomposition directly.  The same
values are preserved by the closed graph feature and the raw log read.
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
namespace SourcePrefix

noncomputable section

open CanonicalArithmeticState.AllPlaceEulerLog.Conductor
open GraphLogPositionCone

open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Runtime.Material
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Runtime.MuntzGraph.Consumer
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Runtime.MuntzGraph.Conductor.Graph
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Runtime.MuntzGraph.Conductor.Graph.Domain

/-- Selected runtime specialization: source equality, closed-graph equality,
and raw logarithmic whole read all use the same installed boundary value. -/
theorem runtimeSelected_ownerSourcePrefix_projection
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence : JointRuntimeOccurrenceAt observation nontrivial current}
    (face : GeneratedRuntimeAllPlaceWeilFaceAt
      observation nontrivial occurrence)
    (cutoff : Nat) :
    let owner := globalEulerConductorOccurrence.root.1.1
    let z := selectedCoPoissonMuntzParameter observation
    let value := runtimeSelectedHalfPositionValue face
    ownerEulerGraphWholeSourcePrefix z owner cutoff value =
        ownerEulerGraphRetainedSourcePrefix z owner cutoff value +
          ownerEulerGraphResidualSourcePrefix z owner cutoff value ∧
      halfPositionGraphFeature z
          (ownerEulerGraphWholeSourcePrefix z owner cutoff value) =
        halfPositionGraphFeature z
            (ownerEulerGraphRetainedSourcePrefix z owner cutoff value) +
          halfPositionGraphFeature z
            (ownerEulerGraphResidualSourcePrefix z owner cutoff value) ∧
      quarterMellinGraphLogState
          (ownerEulerGraphWholeSourcePrefix z owner cutoff value).1 =
        ownerEulerGraphWholePrefix owner cutoff
          (runtimeSelectedGraphLogState face) := by
  dsimp only
  refine ⟨ownerEulerGraphSourcePrefix_decomposition_apply _ _ _ _, ?_, ?_⟩
  · have equality := LinearMap.congr_fun
      (ownerEulerGraphFeaturePrefix_decomposition
        (selectedCoPoissonMuntzParameter observation)
        globalEulerConductorOccurrence.root.1.1 cutoff)
      (runtimeSelectedHalfPositionValue face)
    simpa only [LinearMap.comp_apply, LinearMap.add_apply] using equality
  · exact ownerEulerGraphWholeSourcePrefix_log_readback _ _ _ _

/-- Reversal sibling of the same source-generated finite-prefix projection. -/
theorem runtimeReversal_ownerSourcePrefix_projection
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence : JointRuntimeOccurrenceAt observation nontrivial current}
    (face : GeneratedRuntimeAllPlaceWeilFaceAt
      observation nontrivial occurrence)
    (cutoff : Nat) :
    let owner := globalEulerConductorOccurrence.root.1.1
    let z := reversalCoPoissonMuntzParameter observation
    let value := runtimeReversalHalfPositionValue face
    ownerEulerGraphWholeSourcePrefix z owner cutoff value =
        ownerEulerGraphRetainedSourcePrefix z owner cutoff value +
          ownerEulerGraphResidualSourcePrefix z owner cutoff value ∧
      halfPositionGraphFeature z
          (ownerEulerGraphWholeSourcePrefix z owner cutoff value) =
        halfPositionGraphFeature z
            (ownerEulerGraphRetainedSourcePrefix z owner cutoff value) +
          halfPositionGraphFeature z
            (ownerEulerGraphResidualSourcePrefix z owner cutoff value) ∧
      quarterMellinGraphLogState
          (ownerEulerGraphWholeSourcePrefix z owner cutoff value).1 =
        ownerEulerGraphWholePrefix owner cutoff
          (runtimeReversalGraphLogState face) := by
  dsimp only
  refine ⟨ownerEulerGraphSourcePrefix_decomposition_apply _ _ _ _, ?_, ?_⟩
  · have equality := LinearMap.congr_fun
      (ownerEulerGraphFeaturePrefix_decomposition
        (reversalCoPoissonMuntzParameter observation)
        globalEulerConductorOccurrence.root.1.1 cutoff)
      (runtimeReversalHalfPositionValue face)
    simpa only [LinearMap.comp_apply, LinearMap.add_apply] using equality
  · exact ownerEulerGraphWholeSourcePrefix_log_readback _ _ _ _

end
end SourcePrefix
end HalfPositionSource
end MuntzConductor
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
