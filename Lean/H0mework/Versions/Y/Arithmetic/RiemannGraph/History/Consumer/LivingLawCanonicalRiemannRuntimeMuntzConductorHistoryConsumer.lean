import H0mework.Versions.Y.Arithmetic.PrimeLeakage.PrimeScaleRuntimeAlignment
import H0mework.Versions.Y.Arithmetic.RiemannGraph.Graph.Prefix.LivingLawCanonicalRiemannRuntimeMuntzHalfPositionConductorPrefix
import H0mework.Versions.Y.Arithmetic.RiemannGraph.History.Soundness.LivingLawCanonicalRiemannRuntimeMuntzConductorHistorySoundness
import H0mework.Versions.Y.Arithmetic.RiemannRuntime.PairedOmegaQuarterScaleRadialCurrent

/-!
# Direct consumers of the installed conductor history

One all-place face now exposes the exact conductor successor, its source and
closed half-position graph prefixes, and the installed Omega retained read.
The theorem records provenance and the existing decomposition; it does not
assert that the retained radial current vanishes.
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
namespace History

open CanonicalUnitArithmeticRoot
open ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
open ClozelGeneralizedDual.MuntzConductor.HalfPositionSource.SourcePrefix
open Material

noncomputable section

/-- The raw source boundary in an actual all-place face has the installed
retained incidence as its literal measurement projection. -/
theorem runtimeFace_sourceBoundary_measurement_eq_retained
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {current : Current}
    {occurrence : JointRuntimeOccurrenceAt observation nontrivial current}
    (face : GeneratedRuntimeAllPlaceWeilFaceAt
      observation nontrivial occurrence) :
    runtimeJointMeasurementFace face.sourceBoundaryWhole =
      runtimeJointBalanceFace face.retained := by
  rw [face.sourceBoundaryWhole_eq, face.retained_eq]
  change
    runtimeJointMeasurementFace
        (runtimeJointRelationGeneratorValue observation nontrivial
          (face.stage, .sourceBoundary)) =
      (installedRuntimeEffectValueAt observation nontrivial face.stage).retained
  exact runtimeJointSourceBoundary_measurement_eq_installedRetained
    observation nontrivial face.stage

theorem runtimeFace_sourceBoundary_radial_eq_retained
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {current : Current}
    {occurrence : JointRuntimeOccurrenceAt observation nontrivial current}
    (face : GeneratedRuntimeAllPlaceWeilFaceAt
      observation nontrivial occurrence) :
    retainedTargetModulusImbalance
        (runtimeJointMeasurementFace face.sourceBoundaryWhole) =
      retainedTargetModulusImbalance
        (runtimeJointBalanceFace face.retained) := by
  rw [runtimeFace_sourceBoundary_measurement_eq_retained face]

/-- A prime-power increment keeps the primitive Euler weight and the actual
co-Poisson source value inside the history evaluator. -/
theorem primePowerConductorHistoryIncrement_readback
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (test : SchwartzMap ℝ ℂ) (scale : ℝ)
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    conductorHistoryGeneratorValue
        (Consumer.primePowerRuntimeFace
          observation nontrivial prime exponent)
        (((prime : Nat) ^ exponent - 1), .increment) test scale =
      (Real.log ((prime : Nat) : ℝ) : ℂ) *
        ClozelGeneralizedDual.coPoissonMuntzEvenSource test
          ((((prime : Nat) ^ exponent : Nat) : ℝ) * scale) := by
  exact primePowerRuntimeFace_conductorDilationTerm
    observation nontrivial test scale prime exponent positive

/-- Exact successor and raw-boundary projection coexist in the same actual
prime-power runtime face. -/
theorem primePower_conductorSuccessor_and_rawEffect_projection
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat)
    (test : SchwartzMap ℝ ℂ) (scale : ℝ) (cutoff : Nat) :
    let face := Consumer.primePowerRuntimeFace
      observation nontrivial prime exponent
    runtimeFaceConductorDilationPrefix face test scale (cutoff + 1) =
        runtimeFaceConductorDilationPrefix face test scale cutoff +
          runtimeFaceConductorDilationTerm face test scale cutoff ∧
      runtimeJointMeasurementFace face.sourceBoundaryWhole =
        runtimeJointBalanceFace face.retained := by
  dsimp only
  exact ⟨runtimeFaceConductorDilationPrefix_succ _ _ _ _,
    runtimeFace_sourceBoundary_measurement_eq_retained _⟩

/-- Direct same-face consumer: the history relation, selected/reversal
half-position prefix decompositions and raw Omega read are simultaneous. -/
theorem runtimeConductorHistory_sourceGraph_directConsumer
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {current : Current}
    {occurrence : JointRuntimeOccurrenceAt observation nontrivial current}
    (face : GeneratedRuntimeAllPlaceWeilFaceAt
      observation nontrivial occurrence)
    (cutoff : Nat) :
    conductorHistoryFreeEvaluation face
        (conductorSuccessorRelation cutoff) = 0 ∧
      runtimeJointMeasurementFace face.sourceBoundaryWhole =
        runtimeJointBalanceFace face.retained ∧
      type_of% (runtimeSelected_ownerSourcePrefix_projection face cutoff) ∧
      type_of% (runtimeReversal_ownerSourcePrefix_projection face cutoff) := by
  exact ⟨conductorSuccessorRelation_evaluates_zero face cutoff,
    runtimeFace_sourceBoundary_measurement_eq_retained face,
    runtimeSelected_ownerSourcePrefix_projection face cutoff,
    runtimeReversal_ownerSourcePrefix_projection face cutoff⟩

end
end History
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
