import H0mework.Versions.Y.Arithmetic.PrimeLeakage.PrimePowerRuntimeWholeQuadratic

/-!
# Prime-power projection of the runtime Müntz source-current graph

The installed source boundary is evaluated before any scalar read.  Its
selected and reversal Schwartz tests and graph-cokernel classes remain in the
same runtime face.  Only then does the conductor-weighted character read
recover the retained Euler quadratic.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

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
namespace Consumer

open Character.IntegralCharacterGroupRing
open ClozelGeneralizedDual
open ClozelGeneralizedDual.CenteredGram
open ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
open ClozelGeneralizedDual.ThetaJRoleRepresentation
open Material
open PrimePower.Quadratic
open PrimePower.Source
open Quadratic
open SourceGeneratedIntegralCharacterGroupRing
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Occurrence
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Runtime.Consumer
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Source

noncomputable section

def runtimeFaceIntegralSourceBoundary
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence : JointRuntimeOccurrenceAt observation nontrivial current}
    (face : GeneratedRuntimeAllPlaceWeilFaceAt
      observation nontrivial occurrence) : IntegralScaleCarrier :=
  runtimeJointIntegralFace face.sourceBoundaryWhole

theorem primePowerRuntimeFace_integralBoundary_eq_source
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) :
    runtimeFaceIntegralSourceBoundary
        (primePowerRuntimeFace observation nontrivial prime exponent) =
      primePowerBoundaryIntegralReadFromSource
        (zeroOwnedAllPrimeWeilQuadraticOccurrence
          observation nontrivial).root prime exponent := by
  unfold runtimeFaceIntegralSourceBoundary
  rw [(primePowerRuntimeFace observation nontrivial prime exponent
      ).sourceBoundaryWhole_eq,
    primePowerRuntimeFace_stage,
    primePowerBoundaryIntegralReadFromSource_root_eq]
  rfl

def runtimeFaceMuntzCharacterLeakage
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {current : CanonicalUnitArithmeticRoot.Current}
    {occurrence : JointRuntimeOccurrenceAt observation nontrivial current}
    (face : GeneratedRuntimeAllPlaceWeilFaceAt
      observation nontrivial occurrence) : ℂ :=
  face.reversalCharacterEvaluation (runtimeFaceIntegralSourceBoundary face) -
    face.selectedCharacterEvaluation (runtimeFaceIntegralSourceBoundary face)

theorem primePowerRuntimeFace_muntzLeakage_eq_source
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) :
    runtimeFaceMuntzCharacterLeakage
        (primePowerRuntimeFace observation nontrivial prime exponent) =
      primePowerCharacterLeakageReadFromSource
        (zeroOwnedAllPrimeWeilQuadraticOccurrence
          observation nontrivial).root prime exponent := by
  unfold runtimeFaceMuntzCharacterLeakage
  rw [primePowerRuntimeFace_integralBoundary_eq_source]
  change reversalGraphCharacterEvaluationFromSource
        (zeroOwnedAllPrimeWeilQuadraticOccurrence
          observation nontrivial).root.1
        (primePowerBoundaryIntegralReadFromSource
          (zeroOwnedAllPrimeWeilQuadraticOccurrence
            observation nontrivial).root prime exponent) -
      selectedGraphCharacterEvaluationFromSource
        (zeroOwnedAllPrimeWeilQuadraticOccurrence
          observation nontrivial).root.1
        (primePowerBoundaryIntegralReadFromSource
          (zeroOwnedAllPrimeWeilQuadraticOccurrence
            observation nontrivial).root prime exponent) = _
  rfl

theorem primePowerRuntimeFace_muntzLeakage_eq_retainedAmplitude
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    runtimeFaceMuntzCharacterLeakage
        (primePowerRuntimeFace observation nontrivial prime exponent) =
      runtimeFaceRetainedAmplitude
        (primePowerRuntimeFace observation nontrivial prime exponent) := by
  rw [primePowerRuntimeFace_muntzLeakage_eq_source,
    primePowerRuntimeRetainedAmplitude_eq_characterLeakage
      observation nontrivial prime exponent positive]

theorem primePowerRuntimeMuntzSourceCurrent_quadratic
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    let face := primePowerRuntimeFace
      observation nontrivial prime exponent
    face.eulerConductorCurrent
          (thetaDistributionPrimePower prime exponent) *
        ‖runtimeFaceMuntzCharacterLeakage face‖ ^ 2 =
      primePowerRuntimeRetainedQuadratic face prime exponent := by
  dsimp only
  rw [primePowerRuntimeFace_conductor_eq_eulerWeight,
    primePowerRuntimeFace_muntzLeakage_eq_retainedAmplitude
      observation nontrivial prime exponent positive]
  rfl

/-- One theorem exposes the two actual graph squares and their retained
quadratic read at the same runtime occurrence. -/
theorem primePowerRuntimeMuntzSourceCurrent_projection
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (prime : Nat.Primes) (exponent : Nat) (positive : 0 < exponent) :
    let face := primePowerRuntimeFace
      observation nontrivial prime exponent
    let boundary := runtimeFaceIntegralSourceBoundary face
    face.muntzSourceCurrentGraph.selectedQuotientOrbit boundary =
        coPoissonMuntzGraphSourceMap
          (selectedCoPoissonMuntzParameter observation)
          (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
          (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial)
          (face.muntzSourceCurrentGraph.selectedTestOrbit boundary) ∧
      face.muntzSourceCurrentGraph.reversalQuotientOrbit boundary =
        coPoissonMuntzGraphSourceMap
          (reversalCoPoissonMuntzParameter observation)
          (reversalCoPoissonMuntzParameter_re_pos observation nontrivial)
          (reversalCoPoissonMuntzParameter_re_lt_half observation nontrivial)
          (face.muntzSourceCurrentGraph.reversalTestOrbit boundary) ∧
      face.eulerConductorCurrent
          (thetaDistributionPrimePower prime exponent) *
          ‖runtimeFaceMuntzCharacterLeakage face‖ ^ 2 =
        primePowerRuntimeRetainedQuadratic face prime exponent := by
  dsimp only
  exact ⟨GeneratedRuntimeMuntzSourceCurrentGraphAt.selected_graph_apply _ _,
    GeneratedRuntimeMuntzSourceCurrentGraphAt.reversal_graph_apply _ _,
    primePowerRuntimeMuntzSourceCurrent_quadratic
      observation nontrivial prime exponent positive⟩

end
end Consumer
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
