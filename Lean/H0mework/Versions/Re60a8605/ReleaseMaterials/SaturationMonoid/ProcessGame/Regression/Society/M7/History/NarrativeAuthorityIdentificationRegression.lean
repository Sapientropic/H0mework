import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Observer.ReadoutFactorization
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M7.History.TraceConstrainedNarrativeFixture

/-!
# M7 history and narrative authority boundary

The visible narrative factors through the M6 observer and has a genuinely
non-singleton actual-occurrence fibre.  Every emitted claim is constrained by
the existing source trace, while an explicitly unsupported claim is rejected.
The same M6 attachment boundary forbids complete authority reconstruction from
the narrative.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M7NarrativeAuthorityIdentificationRegression

noncomputable section

open Classical.GeneratedTerminalExchange
open Classical.Source.FreeStrategicSyntax
open M5SourceFirstCrossOccurrenceFixture
open M5SourceFirstCrossOccurrenceResidual
open M6NormalizedAuthorityObserverFixture
open M6FaithfulReconstructionNoGoRegression
open M6NaturalReconstructionNoGoRegression
open M7TraceConstrainedNarrativeFixture
open History Observer

def visibleNarrative (_visible : NormalizedImage) : Narrative :=
  commonNarrative

def narrativeOccurrenceReadout :
    OccurrenceReadout ActualPath Narrative :=
  OccurrenceReadout.ofVisible societyObserver visibleNarrative

def narrativeFactorization :
    ReadoutFactorization societyObserver narrativeOccurrenceReadout :=
  ReadoutFactorization.ofVisible societyObserver visibleNarrative

theorem visible_narrative_factorization_positive :
    Nonempty
      (ReadoutFactorization societyObserver narrativeOccurrenceReadout) :=
  ReadoutFactorization.visibleComputation_nonempty
    societyObserver visibleNarrative

theorem narrative_readout_is_trace_readout (path : ActualPath) :
    narrativeOccurrenceReadout.read path =
      narrativeReadout.narrative path :=
  rfl

theorem every_emitted_narrative_is_trace_constrained (path : ActualPath) :
    narrativeReadout.SupportsAt path
      (narrativeOccurrenceReadout.read path) := by
  rw [narrative_readout_is_trace_readout]
  exact narrativeReadout.emitted_supports path

theorem left_trace_is_existing_occurrence_trace :
    narrativeReadout.trace leftPath = leftProgram.occurrence.trace :=
  rfl

theorem right_trace_is_existing_occurrence_trace :
    narrativeReadout.trace rightPath = rightProgram.occurrence.trace :=
  rfl

theorem narrative_no_complete_authority_identification :
    ¬ Nonempty
      (AuthorityCompleteReadoutAt societyObserver narrativeOccurrenceReadout) :=
  societySourceGeneratedAttachingDirection
    |>.boundary_noAuthorityCompleteReadout narrativeFactorization

structure NarrativeAuthorityIdentificationCertificate : Prop where
  leftExactConsumer : TerminalAuthorityConsumerAt leftProgram leftTerminal
  rightExactConsumer : TerminalAuthorityConsumerAt rightProgram rightTerminal
  leftTraceExact :
    narrativeReadout.trace leftPath = leftProgram.occurrence.trace
  rightTraceExact :
    narrativeReadout.trace rightPath = rightProgram.occurrence.trace
  commonNarrativeHasWitnessedOriginClaim :
    FreeClassicalAtom.origin ∈ narrativeReadout.claims commonNarrative
  allEmittedNarrativesTraceConstrained : ∀ path,
    narrativeReadout.SupportsAt path
      (narrativeOccurrenceReadout.read path)
  sameNarrative :
    narrativeOccurrenceReadout.read leftPath =
      narrativeOccurrenceReadout.read rightPath
  narrativeFibreNotSingleton :
    ¬ Subsingleton
      (narrativeReadout.NarrativeFibreAt
        (narrativeReadout.narrative leftPath))
  actualOccurrencesDifferent :
    actualOccurrence leftPath ≠ actualOccurrence rightPath
  authorityDifferent :
    societyObserver.authorityK leftPath ≠
      societyObserver.authorityK rightPath
  leftAuthorityClaimWitnessed :
    narrativeReadout.SupportsAt leftPath leftAuthorityNarrative
  sameClaimRejectedWithoutRightTraceWitness :
    ¬ narrativeReadout.SupportsAt rightPath leftAuthorityNarrative
  visibleFactorization : Nonempty
    (ReadoutFactorization societyObserver narrativeOccurrenceReadout)
  attachmentBoundaryExact :
    societySourceGeneratedAttachingDirection.boundaryKernelPair =
      societyRootedObserverObstruction.kernelPair
  noCompleteAuthorityIdentification :
    ¬ Nonempty
      (AuthorityCompleteReadoutAt societyObserver narrativeOccurrenceReadout)

theorem narrativeAuthorityIdentificationDirectConsumer :
    NarrativeAuthorityIdentificationCertificate where
  leftExactConsumer := left_exact_authority_consumer
  rightExactConsumer := right_exact_authority_consumer
  leftTraceExact := left_trace_is_existing_occurrence_trace
  rightTraceExact := right_trace_is_existing_occurrence_trace
  commonNarrativeHasWitnessedOriginClaim :=
    commonNarrative_has_witnessed_origin_claim
  allEmittedNarrativesTraceConstrained :=
    every_emitted_narrative_is_trace_constrained
  sameNarrative := rfl
  narrativeFibreNotSingleton := common_narrative_fibre_not_subsingleton
  actualOccurrencesDifferent := actualOccurrences_ne
  authorityDifferent := pathAuthorityK_ne
  leftAuthorityClaimWitnessed := leftAuthorityNarrative_supported_left
  sameClaimRejectedWithoutRightTraceWitness :=
    leftAuthorityNarrative_not_supported_right
  visibleFactorization := visible_narrative_factorization_positive
  attachmentBoundaryExact := society_attaching_boundary_exact
  noCompleteAuthorityIdentification :=
    narrative_no_complete_authority_identification

end
end M7NarrativeAuthorityIdentificationRegression
end Society
end ProcessGame
end SaturationMonoid
