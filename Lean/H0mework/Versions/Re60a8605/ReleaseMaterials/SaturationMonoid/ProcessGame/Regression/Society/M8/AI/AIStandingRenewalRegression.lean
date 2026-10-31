import H0mework.Society.Renewal.RenewalFaceSource
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.AI.TraceWitnessedStanding

/-!
# M8 trace-witnessed AI renewal face

The exact canonical MultiAgent source seed generates the actor lineage,
standing readout, responsibility admission, maintained consumer edge, and
disposition.  The local face contains no consciousness or value oracle and
claims no operational authority before root installation.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M8AIStandingRenewalRegression

open ResponsibilityLifecycle
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open DomainReuse Renewal
open AI.TraceWitnessedStanding

def aiStandingOf
    (seed : SourceSeed threeAgentOccurrenceOf ThreeCycleTime
      MultiAgent.seedAt threeAgentProcessGame.source) :
    MultiAgent.GeneratedInteractionActor :=
  generatedActorOf threeAgentProcessGame ThreeCycleTime MultiAgent.seedAt
    MultiAgent.InteractionLineage MultiAgent.lineageOf seed

def AIConsumerAt
    (seed : SourceSeed threeAgentOccurrenceOf ThreeCycleTime
      MultiAgent.seedAt threeAgentProcessGame.source) :=
  ResponsibilityConsumerAt seed.1

def AIDispositionAt
    (seed : SourceSeed threeAgentOccurrenceOf ThreeCycleTime
      MultiAgent.seedAt threeAgentProcessGame.source) :=
  BoundaryDisposition V (obligation seed.1) seed.1

abbrev AILocalRenewalFace :=
  SourceGeneratedRenewalFace threeAgentProcessGame ThreeCycleTime
    MultiAgent.seedAt MultiAgent.InteractionLineage MultiAgent.lineageOf
    MultiAgent.GeneratedInteractionActor aiStandingOf
    AIConsumerAt AIDispositionAt

def aiRenewalSeed :
    SourceSeed threeAgentOccurrenceOf ThreeCycleTime
      MultiAgent.seedAt threeAgentProcessGame.source :=
  MultiAgent.sourceSeed .t0

def aiResponsibilityConsumer : AIConsumerAt aiRenewalSeed :=
  responsibilityConsumer .t0

def aiRenewalDisposition : AIDispositionAt aiRenewalSeed :=
  P.boundaryDisposition
    (ReviewEvent.renew (obligation := obligation .t0))

/-- Local source-generated face; root installation remains a separate
obligation. -/
def aiLocalRenewalFace : AILocalRenewalFace :=
  SourceGeneratedRenewalFace.generate aiRenewalSeed
    aiResponsibilityConsumer aiRenewalDisposition

@[simp] theorem aiLocalRenewalFace_event : aiLocalRenewalFace.event = .t0 :=
  rfl

theorem aiLocalRenewalFace_event_mem_trace :
    ∃ state ∈ threeAgentProcessGame.occurrence.trace,
      MultiAgent.seedAt threeAgentProcessGame.source state
        aiLocalRenewalFace.event :=
  aiLocalRenewalFace.event_mem_source_trace

@[simp] theorem aiLocalRenewalFace_actor_eq_standing :
    aiLocalRenewalFace.actor = aiLocalRenewalFace.standing :=
  rfl

theorem aiLocalRenewalFace_actor_exact :
    aiLocalRenewalFace.actor = actorOf .t0 :=
  rfl

theorem aiLocalRenewalFace_consumer_edge_exact :
    aiLocalRenewalFace.responsibilityConsumer.edge = renewalEdge .t0 :=
  aiLocalRenewalFace.responsibilityConsumer.edge_eq

theorem aiLocalRenewalFace_consumer_history_append :
    aiLocalRenewalFace.responsibilityConsumer.edge.target.history =
      (admittedState .t0).current.history ++
        [aiLocalRenewalFace.responsibilityConsumer.edge.lifecycleEvent] := by
  rw [aiLocalRenewalFace_consumer_edge_exact]
  exact renewal_history_append .t0

def aiLocalRenewalFace_consumer_source_owned :
    SourceOwnsResponsibilityIncidence V .t0 (obligation .t0) :=
  aiLocalRenewalFace.responsibilityConsumer.sourceOwnership

theorem aiLocalRenewalFace_continuation_disposition :
    aiLocalRenewalFace.exactDisposition = .carry (.maintained ()) :=
  rfl

/-- Exit is an actual alternative boundary event of the same installed
process, not a preinstalled future inside the renewal face. -/
theorem same_source_actual_exit_disposition :
    P.boundaryDisposition
      (ReviewEvent.exit (obligation := obligation .t0)) =
        .terminal (.final (.fulfilled ())) :=
  exitDisposition .t0

/-! ## No-free-standing control -/

def noAISeedAt
    (_source : Unit) (_state : ThreeAgentFoldPoint) (_seed : Empty) : Prop :=
  False

def noAILineage (_source : Unit) := Empty

def noAILineageOf
    (source : Unit)
    (seed : SourceSeed threeAgentOccurrenceOf Empty noAISeedAt source) :
    noAILineage source :=
  nomatch seed.1

theorem no_free_ai_standing :
    SourceGeneratedRenewalFace threeAgentProcessGame
      Empty noAISeedAt noAILineage noAILineageOf
      MultiAgent.GeneratedInteractionActor
      (fun seed => nomatch seed.1)
      (fun seed => nomatch seed.1)
      (fun seed => nomatch seed.1) → False :=
  noSourceSeed_noRenewalFace (fun seed => nomatch seed.1)

/-- Conditional local certificate.  It signs exact source provenance,
responsibility consumption, and the current disposition, while making no
consciousness/value claim and no root-standing claim. -/
structure AILocalRenewalFaceCertificate where
  traceWitnessed :
    ∃ state ∈ threeAgentProcessGame.occurrence.trace,
      MultiAgent.seedAt threeAgentProcessGame.source state
        aiLocalRenewalFace.event
  actorIsStanding : aiLocalRenewalFace.actor = aiLocalRenewalFace.standing
  actorExact : aiLocalRenewalFace.actor = actorOf .t0
  responsibilityBearerExact : (obligation .t0).bearer = actorOf .t0
  sourceLineageExact :
    (obligation .t0).lineage =
      MultiAgent.lineageOf () (MultiAgent.sourceSeed .t0)
  exactConsumerEdge :
    aiLocalRenewalFace.responsibilityConsumer.edge = renewalEdge .t0
  consumerHistoryAppend :
    aiLocalRenewalFace.responsibilityConsumer.edge.target.history =
      (admittedState .t0).current.history ++
        [aiLocalRenewalFace.responsibilityConsumer.edge.lifecycleEvent]
  consumerSourceOwned :
    SourceOwnsResponsibilityIncidence V .t0 (obligation .t0)
  continuationDisposition :
    aiLocalRenewalFace.exactDisposition = .carry (.maintained ())
  actualExitDisposition :
    P.boundaryDisposition
      (ReviewEvent.exit (obligation := obligation .t0)) =
        .terminal (.final (.fulfilled ()))

def aiLocalRenewalFaceDirectConsumer : AILocalRenewalFaceCertificate where
  traceWitnessed := aiLocalRenewalFace_event_mem_trace
  actorIsStanding := aiLocalRenewalFace_actor_eq_standing
  actorExact := aiLocalRenewalFace_actor_exact
  responsibilityBearerExact := obligation_bearer .t0
  sourceLineageExact := obligation_lineage .t0
  exactConsumerEdge := aiLocalRenewalFace_consumer_edge_exact
  consumerHistoryAppend := aiLocalRenewalFace_consumer_history_append
  consumerSourceOwned := aiLocalRenewalFace_consumer_source_owned
  continuationDisposition := aiLocalRenewalFace_continuation_disposition
  actualExitDisposition := same_source_actual_exit_disposition

end M8AIStandingRenewalRegression
end Society
end ProcessGame
end SaturationMonoid
