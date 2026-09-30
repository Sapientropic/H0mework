import H0mework.Foundation.Agency.Boundary
import H0mework.Foundation.Responsibility.Lineage

/-!
# Exact actor/responsibility incidence seeds

Responsibility incidence is compiled from exact seeds at the same target
edge state as the lifecycle event.  No free actor--bearer or
actor--obligation relation is accepted.  Each seed compiles its actor seed,
obligation and framework source event together.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Lifecycle
namespace Universal

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

universe u v w x

variable {Source : Type u} {State : Type v}
variable {occurrenceOf : Source → RootedAccountedUnfolding State}
variable {game : SaturationMonoid.ProcessGame occurrenceOf}
variable {core : SourceOwnedLifecycleCore.{u, v, w} occurrenceOf game}

/-- Raw source-owned incidence compiler. -/
structure ActorResponsibilityIncidenceCompiler
    (core : SourceOwnedLifecycleCore.{u, v, w} occurrenceOf game)
    (V : Vocabulary.{x}) where
  SourceSeed : Type (max w x)
  sourceAdmittedAt : SourceSeed → Prop
  sourceActorSeed : SourceSeed → core.sourceFace.Seed
  sourceActor_active : ∀ seed,
    sourceAdmittedAt seed →
      core.sourceFace.SeedAt game.source
        (core.sourceFace.state game.source) (sourceActorSeed seed)
  sourceObligation : SourceSeed → AdmittedObligation V
  sourceEvent : SourceSeed → V.SourceEvent
  TargetSeed : Type (max w x)
  targetAdmittedAt : TargetSeed → Prop
  targetActorSeed : TargetSeed → core.targetFace.Seed
  targetActor_active : ∀ seed,
    targetAdmittedAt seed →
      core.targetFace.SeedAt game.source
        (core.targetFace.state game.source) (targetActorSeed seed)
  targetObligation : TargetSeed → AdmittedObligation V
  targetEvent : TargetSeed → V.SourceEvent
  HistoricalSeed : Type (max w x)
  historicalAdmittedAt : HistoricalSeed → Prop
  historicalActorSeed : HistoricalSeed → core.HistorySeed
  historicalActorState : HistoricalSeed → State
  historicalActor_active : ∀ seed,
    historicalAdmittedAt seed →
      core.historySeedAt game.source (historicalActorState seed)
        (historicalActorSeed seed)
  historicalObligation : HistoricalSeed → AdmittedObligation V
  historicalEvent : HistoricalSeed → V.SourceEvent

namespace ActorResponsibilityIncidenceCompiler

def sourceIncidenceSeedAt
    {V : Vocabulary.{x}}
    (compiler : ActorResponsibilityIncidenceCompiler core V)
    (_source : Source) (state : State) (seed : compiler.SourceSeed) : Prop :=
  state = core.targetFace.state game.source ∧
    compiler.sourceAdmittedAt seed

abbrev ExactSourceSeed
    {V : Vocabulary.{x}}
    (compiler : ActorResponsibilityIncidenceCompiler core V) :=
  _root_.SaturationMonoid.ProcessGame.SourceSeed occurrenceOf
    compiler.SourceSeed compiler.sourceIncidenceSeedAt
    game.source

theorem ExactSourceSeed.admitted
    {V : Vocabulary.{x}}
    (compiler : ActorResponsibilityIncidenceCompiler core V)
    (seed : compiler.ExactSourceSeed) :
    compiler.sourceAdmittedAt seed.1 := by
  rcases seed.2 with ⟨state, _inTrace, _atTarget, admitted⟩
  exact admitted

def ExactSourceSeed.actorSeed
    {V : Vocabulary.{x}}
    (compiler : ActorResponsibilityIncidenceCompiler core V)
    (seed : compiler.ExactSourceSeed) :
    _root_.SaturationMonoid.ProcessGame.SourceSeed occurrenceOf
      core.sourceFace.Seed core.sourceFace.SeedAt
      game.source :=
  ⟨compiler.sourceActorSeed seed.1,
    core.sourceFace.state game.source,
    core.source_state_mem,
    compiler.sourceActor_active seed.1 (seed.admitted compiler)⟩

def ExactSourceSeed.actor
    {V : Vocabulary.{x}}
    (compiler : ActorResponsibilityIncidenceCompiler core V)
    (seed : compiler.ExactSourceSeed) : core.SourceActor :=
  core.sourceActorOf (seed.actorSeed compiler)

def ExactSourceSeed.obligation
    {V : Vocabulary.{x}}
    (compiler : ActorResponsibilityIncidenceCompiler core V)
    (seed : compiler.ExactSourceSeed) : AdmittedObligation V :=
  compiler.sourceObligation seed.1

def ExactSourceSeed.sourceEvent
    {V : Vocabulary.{x}}
    (compiler : ActorResponsibilityIncidenceCompiler core V)
    (seed : compiler.ExactSourceSeed) : V.SourceEvent :=
  compiler.sourceEvent seed.1

def targetIncidenceSeedAt
    {V : Vocabulary.{x}}
    (compiler : ActorResponsibilityIncidenceCompiler core V)
    (_source : Source) (state : State) (seed : compiler.TargetSeed) : Prop :=
  state = core.targetFace.state game.source ∧
    compiler.targetAdmittedAt seed

abbrev ExactTargetSeed
    {V : Vocabulary.{x}}
    (compiler : ActorResponsibilityIncidenceCompiler core V) :=
  _root_.SaturationMonoid.ProcessGame.SourceSeed occurrenceOf
    compiler.TargetSeed compiler.targetIncidenceSeedAt
    game.source

theorem ExactTargetSeed.admitted
    {V : Vocabulary.{x}}
    (compiler : ActorResponsibilityIncidenceCompiler core V)
    (seed : compiler.ExactTargetSeed) :
    compiler.targetAdmittedAt seed.1 := by
  rcases seed.2 with ⟨state, _inTrace, _atTarget, admitted⟩
  exact admitted

def ExactTargetSeed.actorSeed
    {V : Vocabulary.{x}}
    (compiler : ActorResponsibilityIncidenceCompiler core V)
    (seed : compiler.ExactTargetSeed) :
    _root_.SaturationMonoid.ProcessGame.SourceSeed occurrenceOf
      core.targetFace.Seed core.targetFace.SeedAt
      game.source :=
  ⟨compiler.targetActorSeed seed.1,
    core.targetFace.state game.source,
    core.target_state_mem,
    compiler.targetActor_active seed.1 (seed.admitted compiler)⟩

def ExactTargetSeed.actor
    {V : Vocabulary.{x}}
    (compiler : ActorResponsibilityIncidenceCompiler core V)
    (seed : compiler.ExactTargetSeed) : core.TargetActor :=
  core.targetActorOf (seed.actorSeed compiler)

def ExactTargetSeed.obligation
    {V : Vocabulary.{x}}
    (compiler : ActorResponsibilityIncidenceCompiler core V)
    (seed : compiler.ExactTargetSeed) : AdmittedObligation V :=
  compiler.targetObligation seed.1

def ExactTargetSeed.sourceEvent
    {V : Vocabulary.{x}}
    (compiler : ActorResponsibilityIncidenceCompiler core V)
    (seed : compiler.ExactTargetSeed) : V.SourceEvent :=
  compiler.targetEvent seed.1

def historicalIncidenceSeedAt
    {V : Vocabulary.{x}}
    (compiler : ActorResponsibilityIncidenceCompiler core V)
    (_source : Source) (state : State)
    (seed : compiler.HistoricalSeed) : Prop :=
  state = core.targetFace.state game.source ∧
    compiler.historicalAdmittedAt seed

abbrev ExactHistoricalSeed
    {V : Vocabulary.{x}}
    (compiler : ActorResponsibilityIncidenceCompiler core V) :=
  _root_.SaturationMonoid.ProcessGame.SourceSeed occurrenceOf
    compiler.HistoricalSeed
    compiler.historicalIncidenceSeedAt game.source

theorem ExactHistoricalSeed.admitted
    {V : Vocabulary.{x}}
    (compiler : ActorResponsibilityIncidenceCompiler core V)
    (seed : compiler.ExactHistoricalSeed) :
    compiler.historicalAdmittedAt seed.1 := by
  rcases seed.2 with ⟨state, _inTrace, _atTarget, admitted⟩
  exact admitted

def ExactHistoricalSeed.actorSeed
    {V : Vocabulary.{x}}
    (compiler : ActorResponsibilityIncidenceCompiler core V)
    (seed : compiler.ExactHistoricalSeed) :
    _root_.SaturationMonoid.ProcessGame.SourceSeed occurrenceOf
      core.HistorySeed core.historySeedAt game.source := by
  let state := compiler.historicalActorState seed.1
  have active := compiler.historicalActor_active seed.1
    (seed.admitted compiler)
  exact ⟨compiler.historicalActorSeed seed.1,
    state,
    List.mem_of_mem_take
      (core.history_before_event state (compiler.historicalActorSeed seed.1)
        active),
    active⟩

def ExactHistoricalSeed.actor
    {V : Vocabulary.{x}}
    (compiler : ActorResponsibilityIncidenceCompiler core V)
    (seed : compiler.ExactHistoricalSeed) : core.HistoricalActorBefore :=
  generatedActorOf game core.HistorySeed core.historySeedAt
    core.HistoryLineage core.historyLineageOf (seed.actorSeed compiler)

def ExactHistoricalSeed.obligation
    {V : Vocabulary.{x}}
    (compiler : ActorResponsibilityIncidenceCompiler core V)
    (seed : compiler.ExactHistoricalSeed) : AdmittedObligation V :=
  compiler.historicalObligation seed.1

def ExactHistoricalSeed.sourceEvent
    {V : Vocabulary.{x}}
    (compiler : ActorResponsibilityIncidenceCompiler core V)
    (seed : compiler.ExactHistoricalSeed) : V.SourceEvent :=
  compiler.historicalEvent seed.1

structure SourceResponsibilityAt
    {V : Vocabulary.{x}}
    (compiler : ActorResponsibilityIncidenceCompiler core V)
    (actor : core.SourceActor) (obligation : AdmittedObligation V)
    (sourceEvent : V.SourceEvent) where
  seed : compiler.ExactSourceSeed
  actor_eq : seed.actor compiler = actor
  obligation_eq : seed.obligation compiler = obligation
  sourceEvent_eq : seed.sourceEvent compiler = sourceEvent

structure TargetResponsibilityAt
    {V : Vocabulary.{x}}
    (compiler : ActorResponsibilityIncidenceCompiler core V)
    (actor : core.TargetActor) (obligation : AdmittedObligation V)
    (sourceEvent : V.SourceEvent) where
  seed : compiler.ExactTargetSeed
  actor_eq : seed.actor compiler = actor
  obligation_eq : seed.obligation compiler = obligation
  sourceEvent_eq : seed.sourceEvent compiler = sourceEvent

structure HistoricalResponsibilityAt
    {V : Vocabulary.{x}}
    (compiler : ActorResponsibilityIncidenceCompiler core V)
    (actor : core.HistoricalActorBefore) (obligation : AdmittedObligation V)
    (sourceEvent : V.SourceEvent) where
  seed : compiler.ExactHistoricalSeed
  actor_eq : seed.actor compiler = actor
  obligation_eq : seed.obligation compiler = obligation
  sourceEvent_eq : seed.sourceEvent compiler = sourceEvent

end ActorResponsibilityIncidenceCompiler

/-- Exact incidence compiler plus the only uniqueness needed downstream:
one fixed obligation occurrence determines at most one actor on each face. -/
structure ActorResponsibilityIncidence
    (core : SourceOwnedLifecycleCore.{u, v, w} occurrenceOf game)
    (V : Vocabulary.{x}) where
  compiler : ActorResponsibilityIncidenceCompiler core V
  source_actor_unique : ∀ {obligation sourceEvent first last},
    compiler.SourceResponsibilityAt first obligation sourceEvent →
      compiler.SourceResponsibilityAt last obligation sourceEvent →
        first = last
  target_actor_unique : ∀ {obligation sourceEvent first last},
    compiler.TargetResponsibilityAt first obligation sourceEvent →
      compiler.TargetResponsibilityAt last obligation sourceEvent →
        first = last
  historical_actor_unique : ∀ {obligation sourceEvent first last},
    compiler.HistoricalResponsibilityAt first obligation sourceEvent →
      compiler.HistoricalResponsibilityAt last obligation sourceEvent →
        first = last

namespace ActorResponsibilityIncidence

abbrev SourceResponsibilityAt
    {V : Vocabulary.{x}} (incidence : ActorResponsibilityIncidence core V) :=
  incidence.compiler.SourceResponsibilityAt

abbrev TargetResponsibilityAt
    {V : Vocabulary.{x}} (incidence : ActorResponsibilityIncidence core V) :=
  incidence.compiler.TargetResponsibilityAt

abbrev HistoricalResponsibilityAt
    {V : Vocabulary.{x}} (incidence : ActorResponsibilityIncidence core V) :=
  incidence.compiler.HistoricalResponsibilityAt

end ActorResponsibilityIncidence
end Universal
end Lifecycle
end Society
end ProcessGame
end SaturationMonoid
