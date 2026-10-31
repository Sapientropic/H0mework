import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Classical.Source.FreeStrategicOccurrence
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Future.RelationIndexedFuture

/-!
# M0/M2 generation of a free strategic program

The compatibility entry now owns only the M0 actor face and the M2
relation/actionable-future compiler.  Syntax and exact occurrence restrictions
are provided by the two lower source modules.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Classical
namespace Source

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations

namespace FreeStrategicSyntax

def actorSeedAt (program : FreeStrategicSyntax)
    (_source : Unit) (state : FreeClassicalAtom)
    (_actor : program.ActorIndex) : Prop :=
  state = program.actorBoundaryAtom

def actorFace (program : FreeStrategicSyntax) :
    M0BoundaryFace program.occurrenceOf where
  Seed := program.ActorIndex
  Lineage := fun _ => program.ActorIndex
  SeedAt := program.actorSeedAt
  lineageOf := fun _ seed => seed.1
  state := fun _ => program.actorBoundaryAtom
  seedAt_state := by
    intro source state seed active
    exact active

def exactActorSeed (program : FreeStrategicSyntax)
    (actor : program.ActorIndex) :
    SourceSeed program.occurrenceOf program.ActorIndex
      program.actorSeedAt () :=
  ⟨actor, program.actorBoundaryAtom,
    program.actorBoundaryAtom_mem_trace, rfl⟩

abbrev Actor (program : FreeStrategicSyntax) :=
  GeneratedActor (program.processGame) program.ActorIndex program.actorSeedAt
    (fun _ => program.ActorIndex) (fun _ seed => seed.1)

def actorOf (program : FreeStrategicSyntax)
    (actor : program.ActorIndex) : program.Actor :=
  generatedActorOf program.processGame program.ActorIndex program.actorSeedAt
    (fun _ => program.ActorIndex) (fun _ seed => seed.1)
    (program.exactActorSeed actor)

@[simp] theorem actorOf_value (program : FreeStrategicSyntax)
    (actor : program.ActorIndex) :
    (program.actorOf actor).1 = actor :=
  rfl

def relationSeedAt (program : FreeStrategicSyntax)
    (_source : Unit) (state : FreeClassicalAtom)
    (_player : program.Player) : Prop :=
  state = program.actorBoundaryAtom

structure ActionContinuationAt (program : FreeStrategicSyntax)
    (player : program.Player) (code : program.FutureCode) : Type where
  player_eq : code.1 = player

abbrev relationCompiler (program : FreeStrategicSyntax) :
    SourceOwnedRelationRoleCompiler program.occurrenceOf
      program.processGame program.actorFace where
  RelationSeed := program.Player
  RelationLineage := fun _ => program.Player
  relationSeedAt := program.relationSeedAt
  relationLineageOf := fun _ seed => seed.1
  beneficiaryActorSeed := program.playerActorIndex
  beneficiaryActor_active := by
    intro source state seed active
    exact active
  Role := fun _ => Unit
  Phase := fun _ => Unit
  sourceRoleOf := fun _ _ => ()
  phaseStepOf := fun _ _ => ()
  advanceRole := fun _ _ _ => ()
  FutureCode := program.FutureCode
  futureCodeDecidableEq := inferInstance
  futureCodeCarrier := Finset.univ
  futureIdle := fun _ => False
  FutureContinuationAt := fun player _side code =>
    ActionContinuationAt program player code
  futureBoundaryState := fun _ _ => .origin
  futureBoundaryState_mem := by
    intro lineage side
    exact program.origin_mem_trace
  FutureContinuationWitnessAt := fun _ _ _ continuation =>
    continuation.player_eq = continuation.player_eq
  futureContinuation_witnessed := by
    intro lineage side code continuation
    rfl

def exactRelationSeed (program : FreeStrategicSyntax)
    (player : program.Player) :
    program.relationCompiler.ExactRelationSeed :=
  ⟨player, program.actorBoundaryAtom,
    program.actorBoundaryAtom_mem_trace, rfl⟩

def generatedRelation (program : FreeStrategicSyntax)
    (player : program.Player) :
    program.relationCompiler.GeneratedRelation :=
  program.relationCompiler.relationOf (program.exactRelationSeed player)

theorem player_generates_interest (program : FreeStrategicSyntax)
    (player : program.Player) :
    program.relationCompiler.GeneratedInterestAt
      (program.actorOf (program.playerActorIndex player))
      (program.generatedRelation player) :=
  ⟨program.exactRelationSeed player, rfl, rfl⟩

abbrev GeneratedStrategy (program : FreeStrategicSyntax)
    (player : program.Player) :=
  { code : program.relationCompiler.FutureCode //
    code ∈ program.relationCompiler.actionableFutureCodesAt
      (program.generatedRelation player) .source }

theorem generatedStrategy_mem_iff (program : FreeStrategicSyntax)
    (player : program.Player)
    (code : program.relationCompiler.FutureCode) :
    code ∈ program.relationCompiler.actionableFutureCodesAt
        (program.generatedRelation player) .source ↔
      code.1 = player := by
  rw [program.relationCompiler.mem_actionableFutureCodesAt_iff]
  constructor
  · rintro ⟨_carrier, ⟨continuation⟩, _notIdle⟩
    exact continuation.player_eq
  · intro playerEq
    exact ⟨Finset.mem_univ _, ⟨⟨playerEq⟩⟩, by simp⟩

def generatedStrategyOf (program : FreeStrategicSyntax)
    (player : program.Player) (strategy : program.Strategy player) :
    program.GeneratedStrategy player :=
  ⟨⟨player, strategy⟩,
    (program.generatedStrategy_mem_iff player _).2 rfl⟩

def generatedStrategyEquiv (program : FreeStrategicSyntax)
    (player : program.Player) :
    program.GeneratedStrategy player ≃ program.Strategy player where
  toFun generated := by
    have playerEq :=
      (program.generatedStrategy_mem_iff player generated.1).1 generated.2
    exact playerEq ▸ generated.1.2
  invFun := program.generatedStrategyOf player
  left_inv := by
    intro generated
    apply Subtype.ext
    rcases generated with ⟨⟨codePlayer, strategy⟩, member⟩
    have playerEq :=
      (program.generatedStrategy_mem_iff player ⟨codePlayer, strategy⟩).1 member
    cases playerEq
    rfl
  right_inv := by intro strategy; rfl

end FreeStrategicSyntax
end
end Source
end Classical
end Society
end ProcessGame
end SaturationMonoid
