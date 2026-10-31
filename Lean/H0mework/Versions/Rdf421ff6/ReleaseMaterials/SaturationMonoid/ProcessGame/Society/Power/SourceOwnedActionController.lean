import H0mework.Foundation.Agency.Boundary
import Mathlib.Logic.ExistsUnique

/-!
# Source-owned actual-action controller

An action controller is generated from an exact action seed in the same
ProcessGame occurrence and then compiled through an existing M0 actor face.
The compiler stores neither a controller registry nor an owner verdict.  For a
fixed exact action occurrence the controller is a deterministic actor image.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Power

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal

universe u v w x

variable {Source : Type u} {State : Type v}
variable {occurrenceOf : Source → RootedAccountedUnfolding State}
variable {game : SaturationMonoid.ProcessGame occurrenceOf}

/-- Exact action seeds and their fixed compilation into one existing M0 actor
face.  `ActionSeed` is domain source data; a later `ControllerAt` carries an
occurrence trace witness and cannot be made from an actor label alone. -/
structure SourceOwnedActionControllerCompiler
    (game : SaturationMonoid.ProcessGame occurrenceOf)
    (actorFace : M0BoundaryFace.{u, v, w} occurrenceOf) where
  ActionSeed : Type x
  actionAdmittedAt : ActionSeed → Prop
  actionState : Source → State
  actionState_mem :
    actionState game.source ∈ game.occurrence.trace
  actorState_mem :
    actorFace.state game.source ∈ game.occurrence.trace
  actorSeed : ActionSeed → actorFace.Seed
  actorSeed_active : ∀ action,
    actionAdmittedAt action →
      actorFace.SeedAt game.source (actorFace.state game.source)
        (actorSeed action)

namespace SourceOwnedActionControllerCompiler

variable {actorFace : M0BoundaryFace.{u, v, w} occurrenceOf}

variable
  (compiler : SourceOwnedActionControllerCompiler.{u, v, w, x}
    game actorFace)

def actionSeedAt (_source : Source) (state : State)
    (action : compiler.ActionSeed) : Prop :=
  state = compiler.actionState game.source ∧
    compiler.actionAdmittedAt action

abbrev ExactActionSeed :=
  _root_.SaturationMonoid.ProcessGame.SourceSeed occurrenceOf
    compiler.ActionSeed compiler.actionSeedAt game.source

theorem ExactActionSeed.admitted
    (action : compiler.ExactActionSeed) :
    compiler.actionAdmittedAt action.1 := by
  rcases action.2 with ⟨_state, _inTrace, _atState, admitted⟩
  exact admitted

def ExactActionSeed.actorSeed
    (action : compiler.ExactActionSeed) :
    _root_.SaturationMonoid.ProcessGame.SourceSeed occurrenceOf
      actorFace.Seed actorFace.SeedAt game.source :=
  ⟨compiler.actorSeed action.1,
    actorFace.state game.source,
    compiler.actorState_mem,
    compiler.actorSeed_active action.1 (action.admitted compiler)⟩

abbrev Actor
    (_compiler : SourceOwnedActionControllerCompiler.{u, v, w, x}
      game actorFace) :=
  GeneratedActor game actorFace.Seed actorFace.SeedAt actorFace.Lineage
    actorFace.lineageOf

def ExactActionSeed.actor
    (action : compiler.ExactActionSeed) : compiler.Actor :=
  generatedActorOf game actorFace.Seed actorFace.SeedAt actorFace.Lineage
    actorFace.lineageOf (action.actorSeed compiler)

/-- Exact ownership for one fixed action occurrence. -/
def ControllerAt (action : compiler.ExactActionSeed)
    (actor : compiler.Actor) : Prop :=
  action.actor compiler = actor

/-- A fixed exact action occurrence generates exactly one controller actor. -/
theorem controller_total_unique (action : compiler.ExactActionSeed) :
    ∃! uniqueActor : compiler.Actor,
      compiler.ControllerAt action uniqueActor := by
  exact ⟨action.actor compiler, rfl, fun candidate equal => equal.symm⟩

/-- Controller authority exposes the exact occurrence trace seed from which
the actor was compiled. -/
theorem controller_provenance
    {action : compiler.ExactActionSeed} {actor : compiler.Actor}
    (_controlled : compiler.ControllerAt action actor) :
    ∃ state ∈ game.occurrence.trace,
      state = compiler.actionState game.source ∧
        compiler.actionAdmittedAt action.1 := by
  rcases action.2 with ⟨state, inTrace, atState, admitted⟩
  exact ⟨state, inTrace, atState, admitted⟩

end SourceOwnedActionControllerCompiler
end Power
end Society
end ProcessGame
end SaturationMonoid
