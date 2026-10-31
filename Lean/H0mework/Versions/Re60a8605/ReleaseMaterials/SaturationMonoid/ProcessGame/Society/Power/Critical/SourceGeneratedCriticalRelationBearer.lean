import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Power.GeneratedPower
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Lifecycle.AcceptedResponsibilityTransfer

/-!
# Source-generated bearer incidence for arbitrary critical relations

An actual `ActionPowerOverAt` already carries the exact relation seed,
beneficiary, controller action, phase and actionable-freedom change in one
ProcessGame occurrence.  This file adds the minimal cross-domain seam needed
by ordinary exit: a source law may witness that this exact generated relation
has one `Lifecycle.ActorBearer` lineage.

`BearerLineageAt` is deliberately supplied as a dependent source-law family,
not as a total actor map, registry or equality.  The carrier is indexed by the
original power, so it cannot replace the relation compiler, action compiler,
actors, relation or change kind.  `generate` is a generic transporter; an
authoritative domain producer must generate its lineage incidence internally.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Power

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations

universe u v wa wc x y b

variable {Source : Type u} {State : Type v}
variable {occurrenceOf : Source → RootedAccountedUnfolding State}
variable {game : SaturationMonoid.ProcessGame occurrenceOf}
variable {affectedFace : M0BoundaryFace.{u, v, wa} occurrenceOf}
variable {controllerFace : M0BoundaryFace.{u, v, wc} occurrenceOf}

/-- Minimal bearer carrier over one already generated critical power.  It
does not inspect or constrain `freedomChange.kind`; lost, restored and
redirected powers share the same interface. -/
structure SourceGeneratedCriticalRelationBearerAt
    (relationCompiler : SourceOwnedRelationRoleCompiler.{u, v, wa, x}
      occurrenceOf game affectedFace)
    (controllerCompiler : SourceOwnedActionControllerCompiler.{u, v, wc, y}
      game controllerFace)
    [Zero (relationCompiler.Phase game.source)]
    (controller : controllerCompiler.Actor)
    (affected : relationCompiler.Actor)
    (relation : relationCompiler.GeneratedRelation)
    (power : ActionPowerOverAt relationCompiler controllerCompiler
      controller affected relation)
    (BearerLineageAt : relationCompiler.GeneratedRelation →
      Lifecycle.ActorBearer → Type b) : Type (max x y b) where
  private mk ::
  commonBearer : Lifecycle.ActorBearer
  bearerLineage : BearerLineageAt relation commonBearer

namespace SourceGeneratedCriticalRelationBearerAt

variable
    {relationCompiler : SourceOwnedRelationRoleCompiler.{u, v, wa, x}
      occurrenceOf game affectedFace}
    {controllerCompiler : SourceOwnedActionControllerCompiler.{u, v, wc, y}
      game controllerFace}
    [Zero (relationCompiler.Phase game.source)]
    {controller : controllerCompiler.Actor}
    {affected : relationCompiler.Actor}
    {relation : relationCompiler.GeneratedRelation}
    {power : ActionPowerOverAt relationCompiler controllerCompiler
      controller affected relation}
    {BearerLineageAt : relationCompiler.GeneratedRelation →
      Lifecycle.ActorBearer → Type b}

/-- Generic transporter from one source-law incidence.  Root producers must
not expose these two arguments as their public mouth. -/
def generate
    (commonBearer : Lifecycle.ActorBearer)
    (lineage : BearerLineageAt relation commonBearer) :
    SourceGeneratedCriticalRelationBearerAt relationCompiler
      controllerCompiler controller affected relation power BearerLineageAt :=
  ⟨commonBearer, lineage⟩

/-- The carrier preserves the relation/beneficiary occurrence provenance of
the exact indexed power. -/
theorem exact_relation_provenance
    (_carrier : SourceGeneratedCriticalRelationBearerAt relationCompiler
      controllerCompiler controller affected relation power BearerLineageAt) :
    ∃ seed : relationCompiler.ExactRelationSeed,
      (∃ state ∈ game.occurrence.trace,
        state = affectedFace.state game.source ∧
        relationCompiler.relationSeedAt game.source state seed.1 ∧
        affectedFace.SeedAt game.source state
          (relationCompiler.beneficiaryActorSeed seed.1)) ∧
      seed.actor relationCompiler = affected ∧
      relationCompiler.relationOf seed = relation :=
  power.interest_exact_state_provenance

/-- The independent controller action remains the exact action of the same
indexed power. -/
theorem exact_controller_provenance
    (_carrier : SourceGeneratedCriticalRelationBearerAt relationCompiler
      controllerCompiler controller affected relation power BearerLineageAt) :
    ∃ state ∈ game.occurrence.trace,
      state = controllerCompiler.actionState game.source ∧
        controllerCompiler.actionAdmittedAt power.action.1 :=
  power.controller_exact_state_provenance

end SourceGeneratedCriticalRelationBearerAt

end Power
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.Power.SourceGeneratedCriticalRelationBearerAt.generate
#print axioms SaturationMonoid.ProcessGame.Society.Power.SourceGeneratedCriticalRelationBearerAt.exact_relation_provenance
#print axioms SaturationMonoid.ProcessGame.Society.Power.SourceGeneratedCriticalRelationBearerAt.exact_controller_provenance
