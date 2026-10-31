import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Relations.GeneratedRelationRole
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Future.RelationIndexedFuture
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Power.ActionableFreedomChange
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Power.SourceOwnedActionController

/-!
# Generated constraint and action power

Constraint power is a nontrivial generated relation phase over an exact
generated interest.  Action power is strictly stronger: in the same source
occurrence it aligns that relation with an exact action-controller seed and a
genuine actionable-freedom change on one common code carrier.

This separation prevents a constraint-bearer handoff, payoff difference,
closure gain or search branch from being promoted to actual action authority.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Power

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations

universe u v wa wc x y

variable {Source : Type u} {State : Type v}
variable {occurrenceOf : Source → RootedAccountedUnfolding State}
variable {game : SaturationMonoid.ProcessGame occurrenceOf}
variable {affectedFace : M0BoundaryFace.{u, v, wa} occurrenceOf}
variable {controllerFace : M0BoundaryFace.{u, v, wc} occurrenceOf}

/-- A generated relation constrains its generated beneficiary exactly when
its lineage phase is nontrivial.  This mouth deliberately carries no claim
about the actual event controller. -/
structure ConstraintPowerOverAt
    (relationCompiler : SourceOwnedRelationRoleCompiler.{u, v, wa, x}
      occurrenceOf game affectedFace)
    [Zero (relationCompiler.Phase game.source)]
    (affected : relationCompiler.Actor)
    (relation : relationCompiler.GeneratedRelation) : Prop where
  interest : relationCompiler.GeneratedInterestAt affected relation
  phase_nonzero : relationCompiler.phaseStep relation ≠ 0

/-- Actual power exercise: exact controller + affected generated interest +
nontrivial relation phase + genuine actionable future change.  Both exact
seeds live in the same fixed `game.occurrence`; neither actor is a registry
lookup and the change kind is read from its witness. -/
structure ActionPowerOverAt
    (relationCompiler : SourceOwnedRelationRoleCompiler.{u, v, wa, x}
      occurrenceOf game affectedFace)
    (controllerCompiler : SourceOwnedActionControllerCompiler.{u, v, wc, y}
      game controllerFace)
    [Zero (relationCompiler.Phase game.source)]
    (controller : controllerCompiler.Actor)
    (affected : relationCompiler.Actor)
    (relation : relationCompiler.GeneratedRelation) : Type (max x y) where
  action : controllerCompiler.ExactActionSeed
  controller_exact : controllerCompiler.ControllerAt action controller
  constraint : ConstraintPowerOverAt relationCompiler affected relation
  freedomChange :
    ActionableFreedomChange relationCompiler.futureIdle
      (relationCompiler.futureCodesAt relation .source)
      (relationCompiler.futureCodesAt relation .target)

namespace ActionPowerOverAt

variable
    {relationCompiler : SourceOwnedRelationRoleCompiler.{u, v, wa, x}
      occurrenceOf game affectedFace}
    {controllerCompiler : SourceOwnedActionControllerCompiler.{u, v, wc, y}
      game controllerFace}
    [Zero (relationCompiler.Phase game.source)]
    {controller : controllerCompiler.Actor}
    {affected : relationCompiler.Actor}
    {relation : relationCompiler.GeneratedRelation}

/-- Action power always changes the generated actionable freedom fibre. -/
theorem freedom_ne
    (power : ActionPowerOverAt relationCompiler controllerCompiler
      controller affected relation) :
    relationCompiler.futureCodesAt relation .source ≠
      relationCompiler.futureCodesAt relation .target :=
  power.freedomChange.freedom_ne

/-- Action power exposes the exact relation-beneficiary seed rather than an
arbitrary protected-interest predicate. -/
theorem interest_exact_state_provenance
    (power : ActionPowerOverAt relationCompiler controllerCompiler
      controller affected relation) :
    ∃ seed : relationCompiler.ExactRelationSeed,
      (∃ state ∈ game.occurrence.trace,
        state = affectedFace.state game.source ∧
        relationCompiler.relationSeedAt game.source state seed.1 ∧
        affectedFace.SeedAt game.source state
          (relationCompiler.beneficiaryActorSeed seed.1)) ∧
      seed.actor relationCompiler = affected ∧
      relationCompiler.relationOf seed = relation :=
  power.constraint.interest.exact_state_provenance

/-- Action power exposes an independent exact action seed for the actual
controller; relation phase alone cannot manufacture this witness. -/
theorem controller_exact_state_provenance
    (power : ActionPowerOverAt relationCompiler controllerCompiler
      controller affected relation) :
    ∃ state ∈ game.occurrence.trace,
      state = controllerCompiler.actionState game.source ∧
        controllerCompiler.actionAdmittedAt power.action.1 :=
  controllerCompiler.controller_provenance power.controller_exact

end ActionPowerOverAt

/-- Search opportunity has a generated beneficiary and one actionable code,
but no exact action seed and hence no controller authority. -/
structure PowerOpportunityAt
    (relationCompiler : SourceOwnedRelationRoleCompiler.{u, v, wa, x}
      occurrenceOf game affectedFace)
    (affected : relationCompiler.Actor)
    (relation : relationCompiler.GeneratedRelation)
    (side : EdgeSide) : Type x where
  interest : relationCompiler.GeneratedInterestAt affected relation
  code : relationCompiler.FutureCode
  actionable : ActionableAt relationCompiler.futureIdle
    (relationCompiler.futureCodesAt relation side) code

/-- Every actual power exercise contains a search-side actionable witness,
while retaining the additional exact controller seed that the opportunity
mouth intentionally lacks. -/
def ActionPowerOverAt.toOpportunity
    {relationCompiler : SourceOwnedRelationRoleCompiler.{u, v, wa, x}
      occurrenceOf game affectedFace}
    {controllerCompiler : SourceOwnedActionControllerCompiler.{u, v, wc, y}
      game controllerFace}
    [Zero (relationCompiler.Phase game.source)]
    {controller : controllerCompiler.Actor}
    {affected : relationCompiler.Actor}
    {relation : relationCompiler.GeneratedRelation}
    (power : ActionPowerOverAt relationCompiler controllerCompiler
      controller affected relation) :
    (PowerOpportunityAt relationCompiler affected relation .source) ⊕
      (PowerOpportunityAt relationCompiler affected relation .target) := by
  cases power.freedomChange with
  | lost code sourceActionable targetAbsent =>
      exact Sum.inl ⟨power.constraint.interest, code, sourceActionable⟩
  | restored code sourceAbsent targetActionable =>
      exact Sum.inr ⟨power.constraint.interest, code, targetActionable⟩
  | redirected sourceCode targetCode sourceActionable sourceAbsent targetAbsent
      targetActionable =>
      exact Sum.inl ⟨power.constraint.interest, sourceCode, sourceActionable⟩

end Power
end Society
end ProcessGame
end SaturationMonoid
