import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Power.Critical.SourceGeneratedCriticalRelationBearer
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccessRelationFixture

/-!
# Source-generated essential-access critical actions

Every existing essential-access relation seed also generates one exact actual
action controller restricted to that same event.  The relation compiler,
relation actor and future grammar remain the existing fixture objects; this
file adds no relation compiler, actor registry or action table.

For tenure, health and platform, the exact action produces a nonzero relation
phase and a genuine `.lost event` freedom change.  The critical bearer is the
existing exchange-law bearer of the generated relation actor.  In particular,
health remains the `.t2` actor/bearer and is never equated with `.t1`.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedEssentialAccessCriticalAction

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Power Exchange Settlement Price Money UBI
open Lifecycle.Universal.FixedAdapter
open M3FiniteExchangeFixture M3ExchangeSettlementPriceRegression
open M14EssentialAccessRelationFixture

/-! ## Event-indexed source action controller -/

/-- The controller reuses `EssentialAccessEvent` as its action seed and admits
only the event selected by its index. -/
def essentialAccessCriticalActionController
    (event : EssentialAccessEvent) : SourceOwnedActionControllerCompiler
      Lifecycle.actualEventGame targetFace where
  ActionSeed := EssentialAccessEvent
  actionAdmittedAt := fun action => action = event
  actionState := fun _ => .after
  actionState_mem := by
    change Lifecycle.EventState.after ∈
      [Lifecycle.EventState.before, Lifecycle.EventState.after]
    simp
  actorState_mem := by
    change Lifecycle.EventState.after ∈
      [Lifecycle.EventState.before, Lifecycle.EventState.after]
    simp
  actorSeed := fun _ => .t0
  actorSeed_active := by
    intro _action _admitted
    rfl

def exactEssentialAccessCriticalAction
    (event : EssentialAccessEvent) :
    (essentialAccessCriticalActionController event).ExactActionSeed :=
  ⟨event, .after, by
    change Lifecycle.EventState.after ∈
      [Lifecycle.EventState.before, Lifecycle.EventState.after]
    simp, rfl, rfl⟩

def essentialAccessCriticalControllerActor
    (event : EssentialAccessEvent) :
    (essentialAccessCriticalActionController event).Actor :=
  (exactEssentialAccessCriticalAction event).actor
    (essentialAccessCriticalActionController event)

/-- Relation actor and relation are projections of the existing exact
relation seed, not a copied actor/relation registry. -/
def essentialAccessCriticalActor (event : EssentialAccessEvent) :
    essentialAccessRelationCompiler.Actor :=
  (exactEssentialAccessSeed event).actor essentialAccessRelationCompiler

def essentialAccessCriticalRelation (event : EssentialAccessEvent) :
    essentialAccessRelationCompiler.GeneratedRelation :=
  essentialAccessRelationCompiler.relationOf
    (exactEssentialAccessSeed event)

theorem essentialAccessCriticalInterest (event : EssentialAccessEvent) :
    essentialAccessRelationCompiler.GeneratedInterestAt
      (essentialAccessCriticalActor event)
      (essentialAccessCriticalRelation event) :=
  ⟨exactEssentialAccessSeed event, rfl, rfl⟩

theorem essentialAccessCriticalPhase_nonzero
    (event : EssentialAccessEvent) :
    essentialAccessRelationCompiler.phaseStep
        (essentialAccessCriticalRelation event) ≠ 0 := by
  cases event <;> intro impossible <;> cases impossible

/-! ## Exact lost power and generic loss mouth -/

def essentialAccessCriticalFreedomLoss (event : EssentialAccessEvent) :
    ActionableFreedomChange essentialAccessRelationCompiler.futureIdle
      (essentialAccessRelationCompiler.futureCodesAt
        (essentialAccessCriticalRelation event) .source)
      (essentialAccessRelationCompiler.futureCodesAt
        (essentialAccessCriticalRelation event) .target) :=
  .lost event (essentialAccessCode_source_actionable event)
    (essentialAccessCode_target_absent event)

def essentialAccessCriticalActionPower (event : EssentialAccessEvent) :
    ActionPowerOverAt essentialAccessRelationCompiler
      (essentialAccessCriticalActionController event)
      (essentialAccessCriticalControllerActor event)
      (essentialAccessCriticalActor event)
      (essentialAccessCriticalRelation event) where
  action := exactEssentialAccessCriticalAction event
  controller_exact := rfl
  constraint :=
    { interest := essentialAccessCriticalInterest event
      phase_nonzero := essentialAccessCriticalPhase_nonzero event }
  freedomChange := essentialAccessCriticalFreedomLoss event

/-- Existing generic exact-loss mouth specialized to an arbitrary
essential-access event. -/
def essentialAccessCriticalRelationLoss (event : EssentialAccessEvent) :
    SourceGeneratedEmploymentLossAt
      (occurrenceOf := Lifecycle.actualEventOccurrenceOf)
      (game := Lifecycle.actualEventGame)
      (core := Lifecycle.Universal.FixedAdapter.core)
      (controllerFace := Lifecycle.Universal.FixedAdapter.targetFace)
      (exitRelationCompiler := essentialAccessRelationCompiler)
      (employmentController := essentialAccessCriticalActionController event)
      (essentialAccessCriticalControllerActor event)
      (essentialAccessCriticalActor event)
      (essentialAccessCriticalRelation event) where
  power := essentialAccessCriticalActionPower event
  lostCode := event
  sourceActionable := essentialAccessCode_source_actionable event
  targetAbsent := essentialAccessCode_target_absent event
  freedomChange_eq := rfl

/-! ## Source-generated critical bearer -/

/-- Proof-relevant bearer lineage generated from an exact existing relation
seed.  It is an open dependent family over relation/bearer, not an event or
actor registry. -/
structure EssentialAccessCriticalBearerLineageAt
    (relation : essentialAccessRelationCompiler.GeneratedRelation)
    (bearer : Lifecycle.ActorBearer) : Type where
  seed : essentialAccessRelationCompiler.ExactRelationSeed
  relationExact : essentialAccessRelationCompiler.relationOf seed = relation
  bearerExact : exchangeLaw.bearerOfActor
    (seed.actor essentialAccessRelationCompiler) = bearer

def essentialAccessCriticalBearerLineage (event : EssentialAccessEvent) :
    EssentialAccessCriticalBearerLineageAt
      (essentialAccessCriticalRelation event)
      (exchangeLaw.bearerOfActor (essentialAccessCriticalActor event)) :=
  { seed := exactEssentialAccessSeed event
    relationExact := rfl
    bearerExact := rfl }

abbrev EssentialAccessCriticalRelationBearerAt
    (event : EssentialAccessEvent) :=
  SourceGeneratedCriticalRelationBearerAt
    essentialAccessRelationCompiler
    (essentialAccessCriticalActionController event)
    (essentialAccessCriticalControllerActor event)
    (essentialAccessCriticalActor event)
    (essentialAccessCriticalRelation event)
    (essentialAccessCriticalActionPower event)
    EssentialAccessCriticalBearerLineageAt

def essentialAccessCriticalRelationBearer
    (event : EssentialAccessEvent) :
    EssentialAccessCriticalRelationBearerAt event :=
  SourceGeneratedCriticalRelationBearerAt.generate
    (exchangeLaw.bearerOfActor (essentialAccessCriticalActor event))
    (essentialAccessCriticalBearerLineage event)

/-- Compact zero-choice carrier.  Both fields are generated from `event`; no
action, actor, relation, power, bearer or target is accepted at the mouth. -/
structure SourceGeneratedEssentialAccessCriticalActionAt
    (event : EssentialAccessEvent) : Type where
  private mk ::
  loss : SourceGeneratedEmploymentLossAt
    (occurrenceOf := Lifecycle.actualEventOccurrenceOf)
    (game := Lifecycle.actualEventGame)
    (core := Lifecycle.Universal.FixedAdapter.core)
    (controllerFace := Lifecycle.Universal.FixedAdapter.targetFace)
    (exitRelationCompiler := essentialAccessRelationCompiler)
    (employmentController := essentialAccessCriticalActionController event)
    (essentialAccessCriticalControllerActor event)
    (essentialAccessCriticalActor event)
    (essentialAccessCriticalRelation event)
  lossExact : loss = essentialAccessCriticalRelationLoss event
  criticalBearer : EssentialAccessCriticalRelationBearerAt event
  criticalBearerExact : criticalBearer =
    essentialAccessCriticalRelationBearer event

def sourceGeneratedEssentialAccessCriticalActionAt
    (event : EssentialAccessEvent) :
    SourceGeneratedEssentialAccessCriticalActionAt event :=
  { loss := essentialAccessCriticalRelationLoss event
    lossExact := rfl
    criticalBearer := essentialAccessCriticalRelationBearer event
    criticalBearerExact := rfl }

/-! ## Generic direct consumers -/

theorem everyEssentialAccessEvent_generatesCriticalAction :
    ∀ event : EssentialAccessEvent,
      Nonempty (SourceGeneratedEssentialAccessCriticalActionAt event) :=
  fun event => ⟨sourceGeneratedEssentialAccessCriticalActionAt event⟩

theorem essentialAccessCriticalAction_exact_relation_provenance
    (event : EssentialAccessEvent) :
    ∃ seed : essentialAccessRelationCompiler.ExactRelationSeed,
      (∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
        state = targetFace.state Lifecycle.actualEventGame.source ∧
        essentialAccessRelationCompiler.relationSeedAt
          Lifecycle.actualEventGame.source state seed.1 ∧
        targetFace.SeedAt Lifecycle.actualEventGame.source state
          (essentialAccessRelationCompiler.beneficiaryActorSeed seed.1)) ∧
      seed.actor essentialAccessRelationCompiler =
        essentialAccessCriticalActor event ∧
      essentialAccessRelationCompiler.relationOf seed =
        essentialAccessCriticalRelation event :=
  SourceGeneratedCriticalRelationBearerAt.exact_relation_provenance
    (essentialAccessCriticalRelationBearer event)

theorem essentialAccessCriticalAction_exact_controller_provenance
    (event : EssentialAccessEvent) :
    ∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
      state = (essentialAccessCriticalActionController event).actionState
          Lifecycle.actualEventGame.source ∧
      (essentialAccessCriticalActionController event).actionAdmittedAt
        (essentialAccessCriticalActionPower event).action.1 :=
  SourceGeneratedCriticalRelationBearerAt.exact_controller_provenance
    (essentialAccessCriticalRelationBearer event)

/-! ## Health specialization -/

def sourceGeneratedHealthCriticalAction :
    SourceGeneratedEssentialAccessCriticalActionAt .health :=
  sourceGeneratedEssentialAccessCriticalActionAt .health

@[simp] theorem healthCriticalAction_action_exact :
    sourceGeneratedHealthCriticalAction.loss.power.action.1 =
      EssentialAccessEvent.health :=
  rfl

@[simp] theorem healthCriticalAction_actor_exact :
    essentialAccessCriticalActor .health = healthActor :=
  rfl

@[simp] theorem healthCriticalAction_relation_exact :
    essentialAccessCriticalRelation .health = healthRelation :=
  rfl

@[simp] theorem healthCriticalAction_phase_exact :
    essentialAccessRelationCompiler.phaseStep
      (essentialAccessCriticalRelation .health) = .health :=
  rfl

@[simp] theorem healthCriticalAction_targetRole_exact :
    essentialAccessRelationCompiler.roleAt
      (essentialAccessCriticalRelation .health) .target = .healthProvider :=
  rfl

theorem healthCriticalAction_sourceActionable :
    ActionableAt essentialAccessRelationCompiler.futureIdle
      (essentialAccessRelationCompiler.futureCodesAt
        (essentialAccessCriticalRelation .health) .source) .health :=
  essentialAccessCode_source_actionable .health

theorem healthCriticalAction_targetAbsent :
    EssentialAccessEvent.health ∉
      essentialAccessRelationCompiler.futureCodesAt
        (essentialAccessCriticalRelation .health) .target :=
  essentialAccessCode_target_absent .health

@[simp] theorem healthCriticalAction_freedomLoss_exact :
    sourceGeneratedHealthCriticalAction.loss.power.freedomChange =
      .lost .health healthCriticalAction_sourceActionable
        healthCriticalAction_targetAbsent :=
  rfl

@[simp] theorem healthCriticalAction_commonBearer_exact :
    sourceGeneratedHealthCriticalAction.criticalBearer.commonBearer =
      exchangeLaw.bearerOfActor healthActor :=
  rfl

theorem healthCriticalAction_exact_provenance :
    (∃ seed : essentialAccessRelationCompiler.ExactRelationSeed,
      (∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
        state = targetFace.state Lifecycle.actualEventGame.source ∧
        essentialAccessRelationCompiler.relationSeedAt
          Lifecycle.actualEventGame.source state seed.1 ∧
        targetFace.SeedAt Lifecycle.actualEventGame.source state
          (essentialAccessRelationCompiler.beneficiaryActorSeed seed.1)) ∧
      seed.actor essentialAccessRelationCompiler = healthActor ∧
      essentialAccessRelationCompiler.relationOf seed = healthRelation) ∧
    (∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
      state = (essentialAccessCriticalActionController .health).actionState
          Lifecycle.actualEventGame.source ∧
      (essentialAccessCriticalActionController .health).actionAdmittedAt
        sourceGeneratedHealthCriticalAction.loss.power.action.1) :=
  ⟨essentialAccessCriticalAction_exact_relation_provenance .health,
    essentialAccessCriticalAction_exact_controller_provenance .health⟩

/-! ## Exact mismatch controls -/

theorem essentialAccessCriticalController_rejects_mismatch
    {expected actual : EssentialAccessEvent}
    (different : actual ≠ expected) :
    ¬ (essentialAccessCriticalActionController expected).actionAdmittedAt
      actual :=
  different

theorem healthCriticalController_rejects_tenure :
    ¬ (essentialAccessCriticalActionController .health).actionAdmittedAt
      .tenure :=
  essentialAccessCriticalController_rejects_mismatch (by decide)

theorem healthCriticalController_rejects_platform :
    ¬ (essentialAccessCriticalActionController .health).actionAdmittedAt
      .platform :=
  essentialAccessCriticalController_rejects_mismatch (by decide)

theorem healthCriticalActor_ne_t1 :
    essentialAccessCriticalActor .health ≠ targetActor .t1 := by
  intro equality
  have values := congrArg Subtype.val equality
  cases values

theorem healthCriticalBearer_ne_t1 :
    exchangeLaw.bearerOfActor (essentialAccessCriticalActor .health) ≠
      Lifecycle.ActorBearer.target .t1 := by
  intro equality
  cases equality

theorem healthLostCodeTargetReplay_isEmpty :
    IsEmpty (ActionableAt essentialAccessRelationCompiler.futureIdle
      (essentialAccessRelationCompiler.futureCodesAt
        (essentialAccessCriticalRelation .health) .target) .health) :=
  ⟨fun replay => healthCriticalAction_targetAbsent replay.1⟩

theorem healthCriticalAction_hasNoCallerPayload : True := by
  fail_if_success exact sourceGeneratedHealthCriticalAction.actor
  fail_if_success exact sourceGeneratedHealthCriticalAction.relation
  fail_if_success exact sourceGeneratedHealthCriticalAction.bearer
  fail_if_success exact sourceGeneratedHealthCriticalAction.target
  fail_if_success exact sourceGeneratedHealthCriticalAction.registry
  fail_if_success exact sourceGeneratedHealthCriticalAction.future
  trivial

end
end M14SourceGeneratedEssentialAccessCriticalAction
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedEssentialAccessCriticalAction.essentialAccessCriticalActionPower
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedEssentialAccessCriticalAction.essentialAccessCriticalRelationBearer
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedEssentialAccessCriticalAction.everyEssentialAccessEvent_generatesCriticalAction
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedEssentialAccessCriticalAction.healthCriticalAction_exact_provenance
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedEssentialAccessCriticalAction.healthLostCodeTargetReplay_isEmpty
