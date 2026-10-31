import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.UBIExitCapacityFixture

/-!
# M14 essential-access relation fixture

Tenure, health, and platform are exact relation seeds admitted at the existing
M1 lifecycle occurrence.  Their lineages generate distinct actors, phases,
and target roles through the standard relation compiler.  No sector label is
read from an observer and no actor, sector, property, or provider registry is
introduced.

The tenure actor is definitionally the existing M3 accepting counterparty for
the UBI payment.  Thus the pre-emitter UBI disposition can carry its generated
payment-purpose authority in the existing payload without creating another
projection, root, or occurrence.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14EssentialAccessRelationFixture

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Power Exchange Settlement Price Money UBI
open Lifecycle.Universal.FixedAdapter
open M3FiniteExchangeFixture M3ExchangeSettlementPriceRegression
open M14UBIExitCapacityFixture

inductive EssentialAccessEvent where
  | tenure
  | health
  | platform
  deriving DecidableEq, Repr

inductive EssentialAccessSector where
  | idle
  | tenure
  | health
  | platform
  deriving DecidableEq, Repr

instance : Zero EssentialAccessSector := ⟨.idle⟩

inductive EssentialAccessRole where
  | provider
  | tenureProvider
  | healthProvider
  | platformProvider
  deriving DecidableEq, Repr

def essentialAccessSeedAt (_source : Unit) (state : Lifecycle.EventState)
    (_event : EssentialAccessEvent) : Prop :=
  state = .after

def essentialAccessRelationCompiler : SourceOwnedRelationRoleCompiler
    Lifecycle.actualEventOccurrenceOf Lifecycle.actualEventGame targetFace where
  RelationSeed := EssentialAccessEvent
  RelationLineage := fun _ => EssentialAccessEvent
  relationSeedAt := essentialAccessSeedAt
  relationLineageOf := fun _ seed => seed.1
  beneficiaryActorSeed := fun event =>
    match event with
    | .tenure => .t1
    | .health => .t2
    | .platform => .t3
  beneficiaryActor_active := by
    intro _source _state event admitted
    exact admitted
  Role := fun _ => EssentialAccessRole
  Phase := fun _ => EssentialAccessSector
  sourceRoleOf := fun _ _ => .provider
  phaseStepOf := fun _ lineage =>
    match lineage with
    | .tenure => .tenure
    | .health => .health
    | .platform => .platform
  advanceRole := fun _ phase _role =>
    match phase with
    | .idle => .provider
    | .tenure => .tenureProvider
    | .health => .healthProvider
    | .platform => .platformProvider
  FutureCode := EssentialAccessEvent
  futureCodeDecidableEq := inferInstance
  futureCodeCarrier := {.tenure, .health, .platform}
  futureIdle := fun _ => False
  FutureContinuationAt := fun lineage side code =>
    if lineage = code ∧ side = .source then PUnit else PEmpty
  futureBoundaryState := fun _ _ => .after
  futureBoundaryState_mem := by
    intro _lineage _side
    change Lifecycle.EventState.after ∈
      [Lifecycle.EventState.before, Lifecycle.EventState.after]
    simp
  FutureContinuationWitnessAt := fun _ _ _ _ => True
  futureContinuation_witnessed := by
    intro _lineage _side _code _continuation
    trivial

instance essentialAccessRelationPhaseZero :
    Zero (essentialAccessRelationCompiler.Phase
      Lifecycle.actualEventGame.source) := by
  change Zero EssentialAccessSector
  infer_instance

def exactEssentialAccessSeed (event : EssentialAccessEvent) :
    essentialAccessRelationCompiler.ExactRelationSeed :=
  ⟨event, .after, by
    change Lifecycle.EventState.after ∈
      [Lifecycle.EventState.before, Lifecycle.EventState.after]
    simp, rfl⟩

def tenureActor : essentialAccessRelationCompiler.Actor :=
  (exactEssentialAccessSeed .tenure).actor essentialAccessRelationCompiler

def healthActor : essentialAccessRelationCompiler.Actor :=
  (exactEssentialAccessSeed .health).actor essentialAccessRelationCompiler

def platformActor : essentialAccessRelationCompiler.Actor :=
  (exactEssentialAccessSeed .platform).actor essentialAccessRelationCompiler

def tenureRelation : essentialAccessRelationCompiler.GeneratedRelation :=
  essentialAccessRelationCompiler.relationOf (exactEssentialAccessSeed .tenure)

def healthRelation : essentialAccessRelationCompiler.GeneratedRelation :=
  essentialAccessRelationCompiler.relationOf (exactEssentialAccessSeed .health)

def platformRelation : essentialAccessRelationCompiler.GeneratedRelation :=
  essentialAccessRelationCompiler.relationOf
    (exactEssentialAccessSeed .platform)

theorem tenureInterest :
    essentialAccessRelationCompiler.GeneratedInterestAt
      tenureActor tenureRelation :=
  ⟨exactEssentialAccessSeed .tenure, rfl, rfl⟩

theorem healthInterest :
    essentialAccessRelationCompiler.GeneratedInterestAt
      healthActor healthRelation :=
  ⟨exactEssentialAccessSeed .health, rfl, rfl⟩

theorem platformInterest :
    essentialAccessRelationCompiler.GeneratedInterestAt
      platformActor platformRelation :=
  ⟨exactEssentialAccessSeed .platform, rfl, rfl⟩

/-! ## Exact tenure exit action and loss -/

/-- The existing relation event doubles as the action seed.  This adds no
second relation-kind or action registry. -/
def essentialAccessExitController : SourceOwnedActionControllerCompiler
    Lifecycle.actualEventGame targetFace where
  ActionSeed := EssentialAccessEvent
  actionAdmittedAt := fun action => action = .tenure
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

def exactTenureExitAction : essentialAccessExitController.ExactActionSeed :=
  ⟨.tenure, .after, by
    change Lifecycle.EventState.after ∈
      [Lifecycle.EventState.before, Lifecycle.EventState.after]
    simp, rfl, rfl⟩

def tenureExitControllerActor : essentialAccessExitController.Actor :=
  exactTenureExitAction.actor essentialAccessExitController

theorem essentialAccessCode_source_actionable
    (event : EssentialAccessEvent) :
    ActionableAt essentialAccessRelationCompiler.futureIdle
      (essentialAccessRelationCompiler.futureCodesAt
        (essentialAccessRelationCompiler.relationOf
          (exactEssentialAccessSeed event)) .source) event := by
  constructor
  · apply (essentialAccessRelationCompiler.mem_futureCodesAt_iff
      (essentialAccessRelationCompiler.relationOf
        (exactEssentialAccessSeed event)) .source event).mpr
    constructor
    · cases event <;>
        change _ ∈ ({.tenure, .health, .platform} :
          Finset EssentialAccessEvent) <;> simp
    · refine ⟨?_⟩
      change (if event = event ∧ EdgeSide.source = .source then
        PUnit else PEmpty)
      simp
      exact PUnit.unit
  · simp [essentialAccessRelationCompiler]

theorem essentialAccessCode_target_absent
    (event : EssentialAccessEvent) :
    event ∉ essentialAccessRelationCompiler.futureCodesAt
      (essentialAccessRelationCompiler.relationOf
        (exactEssentialAccessSeed event)) .target := by
  intro member
  have continuation :=
    (essentialAccessRelationCompiler.mem_futureCodesAt_iff
      (essentialAccessRelationCompiler.relationOf
        (exactEssentialAccessSeed event)) .target event).mp member |>.2
  rcases continuation with ⟨continuation⟩
  change (if event = event ∧ EdgeSide.target = .source then
    PUnit else PEmpty) at continuation
  simp at continuation
  exact nomatch continuation

theorem tenure_phase_nonzero :
    essentialAccessRelationCompiler.phaseStep tenureRelation ≠ 0 := by
  intro impossible
  cases impossible

def tenureExitFreedomLoss : ActionableFreedomChange
    essentialAccessRelationCompiler.futureIdle
    (essentialAccessRelationCompiler.futureCodesAt tenureRelation .source)
    (essentialAccessRelationCompiler.futureCodesAt tenureRelation .target) :=
  .lost .tenure (essentialAccessCode_source_actionable .tenure)
    (essentialAccessCode_target_absent .tenure)

/-- Genuine tenure action power in the exact M1 occurrence. -/
def tenureExitActionPower : ActionPowerOverAt essentialAccessRelationCompiler
    essentialAccessExitController tenureExitControllerActor tenureActor
      tenureRelation where
  action := exactTenureExitAction
  controller_exact := rfl
  constraint :=
    { interest := tenureInterest
      phase_nonzero := tenure_phase_nonzero }
  freedomChange := tenureExitFreedomLoss

/-- Existing generic loss interface, now inhabited by a nonemployment
relation without retyping it into the UBI compiler. -/
def tenureRelationLoss : SourceGeneratedEmploymentLossAt
    (occurrenceOf := Lifecycle.actualEventOccurrenceOf)
    (game := Lifecycle.actualEventGame)
    (core := Lifecycle.Universal.FixedAdapter.core)
    (controllerFace := Lifecycle.Universal.FixedAdapter.targetFace)
    (exitRelationCompiler := essentialAccessRelationCompiler)
    (employmentController := essentialAccessExitController)
    tenureExitControllerActor tenureActor tenureRelation where
  power := tenureExitActionPower
  lostCode := .tenure
  sourceActionable := essentialAccessCode_source_actionable .tenure
  targetAbsent := essentialAccessCode_target_absent .tenure
  freedomChange_eq := rfl

@[simp] theorem tenure_phase_is_generated :
    essentialAccessRelationCompiler.phaseStep tenureRelation = .tenure :=
  rfl

@[simp] theorem health_phase_is_generated :
    essentialAccessRelationCompiler.phaseStep healthRelation = .health :=
  rfl

@[simp] theorem platform_phase_is_generated :
    essentialAccessRelationCompiler.phaseStep platformRelation = .platform :=
  rfl

@[simp] theorem tenure_target_role_is_generated :
    essentialAccessRelationCompiler.roleAt tenureRelation .target =
      .tenureProvider :=
  rfl

@[simp] theorem health_target_role_is_generated :
    essentialAccessRelationCompiler.roleAt healthRelation .target =
      .healthProvider :=
  rfl

@[simp] theorem platform_target_role_is_generated :
    essentialAccessRelationCompiler.roleAt platformRelation .target =
      .platformProvider :=
  rfl

theorem tenure_actor_is_exact_payment_counterparty :
    tenureActor = exactCounterpartyActor exactResidualActivation := by
  apply Subtype.ext
  rfl

theorem tenure_health_actors_ne : tenureActor ≠ healthActor := by
  intro equality
  have values := congrArg Subtype.val equality
  cases values

theorem tenure_platform_actors_ne : tenureActor ≠ platformActor := by
  intro equality
  have values := congrArg Subtype.val equality
  cases values

theorem tenure_health_relations_ne : tenureRelation ≠ healthRelation := by
  intro equality
  have values := congrArg Subtype.val equality
  cases values

theorem tenure_platform_relations_ne : tenureRelation ≠ platformRelation := by
  intro equality
  have values := congrArg Subtype.val equality
  cases values

theorem tenure_health_phases_ne :
    essentialAccessRelationCompiler.phaseStep tenureRelation ≠
      essentialAccessRelationCompiler.phaseStep healthRelation := by
  rw [tenure_phase_is_generated, health_phase_is_generated]
  intro equality
  cases equality

theorem tenure_platform_phases_ne :
    essentialAccessRelationCompiler.phaseStep tenureRelation ≠
      essentialAccessRelationCompiler.phaseStep platformRelation := by
  rw [tenure_phase_is_generated, platform_phase_is_generated]
  intro equality
  cases equality

/-- The old protected-interest readout is too coarse to carry sector truth. -/
theorem tenure_health_protectedInterest_readouts_eq :
    exchangeLaw.protectedInterestOfActor tenureActor =
      exchangeLaw.protectedInterestOfActor healthActor :=
  rfl

theorem tenure_platform_protectedInterest_readouts_eq :
    exchangeLaw.protectedInterestOfActor tenureActor =
      exchangeLaw.protectedInterestOfActor platformActor :=
  rfl

end
end M14EssentialAccessRelationFixture
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14EssentialAccessRelationFixture.tenure_actor_is_exact_payment_counterparty
#print axioms SaturationMonoid.ProcessGame.Society.M14EssentialAccessRelationFixture.tenure_health_relations_ne
