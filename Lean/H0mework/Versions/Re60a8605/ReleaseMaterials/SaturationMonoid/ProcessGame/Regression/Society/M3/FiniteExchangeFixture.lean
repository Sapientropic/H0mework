import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Exchange.GeneratedExchange
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Lifecycle.Universal.FixedFixtureCore
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Lifecycle.AcceptedResponsibilityTransfer

/-!
# Four-leg direct fixture for universal native exchange

This fixture specializes the arbitrary finite-leg producer to four locally
generated legs.  It reuses the existing M1 lifecycle vocabulary and fixed
ProcessGame occurrence, while installing one process and one actor/
responsibility incidence.  It is an example consumer, not the scope of the
universal exchange theorem.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M3FiniteExchangeFixture

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Exchange
open Lifecycle.Universal.FixedAdapter

abbrev V := Lifecycle.LifecycleVocabulary

def sourceEventOfToken : Lifecycle.TargetToken → Lifecycle.EventState
  | .t0 | .t2 | .t4 => .before
  | .t1 | .t3 | .t5 => .after

def admissionPayload (token : Lifecycle.TargetToken) :
    NativeAdmissionPayload V where
  sourceEvent := sourceEventOfToken token
  content := ()
  residual := ()
  bearer := .target token
  beneficiary := ()
  scope := ()
  lineage := .debt
  anchor_scope_eq := rfl
  anchor_lineage_eq := rfl
  origin := .explicitCommitment ()
  authority := ()
  assumption := .accepted ()
  dischargeJurisdiction := ()

def admittedObligation (token : Lifecycle.TargetToken) :
    AdmittedObligation V :=
  (admissionPayload token).toObligation

/-- Existing responsibility grammar specialized to the four settlement
branches needed downstream. -/
inductive ReviewEvent (obligation : AdmittedObligation V) where
  | maintain
  | supersede
  | bearerRelease
  | fulfill

def reviewDisposition {obligation : AdmittedObligation V} :
    ReviewEvent obligation → BoundaryDisposition V obligation .after
  | .maintain => .carry (.maintained ())
  | .supersede =>
      .terminal (.superseded
        { successor := obligation
          incidence := ()
          lineage_eq := rfl
          anchorTransport := SourceAnchorTransport.refl _ })
  | .bearerRelease =>
      .bearerRelease (.capacityReleasedWithResidue () ())
  | .fulfill => .terminal (.final (.fulfilled ()))

structure ReopenLineageAt (archive : TerminalArchive V) : Type where
  anchorLineage : archive.obligation.lineage = .debt

def reopenPayload (archive : TerminalArchive V)
    (_event : ReopenLineageAt archive) : NativeReopenPayload V archive where
  sourceEvent := .after
  admission :=
    { sourceEvent := .after
      content := archive.obligation.content
      residual := archive.obligation.residual
      bearer := archive.obligation.bearer
      beneficiary := archive.obligation.beneficiary
      scope := archive.obligation.scope
      lineage := archive.obligation.lineage
      anchor_scope_eq := rfl
      anchor_lineage_eq := _event.anchorLineage
      origin := .explicitCommitment ()
      authority := ()
      assumption := .accepted ()
      dischargeJurisdiction := archive.obligation.dischargeJurisdiction }
  source_eq := rfl
  incidence := ()
  lineage_eq := rfl
  anchorTransport := SourceAnchorTransport.refl _

/-- One installed process admits any generated target token and fulfills any
live obligation only when a later boundary event is actually activated. -/
def process : NativeResponsibilityProcess V where
  AdmissionEvent := Lifecycle.TargetToken
  admissionPayload := admissionPayload
  BoundaryEvent := ReviewEvent
  boundarySource := fun _ => .after
  boundary_anchor_eq := by
    intro obligation event
    rfl
  boundary_incidence_eq := by
    intro obligation event
    rfl
  boundaryDisposition := reviewDisposition
  ReopenEvent := ReopenLineageAt
  reopenPayload := fun {_} event => reopenPayload _ event

abbrev P := process

def incidenceCompiler : ActorResponsibilityIncidenceCompiler core V where
  SourceSeed := Empty
  sourceAdmittedAt := fun seed => nomatch seed
  sourceActorSeed := fun seed => nomatch seed
  sourceActor_active := by
    intro seed
    exact nomatch seed
  sourceObligation := fun seed => nomatch seed
  sourceEvent := fun seed => nomatch seed
  TargetSeed := Lifecycle.TargetToken
  targetAdmittedAt := fun _ => True
  targetActorSeed := id
  targetActor_active := by
    intro seed admitted
    rfl
  targetObligation := admittedObligation
  targetEvent := sourceEventOfToken
  HistoricalSeed := Empty
  historicalAdmittedAt := fun seed => nomatch seed
  historicalActorSeed := fun seed => nomatch seed
  historicalActorState := fun seed => nomatch seed
  historicalActor_active := by
    intro seed
    exact nomatch seed
  historicalObligation := fun seed => nomatch seed
  historicalEvent := fun seed => nomatch seed

def incidence : ActorResponsibilityIncidence core V where
  compiler := incidenceCompiler
  source_actor_unique := by
    intro obligation sourceEvent first last firstAt
    exact nomatch firstAt.seed.1
  target_actor_unique := by
    intro obligation sourceEvent first last firstAt lastAt
    calc
      first = firstAt.seed.actor incidenceCompiler := firstAt.actor_eq.symm
      _ = lastAt.seed.actor incidenceCompiler := by
        apply Subtype.ext
        have obligationsEq :=
          firstAt.obligation_eq.trans lastAt.obligation_eq.symm
        have bearersEq := congrArg AdmittedObligation.bearer obligationsEq
        change ActorBearer.target firstAt.seed.1 =
          ActorBearer.target lastAt.seed.1 at bearersEq
        exact ActorBearer.target.inj bearersEq
      _ = last := lastAt.actor_eq
  historical_actor_unique := by
    intro obligation sourceEvent first last firstAt
    exact nomatch firstAt.seed.1

def relationSeedAt (_source : Unit) (state : Lifecycle.EventState)
    (_seed : Lifecycle.TargetToken) : Prop :=
  state = .after

abbrev relationCompiler : SourceOwnedRelationRoleCompiler
    Lifecycle.actualEventOccurrenceOf Lifecycle.actualEventGame targetFace where
  RelationSeed := Lifecycle.TargetToken
  RelationLineage := fun _ => Lifecycle.TargetToken
  relationSeedAt := relationSeedAt
  relationLineageOf := fun _ seed => seed.1
  beneficiaryActorSeed := id
  beneficiaryActor_active := by
    intro source state seed active
    exact active
  Role := fun _ => Unit
  Phase := fun _ => Unit
  sourceRoleOf := fun _ _ => ()
  phaseStepOf := fun _ _ => ()
  advanceRole := fun _ _ _ => ()
  FutureCode := Empty
  futureCodeDecidableEq := inferInstance
  futureCodeCarrier := ∅
  futureIdle := fun code => nomatch code
  FutureContinuationAt := fun _ _ _ => Empty
  futureBoundaryState := fun _ _ => .after
  futureBoundaryState_mem := by
    intro lineage side
    simp [Lifecycle.actualEventOccurrenceOf]
  FutureContinuationWitnessAt := fun _ _ _ _ => False
  futureContinuation_witnessed := by
    intro lineage side code continuation
    exact nomatch continuation

/-- Four legs are local to one exchange seed; they are not a party registry. -/
inductive Leg where
  | a
  | b
  | c
  | d
  deriving DecidableEq, Repr

def legToken : Leg → Lifecycle.TargetToken
  | .a => .t0
  | .b => .t1
  | .c => .t2
  | .d => .t3

def counterparty : Leg → Leg
  | .a => .b
  | .b => .a
  | .c => .d
  | .d => .c

def exchangeCompiler : SourceOwnedExchangeCompiler core V P incidence
    relationCompiler where
  ExchangeSeed := Unit
  exchangeAdmittedAt := fun _ => True
  Leg := fun _ => Leg
  legDecidableEq := fun _ => inferInstance
  legs := fun _ => [.a, .b, .c, .d]
  legs_nodup := by
    intro seed
    decide
  leg_mem := by
    intro seed leg
    cases leg <;> simp
  principalLeg := fun _ => .a
  counterparty := fun _ => counterparty
  counterparty_involutive := by
    intro seed leg
    cases leg <;> rfl
  counterparty_ne := by
    intro seed leg
    cases leg <;> decide
  relationSeed := fun _ leg => legToken leg
  relationSeed_active := by
    intro seed leg admitted
    rfl
  responsibilitySeed := fun _ leg => legToken leg
  responsibilitySeed_active := by
    intro seed leg admitted
    trivial
  admissionEvent := fun _ leg => legToken leg
  sourceState := fun _ =>
    NativeResponsibilityProcess.GeneratedState.initial P
  parentStateOf := fun _ => .after

def exactExchangeSeed : exchangeCompiler.ExactExchangeSeed :=
  ⟨(), .after, by simp [Lifecycle.actualEventOccurrenceOf], rfl, trivial⟩

@[simp] theorem exactCounterparty
    (seed : exchangeCompiler.ExactExchangeSeed) (leg : seed.Leg) :
    seed.counterparty exchangeCompiler leg = counterparty leg :=
  rfl

@[simp] theorem exactSourceEvent
    (seed : exchangeCompiler.ExactExchangeSeed) (leg : seed.Leg) :
    seed.sourceEvent exchangeCompiler leg =
      sourceEventOfToken (legToken leg) :=
  rfl

def exchangeLaw : SourceOwnedExchangeLaw core V P incidence
    relationCompiler where
  compiler := exchangeCompiler
  bearerOfActor := fun actor => .target actor.1
  protectedInterestOfActor := fun _ => ()
  actorSeed_eq := by
    intro seed leg
    rfl
  obligation_eq := by
    intro seed leg
    rfl
  sourceEvent_eq := by
    intro seed leg
    rfl
  bearer_eq := by
    intro seed leg
    rfl
  beneficiary_eq := by
    intro seed leg
    rfl
  restriction_parent_state_eq := by
    intro seed leg
    rfl
  sourceEvents_ne := by
    intro seed leg
    rw [exactSourceEvent seed leg,
      exactSourceEvent seed (seed.counterparty exchangeCompiler leg),
      exactCounterparty seed leg]
    cases leg <;> intro impossible <;> cases impossible
  counterpartyActors_ne := by
    intro seed leg equal
    have values := congrArg Subtype.val equal
    cases leg <;> cases values

def generatedExchange : exchangeLaw.GeneratedExchange :=
  exchangeLaw.exchangeOf exactExchangeSeed

theorem four_leg_native_reciprocity :
    ∀ leg : exactExchangeSeed.Leg,
      relationCompiler.GeneratedInterestAt
          (exactExchangeSeed.actor exchangeCompiler leg)
          (exactExchangeSeed.relation exchangeCompiler leg) ∧
        Nonempty (incidence.TargetResponsibilityAt
          (exactExchangeSeed.actor exchangeCompiler leg)
          (exactExchangeSeed.obligation exchangeCompiler leg)
          (exactExchangeSeed.sourceEvent exchangeCompiler leg)) ∧
        Nonempty (SourceOwnsResponsibilityIncidence V
          (exactExchangeSeed.sourceEvent exchangeCompiler leg)
          (exactExchangeSeed.obligation exchangeCompiler leg)) ∧
        (exactExchangeSeed.obligation exchangeCompiler leg).bearer =
          exchangeLaw.bearerOfActor
            (exactExchangeSeed.actor exchangeCompiler leg) ∧
        (exactExchangeSeed.obligation exchangeCompiler leg).beneficiary =
          exchangeLaw.protectedInterestOfActor
            (exactExchangeSeed.actor exchangeCompiler
              (exactExchangeSeed.counterparty exchangeCompiler leg)) := by
  intro leg
  exact exchangeLaw.native_reciprocity exactExchangeSeed leg

structure ExactCounterpartyProvenanceAt
    (leg : exactExchangeSeed.Leg) : Prop where
  actors_ne :
    exactExchangeSeed.actor exchangeCompiler leg ≠
      exactExchangeSeed.actor exchangeCompiler
        (exactExchangeSeed.counterparty exchangeCompiler leg)
  restrictions_ne :
    exactExchangeSeed.sourceEvent exchangeCompiler leg ≠
      exactExchangeSeed.sourceEvent exchangeCompiler
        (exactExchangeSeed.counterparty exchangeCompiler leg)
  shared_exact_parent :
    ∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
      state = core.targetFace.state Lifecycle.actualEventGame.source ∧
      exchangeCompiler.exchangeAdmittedAt exactExchangeSeed.1 ∧
      exchangeCompiler.parentStateOf
          (exactExchangeSeed.sourceEvent exchangeCompiler leg) = state ∧
      exchangeCompiler.parentStateOf
          (exactExchangeSeed.sourceEvent exchangeCompiler
            (exactExchangeSeed.counterparty exchangeCompiler leg)) = state ∧
      exactExchangeSeed.sourceEvent exchangeCompiler leg ≠
        exactExchangeSeed.sourceEvent exchangeCompiler
          (exactExchangeSeed.counterparty exchangeCompiler leg)

theorem four_leg_counterparty_exact_provenance
    (leg : exactExchangeSeed.Leg) : ExactCounterpartyProvenanceAt leg where
  actors_ne := exchangeLaw.counterparty_actors_distinct exactExchangeSeed leg
  restrictions_ne :=
    exchangeLaw.counterparty_restrictions_distinct exactExchangeSeed leg
  shared_exact_parent :=
    exchangeLaw.counterparty_restrictions_share_exact_parent_state
      exactExchangeSeed leg

theorem fixture_has_more_than_binary_scope :
    (exactExchangeSeed.legList exchangeCompiler).length = 4 :=
  rfl

theorem counterparty_slots_are_distinct :
    ∀ leg : exactExchangeSeed.Leg,
      exactExchangeSeed.obligationSlotIndex exchangeCompiler
          (exactExchangeSeed.counterparty exchangeCompiler leg) ≠
        exactExchangeSeed.obligationSlotIndex exchangeCompiler leg :=
  by
    intro leg
    exact exactExchangeSeed.counterparty_slot_ne exchangeCompiler leg

end M3FiniteExchangeFixture
end Society
end ProcessGame
end SaturationMonoid
