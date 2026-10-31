import H0mework.Foundation.Agency.Installation
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Relations.GeneratedRelationRole

/-!
# Source-generated finite reciprocal exchange

One exact exchange seed generates its own finite family of legs.  Every leg
simultaneously generates a relation-beneficiary incidence, a target
actor/responsibility incidence, and an actual admission in the one installed
responsibility process.  A fixed-point-free involution generates the
counterparty leg; there is no global participant registry and no binary scope
hard-coded into the public producer.

The complete leg list is folded, in order, onto a compiler-generated prior
`GeneratedState`.  Each resulting obligation occurrence retains the exact
exchange seed, dependent leg, and stable slot at which it is live.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Exchange

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations

universe u v w x y z

variable {Source : Type u} {State : Type v}
variable {occurrenceOf : Source → RootedAccountedUnfolding State}
variable {game : SaturationMonoid.ProcessGame occurrenceOf}
variable {core : SourceOwnedLifecycleCore.{u, v, w} occurrenceOf game}
variable {V : Vocabulary.{x}}
variable {P : NativeResponsibilityProcess V}
variable {incidence : ActorResponsibilityIncidence core V}
variable
  {relationCompiler : SourceOwnedRelationRoleCompiler.{u, v, w, y}
    occurrenceOf game core.targetFace}

/-- Raw source-owned exchange compiler.  `Leg` is dependent on the exchange
seed, so parties are local products of one exchange occurrence rather than a
preinstalled actor carrier. -/
structure SourceOwnedExchangeCompiler
    (core : SourceOwnedLifecycleCore.{u, v, w} occurrenceOf game)
    (V : Vocabulary.{x}) (P : NativeResponsibilityProcess V)
    (incidence : ActorResponsibilityIncidence core V)
    (relationCompiler : SourceOwnedRelationRoleCompiler.{u, v, w, y}
      occurrenceOf game core.targetFace) where
  ExchangeSeed : Type z
  exchangeAdmittedAt : ExchangeSeed → Prop
  Leg : ExchangeSeed → Type z
  legDecidableEq : ∀ seed, DecidableEq (Leg seed)
  legs : ∀ seed, List (Leg seed)
  legs_nodup : ∀ seed, (legs seed).Nodup
  leg_mem : ∀ seed (leg : Leg seed), leg ∈ legs seed
  principalLeg : ∀ seed, Leg seed
  counterparty : ∀ seed, Leg seed → Leg seed
  counterparty_involutive : ∀ seed leg,
    counterparty seed (counterparty seed leg) = leg
  counterparty_ne : ∀ seed leg, counterparty seed leg ≠ leg
  relationSeed : ∀ seed, Leg seed → relationCompiler.RelationSeed
  relationSeed_active : ∀ seed (leg : Leg seed),
    exchangeAdmittedAt seed →
      relationCompiler.relationSeedAt game.source
        (core.targetFace.state game.source) (relationSeed seed leg)
  responsibilitySeed : ∀ seed, Leg seed → incidence.compiler.TargetSeed
  responsibilitySeed_active : ∀ seed (leg : Leg seed),
    exchangeAdmittedAt seed →
      incidence.compiler.targetAdmittedAt (responsibilitySeed seed leg)
  admissionEvent : ∀ seed, Leg seed → P.AdmissionEvent
  sourceState : ExchangeSeed → P.GeneratedState
  parentStateOf : V.SourceEvent → State

namespace SourceOwnedExchangeCompiler

variable
  (compiler : SourceOwnedExchangeCompiler.{u, v, w, x, y, z}
    core V P incidence relationCompiler)

local instance instLegDecidableEq (seed : compiler.ExchangeSeed) :
    DecidableEq (compiler.Leg seed) :=
  compiler.legDecidableEq seed

/-- Exchange seeds are admitted only at the exact target boundary state of
the fixed source occurrence. -/
def exchangeSeedAt
    (_source : Source) (state : State) (seed : compiler.ExchangeSeed) : Prop :=
  state = core.targetFace.state game.source ∧
    compiler.exchangeAdmittedAt seed

/-- The sole public producer input: one source-occurrence witnessed exchange
seed. -/
abbrev ExactExchangeSeed :=
  SourceSeed occurrenceOf compiler.ExchangeSeed compiler.exchangeSeedAt
    game.source

namespace ExactExchangeSeed

theorem admitted (seed : compiler.ExactExchangeSeed) :
    compiler.exchangeAdmittedAt seed.1 := by
  rcases seed.2 with ⟨state, _inTrace, _atTarget, admitted⟩
  exact admitted

theorem exact_state_provenance (seed : compiler.ExactExchangeSeed) :
    ∃ state ∈ game.occurrence.trace,
      state = core.targetFace.state game.source ∧
        compiler.exchangeAdmittedAt seed.1 := by
  rcases seed.2 with ⟨state, inTrace, atTarget, admitted⟩
  exact ⟨state, inTrace, atTarget, admitted⟩

abbrev Leg (seed : compiler.ExactExchangeSeed) := compiler.Leg seed.1

def legList (seed : compiler.ExactExchangeSeed) : List seed.Leg :=
  compiler.legs seed.1

theorem leg_mem (seed : compiler.ExactExchangeSeed) (leg : seed.Leg) :
    leg ∈ seed.legList compiler :=
  compiler.leg_mem seed.1 leg

theorem legList_nodup (seed : compiler.ExactExchangeSeed) :
    (seed.legList compiler).Nodup :=
  compiler.legs_nodup seed.1

/-- Exact exchange-local responsibility occurrence.  Its carrier is a leg
of this seed's generated finite family, not a global obligation registry. -/
def ObligationOccurrence (seed : compiler.ExactExchangeSeed) :=
  { leg : seed.Leg // leg ∈ seed.legList compiler }

def obligationOccurrenceOfLeg
    (seed : compiler.ExactExchangeSeed) (leg : seed.Leg) :
    seed.ObligationOccurrence compiler :=
  ⟨leg, seed.leg_mem compiler leg⟩

def principalLeg (seed : compiler.ExactExchangeSeed) : seed.Leg :=
  compiler.principalLeg seed.1

def counterparty (seed : compiler.ExactExchangeSeed) (leg : seed.Leg) :
    seed.Leg :=
  compiler.counterparty seed.1 leg

@[simp] theorem counterparty_counterparty
    (seed : compiler.ExactExchangeSeed) (leg : seed.Leg) :
    seed.counterparty compiler (seed.counterparty compiler leg) = leg :=
  compiler.counterparty_involutive seed.1 leg

theorem counterparty_ne
    (seed : compiler.ExactExchangeSeed) (leg : seed.Leg) :
    seed.counterparty compiler leg ≠ leg :=
  compiler.counterparty_ne seed.1 leg

def relationExactSeed
    (seed : compiler.ExactExchangeSeed) (leg : seed.Leg) :
    relationCompiler.ExactRelationSeed :=
  ⟨compiler.relationSeed seed.1 leg,
    core.targetFace.state game.source,
    core.target_state_mem,
    compiler.relationSeed_active seed.1 leg (seed.admitted compiler)⟩

def responsibilityExactSeed
    (seed : compiler.ExactExchangeSeed) (leg : seed.Leg) :
    incidence.compiler.ExactTargetSeed :=
  ⟨compiler.responsibilitySeed seed.1 leg,
    core.targetFace.state game.source,
    core.target_state_mem,
    rfl,
    compiler.responsibilitySeed_active seed.1 leg
      (seed.admitted compiler)⟩

def relation (seed : compiler.ExactExchangeSeed) (leg : seed.Leg) :
    relationCompiler.GeneratedRelation :=
  relationCompiler.relationOf (seed.relationExactSeed compiler leg)

def actor (seed : compiler.ExactExchangeSeed) (leg : seed.Leg) :
    core.TargetActor :=
  (seed.relationExactSeed compiler leg).actor relationCompiler

def admissionEvent (seed : compiler.ExactExchangeSeed) (leg : seed.Leg) :
    P.AdmissionEvent :=
  compiler.admissionEvent seed.1 leg

def obligation (seed : compiler.ExactExchangeSeed) (leg : seed.Leg) :
    AdmittedObligation V :=
  (P.admissionPayload (seed.admissionEvent compiler leg)).toObligation

def sourceEvent (seed : compiler.ExactExchangeSeed) (leg : seed.Leg) :
    V.SourceEvent :=
  (P.admissionPayload (seed.admissionEvent compiler leg)).sourceEvent

theorem interest (seed : compiler.ExactExchangeSeed) (leg : seed.Leg) :
    relationCompiler.GeneratedInterestAt
      (seed.actor compiler leg) (seed.relation compiler leg) :=
  ⟨seed.relationExactSeed compiler leg, rfl, rfl⟩

def admissionOwnership
    (seed : compiler.ExactExchangeSeed) (leg : seed.Leg) :
    SourceOwnsResponsibilityIncidence V
      (seed.sourceEvent compiler leg) (seed.obligation compiler leg) :=
  P.admissionSourceOwnership (seed.admissionEvent compiler leg)

def priorGeneratedState (seed : compiler.ExactExchangeSeed) :
    P.GeneratedState :=
  compiler.sourceState seed.1

/-- Dependent fold of every remaining leg onto a generated responsibility
state.  Each step's source is the exact target of the preceding admission. -/
def admitLegs (seed : compiler.ExactExchangeSeed) :
    List seed.Leg → P.GeneratedState → P.GeneratedState
  | [], state => state
  | leg :: remaining, state =>
      let edge : P.Edge state.current :=
        .admit (seed.admissionEvent compiler leg)
      seed.admitLegs remaining
        ⟨edge.target, .step state.generated edge⟩

theorem admitLegs_slots
    (seed : compiler.ExactExchangeSeed)
    (remaining : List seed.Leg) (state : P.GeneratedState) :
    (admitLegs compiler seed remaining state).current.slots =
      state.current.slots ++
        remaining.map (fun leg => .live (seed.obligation compiler leg)) := by
  induction remaining generalizing state with
  | nil => simp [admitLegs]
  | cons leg remaining ih =>
      simp only [admitLegs]
      rw [ih]
      simp [NativeResponsibilityProcess.Edge.target, obligation,
        admissionEvent, List.append_assoc]

/-- Complete process state generated after admitting every exchange leg. -/
def generatedState (seed : compiler.ExactExchangeSeed) : P.GeneratedState :=
  admitLegs compiler seed (seed.legList compiler)
    (seed.priorGeneratedState compiler)

theorem generatedState_slots (seed : compiler.ExactExchangeSeed) :
    (seed.generatedState compiler).current.slots =
      (seed.priorGeneratedState compiler).current.slots ++
        (seed.legList compiler).map
          (fun leg => .live (seed.obligation compiler leg)) :=
  admitLegs_slots compiler seed _ _

/-- Index of a leg inside its source-generated finite carrier. -/
def legIndex (seed : compiler.ExactExchangeSeed) (leg : seed.Leg) : Nat :=
  (seed.legList compiler).idxOf leg

/-- Stable responsibility slot of a generated exchange-leg occurrence. -/
def obligationSlotIndex
    (seed : compiler.ExactExchangeSeed) (leg : seed.Leg) : Nat :=
  (seed.priorGeneratedState compiler).current.slots.length +
    seed.legIndex compiler leg

theorem obligationSlotIndex_injective (seed : compiler.ExactExchangeSeed) :
    Function.Injective (seed.obligationSlotIndex compiler) := by
  intro left right slotsEq
  apply (List.idxOf_inj (seed.leg_mem compiler left)).mp
  exact Nat.add_left_cancel slotsEq

theorem counterparty_slot_ne
    (seed : compiler.ExactExchangeSeed) (leg : seed.Leg) :
    seed.obligationSlotIndex compiler (seed.counterparty compiler leg) ≠
      seed.obligationSlotIndex compiler leg := by
  intro slotsEq
  exact seed.counterparty_ne compiler leg
    (seed.obligationSlotIndex_injective compiler slotsEq)

theorem obligationSlotIndex_lt
    (seed : compiler.ExactExchangeSeed) (leg : seed.Leg) :
    seed.obligationSlotIndex compiler leg <
      (seed.generatedState compiler).current.slots.length := by
  have indexLt : seed.legIndex compiler leg <
      (seed.legList compiler).length :=
    List.idxOf_lt_length_of_mem (seed.leg_mem compiler leg)
  rw [seed.generatedState_slots compiler, List.length_append,
    List.length_map]
  exact Nat.add_lt_add_left indexLt _

/-- Exact final-state lookup: every generated leg is live at its stable slot. -/
@[simp] theorem generatedState_obligationSlotIndex
    (seed : compiler.ExactExchangeSeed) (leg : seed.Leg) :
    (seed.generatedState compiler).current.slots[
        seed.obligationSlotIndex compiler leg]? =
      some (.live (seed.obligation compiler leg)) := by
  rw [seed.generatedState_slots compiler]
  unfold obligationSlotIndex
  rw [List.getElem?_append_right (Nat.le_add_right _ _)]
  simp only [legIndex, Nat.add_sub_cancel_left,
    List.getElem?_map, List.getElem?_idxOf (seed.leg_mem compiler leg),
    Option.map_some]

/-- Finite stable-slot witness recovered from exact lookup. -/
def obligationSlot
    (seed : compiler.ExactExchangeSeed) (leg : seed.Leg) :
    Fin (seed.generatedState compiler).current.slots.length :=
  ⟨seed.obligationSlotIndex compiler leg,
    seed.obligationSlotIndex_lt compiler leg⟩

/-- `Fin` form consumed directly by exact lifecycle boundary edges. -/
@[simp] theorem generatedState_obligationSlot_get
    (seed : compiler.ExactExchangeSeed) (leg : seed.Leg) :
    (seed.generatedState compiler).current.slots.get
        (seed.obligationSlot compiler leg) =
      .live (seed.obligation compiler leg) := by
  have lookup := seed.generatedState_obligationSlotIndex compiler leg
  have indexEq :
      (seed.obligationSlot compiler leg).val =
        seed.obligationSlotIndex compiler leg := rfl
  rw [← indexEq] at lookup
  rw [List.getElem?_eq_getElem
    (seed.obligationSlot compiler leg).isLt] at lookup
  exact Option.some.inj lookup

namespace ObligationOccurrence

def obligation
    {seed : compiler.ExactExchangeSeed}
    (occurrence : seed.ObligationOccurrence compiler) : AdmittedObligation V :=
  seed.obligation compiler occurrence.1

def slotIndex
    {seed : compiler.ExactExchangeSeed}
    (occurrence : seed.ObligationOccurrence compiler) : Nat :=
  seed.obligationSlotIndex compiler occurrence.1

def slot
    {seed : compiler.ExactExchangeSeed}
    (occurrence : seed.ObligationOccurrence compiler) :
    Fin (seed.generatedState compiler).current.slots.length :=
  seed.obligationSlot compiler occurrence.1

/-- Settlement's exact provenance mouth: the occurrence stores its exchange
seed and leg, and its stable slot reads the generated live obligation. -/
@[simp] theorem live_at_slot
    {seed : compiler.ExactExchangeSeed}
    (occurrence : seed.ObligationOccurrence compiler) :
    (seed.generatedState compiler).current.slots.get occurrence.slot =
      .live occurrence.obligation :=
  seed.generatedState_obligationSlot_get compiler occurrence.1

def counterparty
    {seed : compiler.ExactExchangeSeed}
    (occurrence : seed.ObligationOccurrence compiler) :
    seed.ObligationOccurrence compiler :=
  seed.obligationOccurrenceOfLeg compiler
    (seed.counterparty compiler occurrence.1)

theorem counterparty_slot_ne
    {seed : compiler.ExactExchangeSeed}
    (occurrence : seed.ObligationOccurrence compiler) :
    occurrence.counterparty.slotIndex ≠ occurrence.slotIndex :=
  seed.counterparty_slot_ne compiler occurrence.1

end ObligationOccurrence

end ExactExchangeSeed
end SourceOwnedExchangeCompiler

/-- Semantic laws for the source-owned compiler.  All parties, obligations,
bearers, interests, and source events remain outputs indexed by one exact
exchange seed and one of its generated legs. -/
structure SourceOwnedExchangeLaw
    (core : SourceOwnedLifecycleCore.{u, v, w} occurrenceOf game)
    (V : Vocabulary.{x}) (P : NativeResponsibilityProcess V)
    (incidence : ActorResponsibilityIncidence core V)
    (relationCompiler : SourceOwnedRelationRoleCompiler.{u, v, w, y}
      occurrenceOf game core.targetFace) where
  compiler : SourceOwnedExchangeCompiler.{u, v, w, x, y, z}
    core V P incidence relationCompiler
  bearerOfActor : core.TargetActor → V.Bearer
  protectedInterestOfActor : core.TargetActor → V.ProtectedInterest
  actorSeed_eq : ∀ seed : compiler.ExactExchangeSeed, ∀ leg : seed.Leg,
    incidence.compiler.targetActorSeed
        (compiler.responsibilitySeed seed.1 leg) =
      relationCompiler.beneficiaryActorSeed
        (compiler.relationSeed seed.1 leg)
  obligation_eq : ∀ seed : compiler.ExactExchangeSeed, ∀ leg : seed.Leg,
    incidence.compiler.targetObligation
        (compiler.responsibilitySeed seed.1 leg) =
      seed.obligation compiler leg
  sourceEvent_eq : ∀ seed : compiler.ExactExchangeSeed, ∀ leg : seed.Leg,
    incidence.compiler.targetEvent
        (compiler.responsibilitySeed seed.1 leg) =
      seed.sourceEvent compiler leg
  bearer_eq : ∀ seed : compiler.ExactExchangeSeed, ∀ leg : seed.Leg,
    (seed.obligation compiler leg).bearer =
      bearerOfActor (seed.actor compiler leg)
  beneficiary_eq : ∀ seed : compiler.ExactExchangeSeed, ∀ leg : seed.Leg,
    (seed.obligation compiler leg).beneficiary =
      protectedInterestOfActor
        (seed.actor compiler (seed.counterparty compiler leg))
  restriction_parent_state_eq :
    ∀ seed : compiler.ExactExchangeSeed, ∀ leg : seed.Leg,
      compiler.parentStateOf (seed.sourceEvent compiler leg) =
        core.targetFace.state game.source
  sourceEvents_ne : ∀ seed : compiler.ExactExchangeSeed, ∀ leg : seed.Leg,
    seed.sourceEvent compiler leg ≠
      seed.sourceEvent compiler (seed.counterparty compiler leg)
  counterpartyActors_ne :
    ∀ seed : compiler.ExactExchangeSeed, ∀ leg : seed.Leg,
      seed.actor compiler leg ≠
        seed.actor compiler (seed.counterparty compiler leg)

namespace SourceOwnedExchangeLaw

variable
  (law : SourceOwnedExchangeLaw.{u, v, w, x, y, z}
    core V P incidence relationCompiler)

abbrev ExactExchangeSeed := law.compiler.ExactExchangeSeed

/-- Public carrier stores its exact source seed directly.  Projection never
requires a representative choice. -/
def GeneratedExchange :=
  { _seed : law.ExactExchangeSeed // law = law }

def exchangeOf (seed : law.ExactExchangeSeed) : law.GeneratedExchange :=
  ⟨seed, rfl⟩

theorem generatedExchange_has_exact_seed
    (exchange : law.GeneratedExchange) :
    ∃ seed : law.ExactExchangeSeed, law.exchangeOf seed = exchange :=
  ⟨exchange.1, Subtype.ext rfl⟩

namespace GeneratedExchange

def exactSeed (exchange : law.GeneratedExchange) : law.ExactExchangeSeed :=
  exchange.1

@[simp] theorem exactSeed_eq (exchange : law.GeneratedExchange) :
    exchange.exactSeed law = exchange.1 := rfl

end GeneratedExchange

private theorem actor_eq_responsibilityActor
    (seed : law.ExactExchangeSeed) (leg : seed.Leg) :
    (seed.responsibilityExactSeed law.compiler leg).actor
        incidence.compiler =
      seed.actor law.compiler leg := by
  apply Subtype.ext
  apply congrArg (core.targetFace.lineageOf game.source)
  apply Subtype.ext
  exact law.actorSeed_eq seed leg

/-- Exact target actor/responsibility incidence generated for a leg. -/
def responsibilityAt
    (seed : law.ExactExchangeSeed) (leg : seed.Leg) :
    incidence.TargetResponsibilityAt
      (seed.actor law.compiler leg)
      (seed.obligation law.compiler leg)
      (seed.sourceEvent law.compiler leg) where
  seed := seed.responsibilityExactSeed law.compiler leg
  actor_eq := law.actor_eq_responsibilityActor seed leg
  obligation_eq := law.obligation_eq seed leg
  sourceEvent_eq := law.sourceEvent_eq seed leg

/-- Universal native reciprocity: the statement quantifies every leg of every
exact exchange seed and derives its counterparty from the involution. -/
theorem native_reciprocity
    (seed : law.ExactExchangeSeed) (leg : seed.Leg) :
    relationCompiler.GeneratedInterestAt
        (seed.actor law.compiler leg)
        (seed.relation law.compiler leg) ∧
      Nonempty (incidence.TargetResponsibilityAt
        (seed.actor law.compiler leg)
        (seed.obligation law.compiler leg)
        (seed.sourceEvent law.compiler leg)) ∧
      Nonempty (SourceOwnsResponsibilityIncidence V
        (seed.sourceEvent law.compiler leg)
        (seed.obligation law.compiler leg)) ∧
      (seed.obligation law.compiler leg).bearer =
        law.bearerOfActor (seed.actor law.compiler leg) ∧
      (seed.obligation law.compiler leg).beneficiary =
        law.protectedInterestOfActor
          (seed.actor law.compiler (seed.counterparty law.compiler leg)) :=
  ⟨seed.interest law.compiler leg,
    ⟨law.responsibilityAt seed leg⟩,
    ⟨seed.admissionOwnership law.compiler leg⟩,
    law.bearer_eq seed leg,
    law.beneficiary_eq seed leg⟩

theorem counterparties_distinct
    (seed : law.ExactExchangeSeed) (leg : seed.Leg) :
    seed.counterparty law.compiler leg ≠ leg :=
  seed.counterparty_ne law.compiler leg

theorem counterparty_actors_distinct
    (seed : law.ExactExchangeSeed) (leg : seed.Leg) :
    seed.actor law.compiler leg ≠
      seed.actor law.compiler (seed.counterparty law.compiler leg) :=
  law.counterpartyActors_ne seed leg

theorem counterparty_restrictions_distinct
    (seed : law.ExactExchangeSeed) (leg : seed.Leg) :
    seed.sourceEvent law.compiler leg ≠
      seed.sourceEvent law.compiler (seed.counterparty law.compiler leg) :=
  law.sourceEvents_ne seed leg

/-- Fixed-point freedom plus the source-generated principal leg yields at
least two distinct legs for every exact exchange, without a global registry. -/
theorem at_least_two_legs (seed : law.ExactExchangeSeed) :
    ∃ left right : seed.Leg, left ≠ right :=
  ⟨seed.principalLeg law.compiler,
    seed.counterparty law.compiler (seed.principalLeg law.compiler),
    (seed.counterparty_ne law.compiler
      (seed.principalLeg law.compiler)).symm⟩

/-- Counterparty restrictions are distinct but both project to the same
actual parent state in the fixed source occurrence. -/
theorem counterparty_restrictions_share_exact_parent_state
    (seed : law.ExactExchangeSeed) (leg : seed.Leg) :
    ∃ state ∈ game.occurrence.trace,
      state = core.targetFace.state game.source ∧
      law.compiler.exchangeAdmittedAt seed.1 ∧
      law.compiler.parentStateOf (seed.sourceEvent law.compiler leg) = state ∧
      law.compiler.parentStateOf
          (seed.sourceEvent law.compiler
            (seed.counterparty law.compiler leg)) = state ∧
      seed.sourceEvent law.compiler leg ≠
        seed.sourceEvent law.compiler
          (seed.counterparty law.compiler leg) := by
  rcases seed.exact_state_provenance law.compiler with
    ⟨state, inTrace, atTarget, admitted⟩
  refine ⟨state, inTrace, atTarget, admitted, ?_, ?_, law.sourceEvents_ne seed leg⟩
  · rw [law.restriction_parent_state_eq seed leg, ← atTarget]
  · rw [law.restriction_parent_state_eq seed
      (seed.counterparty law.compiler leg), ← atTarget]

/-- The whole exchange is installed in exactly the `(V,P,incidence)` passed
to this universal law. -/
def installed
    (law : SourceOwnedExchangeLaw.{u, v, w, x, y, z}
      core V P incidence relationCompiler) :
    FrameworkInstallation.{u, v, w, x} core :=
  let _authority := law
  .installed V P incidence

@[simp] theorem installed_eq
    (law : SourceOwnedExchangeLaw.{u, v, w, x, y, z}
      core V P incidence relationCompiler) :
    law.installed =
      (FrameworkInstallation.installed V P incidence :
        FrameworkInstallation.{u, v, w, x} core) := rfl

end SourceOwnedExchangeLaw
end Exchange
end Society
end ProcessGame
end SaturationMonoid
