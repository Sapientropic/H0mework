import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Settlement.AutomaticFullFulfillment

/-!
# Source-generated symmetric clearing

One exact exchange leg and its source-generated counterparty determine the
two sides of clearing.  A process-native fulfillment authority supplies an
actual consumer for every leg.  The existing automatic fulfillment fold then
produces the sole exhaustive run; this module neither accepts nor constructs
a second run.

The clearing carrier is a zero-field restriction of those existing indices.
Actors, responsibility slots, source ownership, fulfillment, and the closed
target are all read from the exact exchange seed and the canonical fold.  No
participant registry, balance table, weight, coverage premise, clearing unit,
currency issuer, ledger, or completed schedule is introduced.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Clearing

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Exchange Settlement
open Settlement.SourceOwnedSettlementCompiler

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
variable
  {exchangeLaw : SourceOwnedExchangeLaw.{u, v, w, x, y, z}
    core V P incidence relationCompiler}

noncomputable section

/-- A symmetric clearing face is indexed only by an existing total
fulfillment authority, one exact exchange seed, and one of that seed's actual
legs.  The other side and the exhaustive run are generated, not supplied. -/
inductive SourceGeneratedSymmetricClearingAt
    (authority : ExactExchangeFulfillmentAuthority
      (exchangeLaw := exchangeLaw))
    (seed : exchangeLaw.ExactExchangeSeed)
    (leg : seed.Leg) : Type where
  | private generated

namespace SourceGeneratedSymmetricClearingAt

/-- Sole producer.  It accepts no second leg, participant family, coverage,
weights, balances, run, or target current. -/
def generate
    (authority : ExactExchangeFulfillmentAuthority
      (exchangeLaw := exchangeLaw))
    (seed : exchangeLaw.ExactExchangeSeed)
    (leg : seed.Leg) :
    SourceGeneratedSymmetricClearingAt authority seed leg :=
  .generated

variable
  {authority : ExactExchangeFulfillmentAuthority
    (exchangeLaw := exchangeLaw)}
  {seed : exchangeLaw.ExactExchangeSeed}
  {leg : seed.Leg}
  (clearing : SourceGeneratedSymmetricClearingAt authority seed leg)

theorem eq_generate : clearing = generate authority seed leg := by
  cases clearing
  rfl

/-! ## Two source-generated sides -/

def counterpartyLeg
    (_clearing : SourceGeneratedSymmetricClearingAt authority seed leg) :
    seed.Leg :=
  seed.counterparty exchangeLaw.compiler leg

@[simp] theorem counterpartyLeg_eq :
    clearing.counterpartyLeg =
      seed.counterparty exchangeLaw.compiler leg :=
  rfl

@[simp] theorem counterparty_counterparty_eq :
    seed.counterparty exchangeLaw.compiler clearing.counterpartyLeg = leg :=
  seed.counterparty_counterparty exchangeLaw.compiler leg

def legActor
    (_clearing : SourceGeneratedSymmetricClearingAt authority seed leg) :
    core.TargetActor :=
  seed.actor exchangeLaw.compiler leg

def counterpartyActor
    (_clearing : SourceGeneratedSymmetricClearingAt authority seed leg) :
    core.TargetActor :=
  seed.actor exchangeLaw.compiler _clearing.counterpartyLeg

def legSlotIndex
    (_clearing : SourceGeneratedSymmetricClearingAt authority seed leg) : Nat :=
  seed.obligationSlotIndex exchangeLaw.compiler leg

def counterpartySlotIndex
    (_clearing : SourceGeneratedSymmetricClearingAt authority seed leg) : Nat :=
  seed.obligationSlotIndex exchangeLaw.compiler _clearing.counterpartyLeg

theorem actors_distinct :
    clearing.legActor ≠ clearing.counterpartyActor :=
  SourceOwnedExchangeLaw.counterparty_actors_distinct exchangeLaw seed leg

theorem slotIndices_distinct :
    clearing.legSlotIndex ≠ clearing.counterpartySlotIndex :=
  (SourceOwnedExchangeCompiler.ExactExchangeSeed.counterparty_slot_ne
    exchangeLaw.compiler seed leg).symm

/-- Exact process-native consumer on the selected side. -/
def legConsumer
    (_clearing : SourceGeneratedSymmetricClearingAt authority seed leg) :
    ExactLegFulfillmentAt seed leg :=
  authority seed leg

/-- The other consumer is forced by the existing counterparty involution. -/
def counterpartyConsumer
    (_clearing : SourceGeneratedSymmetricClearingAt authority seed leg) :
    ExactLegFulfillmentAt seed _clearing.counterpartyLeg :=
  authority seed _clearing.counterpartyLeg

/-- Source ownership of the selected clearing action. -/
def legSourceOwnership :
    SourceOwnsResponsibilityIncidence V
      (P.boundarySource clearing.legConsumer.event)
      (seed.obligation exchangeLaw.compiler leg) :=
  P.boundarySourceOwnership clearing.legConsumer.event

/-- Independent source ownership of the counterparty clearing action. -/
def counterpartySourceOwnership :
    SourceOwnsResponsibilityIncidence V
      (P.boundarySource clearing.counterpartyConsumer.event)
      (seed.obligation exchangeLaw.compiler clearing.counterpartyLeg) :=
  P.boundarySourceOwnership clearing.counterpartyConsumer.event

/-- Both original admissions also retain their own exact source incidence. -/
def legAdmissionOwnership :
    SourceOwnsResponsibilityIncidence V
      (seed.sourceEvent exchangeLaw.compiler leg)
      (seed.obligation exchangeLaw.compiler leg) :=
  seed.admissionOwnership exchangeLaw.compiler leg

def counterpartyAdmissionOwnership :
    SourceOwnsResponsibilityIncidence V
      (seed.sourceEvent exchangeLaw.compiler clearing.counterpartyLeg)
      (seed.obligation exchangeLaw.compiler clearing.counterpartyLeg) :=
  seed.admissionOwnership exchangeLaw.compiler clearing.counterpartyLeg

/-! ## Sole exhaustive clearing fold -/

def fullResult
    (_clearing : SourceGeneratedSymmetricClearingAt authority seed leg) :=
  AutomaticFullFulfillment.fullResult authority seed

def fullRun : P.Run
    (seed.generatedState exchangeLaw.compiler).current
    clearing.fullResult.current :=
  clearing.fullResult.run

@[simp] theorem fullResult_exact :
    clearing.fullResult = AutomaticFullFulfillment.fullResult authority seed :=
  rfl

@[simp] theorem fullRun_exact :
    clearing.fullRun =
      (AutomaticFullFulfillment.fullResult authority seed).run :=
  rfl

theorem leg_fulfilled :
    Nonempty (AutomaticFullFulfillment.FulfilledSlotAt seed
      clearing.fullResult.current leg) :=
  AutomaticFullFulfillment.fullResult_fulfills authority seed leg

theorem counterparty_fulfilled :
    Nonempty (AutomaticFullFulfillment.FulfilledSlotAt seed
      clearing.fullResult.current clearing.counterpartyLeg) :=
  AutomaticFullFulfillment.fullResult_fulfills authority seed
    clearing.counterpartyLeg

/-- The two restrictions are different, but both are generated at the exact
parent state already witnessed by the same exchange seed. -/
theorem sides_share_exact_parent_state :
    ∃ state ∈ game.occurrence.trace,
      state = core.targetFace.state game.source ∧
      exchangeLaw.compiler.exchangeAdmittedAt seed.1 ∧
      exchangeLaw.compiler.parentStateOf
          (seed.sourceEvent exchangeLaw.compiler leg) = state ∧
      exchangeLaw.compiler.parentStateOf
          (seed.sourceEvent exchangeLaw.compiler clearing.counterpartyLeg) =
        state ∧
      seed.sourceEvent exchangeLaw.compiler leg ≠
        seed.sourceEvent exchangeLaw.compiler clearing.counterpartyLeg :=
  SourceOwnedExchangeLaw.counterparty_restrictions_share_exact_parent_state
    exchangeLaw seed leg

/-- Exhaustiveness is read from the source compiler's own leg carrier.  No
caller-supplied coverage family occurs in this theorem or the producer. -/
theorem every_generated_leg_consumed_and_fulfilled
    (other : seed.Leg) :
    Nonempty (ExactLegFulfillmentAt seed other) ∧
      Nonempty (SourceOwnsResponsibilityIncidence V
        (P.boundarySource (authority seed other).event)
        (seed.obligation exchangeLaw.compiler other)) ∧
      Nonempty (AutomaticFullFulfillment.FulfilledSlotAt seed
        clearing.fullResult.current other) :=
  ⟨⟨authority seed other⟩,
    ⟨P.boundarySourceOwnership (authority seed other).event⟩,
    AutomaticFullFulfillment.fullResult_fulfills authority seed other⟩

/-- The complete two-sided readout.  It quantifies no submitted participant
family and exposes no balance or clearing-unit field. -/
theorem two_sides_exact :
    Nonempty (ExactLegFulfillmentAt seed leg) ∧
      Nonempty (ExactLegFulfillmentAt seed clearing.counterpartyLeg) ∧
      Nonempty (SourceOwnsResponsibilityIncidence V
        (P.boundarySource clearing.legConsumer.event)
        (seed.obligation exchangeLaw.compiler leg)) ∧
      Nonempty (SourceOwnsResponsibilityIncidence V
        (P.boundarySource clearing.counterpartyConsumer.event)
        (seed.obligation exchangeLaw.compiler clearing.counterpartyLeg)) ∧
      clearing.legActor ≠ clearing.counterpartyActor ∧
      clearing.legSlotIndex ≠ clearing.counterpartySlotIndex ∧
      Nonempty (AutomaticFullFulfillment.FulfilledSlotAt seed
        clearing.fullResult.current leg) ∧
      Nonempty (AutomaticFullFulfillment.FulfilledSlotAt seed
        clearing.fullResult.current clearing.counterpartyLeg) :=
  ⟨⟨clearing.legConsumer⟩,
    ⟨clearing.counterpartyConsumer⟩,
    ⟨clearing.legSourceOwnership⟩,
    ⟨clearing.counterpartySourceOwnership⟩,
    clearing.actors_distinct,
    clearing.slotIndices_distinct,
    clearing.leg_fulfilled,
    clearing.counterparty_fulfilled⟩

abbrev automaticSettlementCompiler
    (_clearing : SourceGeneratedSymmetricClearingAt authority seed leg) :=
  AutomaticFullFulfillment.settlementCompiler authority

def settlementOccurrence :
    clearing.automaticSettlementCompiler.GeneratedSettlementOccurrence :=
  AutomaticFullFulfillment.settlementOccurrence authority seed

noncomputable def fullyFulfilled :
    FullyFulfilledExchangeAt clearing.automaticSettlementCompiler
      clearing.settlementOccurrence :=
  AutomaticFullFulfillment.fullyFulfilled authority seed

/-- Exhaustive symmetric clearing removes the whole open-settlement fibre;
it does not assign a zero balance or zero price to a still-open position. -/
theorem target_openSettlement_isEmpty :
    IsEmpty (OpenSettlementAt clearing.automaticSettlementCompiler
      clearing.settlementOccurrence) :=
  clearing.fullyFulfilled.openSettlement_isEmpty

/-! ## Honest nil and one-sided controls -/

/-- The unadvanced exchange current is live at every generated leg and hence
cannot already carry a fulfilled-slot witness. -/
theorem nilCurrent_legFulfilled_isEmpty :
    IsEmpty (AutomaticFullFulfillment.FulfilledSlotAt seed
      (seed.generatedState exchangeLaw.compiler).current leg) := by
  refine ⟨fun fulfilled => ?_⟩
  have live :=
    seed.generatedState_obligationSlotIndex exchangeLaw.compiler leg
  have impossible := live.symm.trans fulfilled.present
  cases impossible

/-- One selected consumer produces one exact edge, not a second exhaustive
run.  The counterparty remains live because its stable slot is distinct. -/
def oneSidedEdge :
    P.Edge (seed.generatedState exchangeLaw.compiler).current :=
  .cross (seed.obligationSlot exchangeLaw.compiler leg)
    (seed.obligation exchangeLaw.compiler leg)
    (seed.generatedState_obligationSlot_get exchangeLaw.compiler leg)
    clearing.legConsumer.event

theorem counterparty_live_after_oneSidedEdge :
    clearing.oneSidedEdge.target.slots[
        clearing.counterpartySlotIndex]? =
      some (.live
        (seed.obligation exchangeLaw.compiler clearing.counterpartyLeg)) := by
  have counterpartyLt : clearing.counterpartySlotIndex <
      (seed.generatedState exchangeLaw.compiler).current.slots.length :=
    seed.obligationSlotIndex_lt exchangeLaw.compiler
      clearing.counterpartyLeg
  have changedNe :
      (seed.obligationSlot exchangeLaw.compiler leg).val ≠
        clearing.counterpartySlotIndex := by
    exact clearing.slotIndices_distinct
  change
    ((seed.generatedState exchangeLaw.compiler).current.slots.set
      (seed.obligationSlot exchangeLaw.compiler leg)
      (P.boundaryDisposition clearing.legConsumer.event).targetSlot)[
        clearing.counterpartySlotIndex]? = _
  rw [List.getElem?_set_of_lt _ _ counterpartyLt, if_neg changedNe]
  exact seed.generatedState_obligationSlotIndex exchangeLaw.compiler
    clearing.counterpartyLeg

/-- Consequently a singleton clearing action cannot masquerade as symmetric
completion: its generated counterparty slot is still live, not fulfilled. -/
theorem oneSided_counterpartyFulfilled_isEmpty :
    IsEmpty (AutomaticFullFulfillment.FulfilledSlotAt seed
      clearing.oneSidedEdge.target clearing.counterpartyLeg) := by
  refine ⟨fun fulfilled => ?_⟩
  have live := clearing.counterparty_live_after_oneSidedEdge
  have impossible := live.symm.trans fulfilled.present
  cases impossible

theorem producer_mouth_has_no_registry_weight_coverage_or_second_run : True := by
  fail_if_success exact clearing.participantRegistry
  fail_if_success exact clearing.coverage
  fail_if_success exact clearing.weights
  fail_if_success exact clearing.balanceTable
  fail_if_success exact clearing.clearingUnit
  fail_if_success exact clearing.currencyIssuer
  fail_if_success exact clearing.secondRun
  fail_if_success exact clearing.completedFuture
  fail_if_success exact generate clearing.legConsumer seed leg
  trivial

end SourceGeneratedSymmetricClearingAt

end
end Clearing
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.Clearing.SourceGeneratedSymmetricClearingAt.generate
#print axioms SaturationMonoid.ProcessGame.Society.Clearing.SourceGeneratedSymmetricClearingAt.every_generated_leg_consumed_and_fulfilled
#print axioms SaturationMonoid.ProcessGame.Society.Clearing.SourceGeneratedSymmetricClearingAt.two_sides_exact
#print axioms SaturationMonoid.ProcessGame.Society.Clearing.SourceGeneratedSymmetricClearingAt.target_openSettlement_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.Clearing.SourceGeneratedSymmetricClearingAt.nilCurrent_legFulfilled_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.Clearing.SourceGeneratedSymmetricClearingAt.oneSided_counterpartyFulfilled_isEmpty
