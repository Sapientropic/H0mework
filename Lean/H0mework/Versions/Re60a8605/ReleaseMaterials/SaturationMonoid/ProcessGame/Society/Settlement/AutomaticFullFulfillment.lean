import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Settlement.ExchangeSettlement

/-!
# Automatic full fulfillment of a generated finite exchange

This module closes an arbitrary source-generated finite exchange without a
caller-supplied current or completed run.  A fixed fulfillment authority
provides one genuine process boundary event for every generated leg.  The
dependent fold then visits the exhaustive source leg list, preserves every
other stable slot at each step, and produces the whole `P.Run` together with
exact fulfilled-slot witnesses for every leg.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Settlement

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Exchange
open SourceOwnedSettlementCompiler

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

/-- Process-native fulfillment of one exact exchange leg. -/
structure ExactLegFulfillmentAt
    (seed : exchangeLaw.ExactExchangeSeed) (leg : seed.Leg) where
  event : P.BoundaryEvent (seed.obligation exchangeLaw.compiler leg)
  receipt : V.FulfilledAt (P.boundarySource event)
    (seed.obligation exchangeLaw.compiler leg).content
    (seed.obligation exchangeLaw.compiler leg).scope
  disposition_eq : P.boundaryDisposition event =
    .terminal (.final (.fulfilled receipt))

/-- Fixed authority assigning a real fulfillment event to every leg of every
exact exchange seed. -/
abbrev ExactExchangeFulfillmentAuthority :=
  (seed : exchangeLaw.ExactExchangeSeed) →
    (leg : seed.Leg) → ExactLegFulfillmentAt seed leg

namespace AutomaticFullFulfillment

variable
  (authority : ExactExchangeFulfillmentAuthority (exchangeLaw := exchangeLaw))

/-- Exact terminal value at one original stable slot in an arbitrary current. -/
structure FulfilledSlotAt
    (seed : exchangeLaw.ExactExchangeSeed)
    (current : ResponsibilityState V) (leg : seed.Leg) where
  sourceEvent : V.SourceEvent
  receipt : V.FulfilledAt sourceEvent
    (seed.obligation exchangeLaw.compiler leg).content
    (seed.obligation exchangeLaw.compiler leg).scope
  present : current.slots[
      seed.obligationSlotIndex exchangeLaw.compiler leg]? =
    some (.terminal ⟨seed.obligation exchangeLaw.compiler leg,
      sourceEvent, .fulfilled receipt⟩)

/-- Result of fulfilling exactly one supplied sublist.  The result also says
that every stable slot outside that sublist is unchanged. -/
structure ListResult
    (seed : exchangeLaw.ExactExchangeSeed)
    (start : ResponsibilityState V) (legs : List seed.Leg) where
  current : ResponsibilityState V
  run : P.Run start current
  fulfilled : ∀ leg, leg ∈ legs → Nonempty (FulfilledSlotAt seed current leg)
  preserved : ∀ leg, leg ∉ legs →
    current.slots[seed.obligationSlotIndex exchangeLaw.compiler leg]? =
      start.slots[seed.obligationSlotIndex exchangeLaw.compiler leg]?
  slots_length : current.slots.length = start.slots.length

private theorem slotIndex_ne_of_ne
    (seed : exchangeLaw.ExactExchangeSeed) {left right : seed.Leg}
    (distinct : left ≠ right) :
    seed.obligationSlotIndex exchangeLaw.compiler left ≠
      seed.obligationSlotIndex exchangeLaw.compiler right := by
  intro equal
  exact distinct (seed.obligationSlotIndex_injective
    exchangeLaw.compiler equal)

private def fulfillmentEdge
    (seed : exchangeLaw.ExactExchangeSeed) (leg : seed.Leg)
    (current : ResponsibilityState V)
    (length_eq : current.slots.length =
      (seed.generatedState exchangeLaw.compiler).current.slots.length)
    (live : current.slots[
        seed.obligationSlotIndex exchangeLaw.compiler leg]? =
      some (.live (seed.obligation exchangeLaw.compiler leg))) :
    P.Edge current := by
  let index := seed.obligationSlotIndex exchangeLaw.compiler leg
  have index_lt : index < current.slots.length := by
    rw [length_eq]
    exact seed.obligationSlotIndex_lt exchangeLaw.compiler leg
  let slot : Fin current.slots.length := ⟨index, index_lt⟩
  have present : current.slots.get slot =
      .live (seed.obligation exchangeLaw.compiler leg) := by
    rw [List.getElem?_eq_getElem index_lt] at live
    exact Option.some.inj live
  exact .cross slot (seed.obligation exchangeLaw.compiler leg) present
    (authority seed leg).event

private theorem fulfillmentEdge_slots_length
    (seed : exchangeLaw.ExactExchangeSeed) (leg : seed.Leg)
    (current : ResponsibilityState V)
    (length_eq : current.slots.length =
      (seed.generatedState exchangeLaw.compiler).current.slots.length)
    (live : current.slots[
        seed.obligationSlotIndex exchangeLaw.compiler leg]? =
      some (.live (seed.obligation exchangeLaw.compiler leg))) :
    (fulfillmentEdge authority seed leg current length_eq live).target.slots.length =
      current.slots.length := by
  simp [fulfillmentEdge, NativeResponsibilityProcess.Edge.target]

private theorem fulfillmentEdge_other_slot
    (seed : exchangeLaw.ExactExchangeSeed) (head leg : seed.Leg)
    (distinct : head ≠ leg)
    (current : ResponsibilityState V)
    (length_eq : current.slots.length =
      (seed.generatedState exchangeLaw.compiler).current.slots.length)
    (live : current.slots[
        seed.obligationSlotIndex exchangeLaw.compiler head]? =
      some (.live (seed.obligation exchangeLaw.compiler head))) :
    (fulfillmentEdge authority seed head current length_eq live).target.slots[
        seed.obligationSlotIndex exchangeLaw.compiler leg]? =
      current.slots[seed.obligationSlotIndex exchangeLaw.compiler leg]? := by
  have indices_ne := slotIndex_ne_of_ne (exchangeLaw := exchangeLaw)
    seed distinct
  simp [fulfillmentEdge, NativeResponsibilityProcess.Edge.target, indices_ne]

private def fulfillList
    (seed : exchangeLaw.ExactExchangeSeed)
    (legs : List seed.Leg) (nodup : legs.Nodup)
    (start : ResponsibilityState V)
    (length_eq : start.slots.length =
      (seed.generatedState exchangeLaw.compiler).current.slots.length)
    (live : ∀ leg, leg ∈ legs →
      start.slots[seed.obligationSlotIndex exchangeLaw.compiler leg]? =
        some (.live (seed.obligation exchangeLaw.compiler leg))) :
    ListResult seed start legs := by
  induction legs generalizing start with
  | nil =>
      exact
        { current := start
          run := .nil
          fulfilled := by intro leg member; simp at member
          preserved := by intro leg _notMember; rfl
          slots_length := rfl }
  | cons head tail inductionHypothesis =>
      have headLive := live head (by simp)
      let edge := fulfillmentEdge authority seed head start length_eq headLive
      have edgeLength : edge.target.slots.length =
          (seed.generatedState exchangeLaw.compiler).current.slots.length := by
        rw [fulfillmentEdge_slots_length authority seed head start
          length_eq headLive, length_eq]
      have headNotTail : head ∉ tail := (List.nodup_cons.mp nodup).1
      have tailNodup : tail.Nodup := (List.nodup_cons.mp nodup).2
      have tailLive : ∀ leg, leg ∈ tail →
          edge.target.slots[
              seed.obligationSlotIndex exchangeLaw.compiler leg]? =
            some (.live (seed.obligation exchangeLaw.compiler leg)) := by
        intro leg member
        have distinct : head ≠ leg := by
          intro equal
          subst leg
          exact headNotTail member
        rw [fulfillmentEdge_other_slot authority seed head leg distinct
          start length_eq headLive]
        exact live leg (by simp [member])
      let tailResult := inductionHypothesis tailNodup edge.target edgeLength tailLive
      refine
        { current := tailResult.current
          run := NativeResponsibilityProcess.Run.concatRuns P
            (.step .nil edge) tailResult.run
          fulfilled := ?_
          preserved := ?_
          slots_length := tailResult.slots_length.trans
            (fulfillmentEdge_slots_length authority seed head start
              length_eq headLive) }
      · intro leg member
        rcases List.mem_cons.mp member with equal | tailMember
        · subst leg
          have headAtEdge : edge.target.slots[
                seed.obligationSlotIndex exchangeLaw.compiler head]? =
              some (.terminal
                ⟨seed.obligation exchangeLaw.compiler head,
                  P.boundarySource (authority seed head).event,
                  .fulfilled (authority seed head).receipt⟩) := by
            have index_lt :
                seed.obligationSlotIndex exchangeLaw.compiler head <
                  start.slots.length := by
              rw [length_eq]
              exact seed.obligationSlotIndex_lt exchangeLaw.compiler head
            simp [edge, fulfillmentEdge,
              NativeResponsibilityProcess.Edge.target,
              BoundaryDisposition.targetSlot,
              (authority seed head).disposition_eq, index_lt]
          refine ⟨
            { sourceEvent := P.boundarySource (authority seed head).event
              receipt := (authority seed head).receipt
              present := ?_ }⟩
          rw [tailResult.preserved head headNotTail]
          exact headAtEdge
        · exact tailResult.fulfilled leg tailMember
      · intro leg notMember
        have headNe : head ≠ leg := by
          intro equal
          subst leg
          exact notMember (by simp)
        have tailNotMem : leg ∉ tail := by
          intro member
          exact notMember (by simp [member])
        rw [tailResult.preserved leg tailNotMem]
        exact fulfillmentEdge_other_slot authority seed head leg headNe
          start length_eq headLive

/-- Canonical dependent run which fulfills the whole exhaustive leg list. -/
def fullResult (seed : exchangeLaw.ExactExchangeSeed) :
    ListResult seed
      (seed.generatedState exchangeLaw.compiler).current
      (seed.legList exchangeLaw.compiler) :=
  fulfillList authority seed (seed.legList exchangeLaw.compiler)
    (seed.legList_nodup exchangeLaw.compiler)
    (seed.generatedState exchangeLaw.compiler).current rfl
    (fun leg _member =>
      seed.generatedState_obligationSlotIndex exchangeLaw.compiler leg)

theorem fullResult_fulfills
    (seed : exchangeLaw.ExactExchangeSeed) (leg : seed.Leg) :
    Nonempty (FulfilledSlotAt seed (fullResult authority seed).current leg) :=
  (fullResult authority seed).fulfilled leg
    (seed.leg_mem exchangeLaw.compiler leg)

/-- Canonical exact witness selected from the constructive finite fold. -/
noncomputable def fulfilledSlot
    (seed : exchangeLaw.ExactExchangeSeed) (leg : seed.Leg) :
    FulfilledSlotAt seed (fullResult authority seed).current leg :=
  Classical.choice (fullResult_fulfills authority seed leg)

/-- The source-owned settlement compiler generated by the automatic fold.
Its seed is an already exact exchange seed; callers never supply a current or
a completed run. -/
def settlementCompiler : SourceOwnedSettlementCompiler exchangeLaw where
  SettlementSeed := exchangeLaw.ExactExchangeSeed
  settlementAdmittedAt := fun _ => True
  exchangeSeed := id
  continuation := fun seed =>
    ⟨(fullResult authority seed).current, (fullResult authority seed).run⟩

/-- Exact settlement seed at the same target boundary as its exchange. -/
def exactSettlementSeed (seed : exchangeLaw.ExactExchangeSeed) :
    (settlementCompiler authority).ExactSettlementSeed :=
  ⟨seed, core.targetFace.state game.source, core.target_state_mem, rfl, trivial⟩

/-- Generated whole-settlement occurrence of one exact exchange. -/
def settlementOccurrence (seed : exchangeLaw.ExactExchangeSeed) :
    (settlementCompiler authority).GeneratedSettlementOccurrence :=
  (settlementCompiler authority).occurrenceOfSeed
    (exactSettlementSeed authority seed)

/-- Exact fulfilled archive at one generated exchange leg. -/
noncomputable def fulfilledExchangeLeg
    (seed : exchangeLaw.ExactExchangeSeed) (leg : seed.Leg) :
    FulfilledExchangeLegAt (settlementCompiler authority)
      (settlementOccurrence authority seed) leg := by
  let witnessed := fulfilledSlot authority seed leg
  refine
    { obligation := seed.obligation exchangeLaw.compiler leg
      sourceEvent := witnessed.sourceEvent
      receipt := witnessed.receipt
      present := ?_ }
  have present := witnessed.present
  have index_lt : seed.obligationSlotIndex exchangeLaw.compiler leg <
      (fullResult authority seed).current.slots.length := by
    rw [(fullResult authority seed).slots_length]
    exact seed.obligationSlotIndex_lt exchangeLaw.compiler leg
  rw [List.getElem?_eq_getElem index_lt] at present
  exact Option.some.inj present

/-- Every source-generated leg is fulfilled in the one dependent settlement
run. -/
noncomputable def fullyFulfilled
    (seed : exchangeLaw.ExactExchangeSeed) :
    FullyFulfilledExchangeAt (settlementCompiler authority)
      (settlementOccurrence authority seed) :=
  ⟨fulfilledExchangeLeg authority seed⟩

end AutomaticFullFulfillment

end Settlement
end Society
end ProcessGame
end SaturationMonoid
