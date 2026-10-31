import H0mework.Foundation.Responsibility.Lifecycle

/-!
# Generated settlement on an exact responsibility edge

Settlement is a readout of one exact `NativeResponsibilityProcess.Edge.cross`.
The boundary disposition is never supplied by a consumer.  Live and terminal
target slots are distinguished exactly; fulfillment is narrower than generic
terminal closure, while supersession and bearer-release routes remain live.

An accounted open settlement additionally carries an independent next
boundary event for its generated target obligation.  A protected-interest
field alone is not treated as a consumer.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Settlement

open ResponsibilityLifecycle

universe u

/-- One exact review edge selected from the fixed responsibility process. -/
structure ExactSettlementEdge
    {V : Vocabulary.{u}} (P : NativeResponsibilityProcess V)
    (source : ResponsibilityState V) where
  slot : Fin source.slots.length
  obligation : AdmittedObligation V
  present : source.slots.get slot = .live obligation
  event : P.BoundaryEvent obligation

namespace ExactSettlementEdge

variable {V : Vocabulary.{u}} {P : NativeResponsibilityProcess V}
variable {source : ResponsibilityState V}

def edge (settlement : ExactSettlementEdge P source) : P.Edge source :=
  .cross settlement.slot settlement.obligation settlement.present
    settlement.event

def sourceEvent (settlement : ExactSettlementEdge P source) : V.SourceEvent :=
  P.boundarySource settlement.event

def disposition (settlement : ExactSettlementEdge P source) :
    BoundaryDisposition V settlement.obligation settlement.sourceEvent :=
  P.boundaryDisposition settlement.event

/-- Exact lifecycle classification.  Only `fulfilled` means full settlement;
the remaining final constructors retain their distinct legal meaning. -/
inductive Class where
  | progressed
  | progressedAndTransferred
  | maintained
  | deferred
  | narrowed
  | acceptedTransfer
  | fulfilled
  | waived
  | invalidated
  | abandonedWithConsequence
  | impossibleResidueAccepted
  | supersededRollover
  | bearerReleaseTransferred
  | jurisdictionEndedWithResidue
  | consentRevokedWithResidue
  | capacityReleasedWithResidue
  deriving DecidableEq, Repr

def classification (settlement : ExactSettlementEdge P source) : Class :=
  match settlement.disposition with
  | .carry (.progressed ..) => .progressed
  | .carry (.progressedAndTransferred ..) => .progressedAndTransferred
  | .carry (.maintained ..) => .maintained
  | .carry (.deferred ..) => .deferred
  | .carry (.narrowed ..) => .narrowed
  | .carry (.transferred ..) => .acceptedTransfer
  | .terminal (.final (.fulfilled _)) => .fulfilled
  | .terminal (.final (.waived _)) => .waived
  | .terminal (.final (.invalidated _)) => .invalidated
  | .terminal (.final (.abandonedWithConsequence _)) =>
      .abandonedWithConsequence
  | .terminal (.final (.impossibleResidueAccepted _)) =>
      .impossibleResidueAccepted
  | .terminal (.superseded _) => .supersededRollover
  | .bearerRelease (.transferredAndAccepted ..) => .bearerReleaseTransferred
  | .bearerRelease (.jurisdictionEndedWithResidue ..) =>
      .jurisdictionEndedWithResidue
  | .bearerRelease (.consentRevoked ..) => .consentRevokedWithResidue
  | .bearerRelease (.capacityReleasedWithResidue ..) =>
      .capacityReleasedWithResidue

/-- The changed target slot remains live with this exact obligation. -/
structure LiveResidualAt (settlement : ExactSettlementEdge P source) where
  obligation : AdmittedObligation V
  targetSlot_eq : settlement.disposition.targetSlot = .live obligation

/-- The changed target slot is terminal with this exact archive. -/
structure ClosedSettlementAt (settlement : ExactSettlementEdge P source) where
  archive : TerminalArchive V
  targetSlot_eq : settlement.disposition.targetSlot = .terminal archive

/-- Every exact settlement edge is live-open or terminal-closed. -/
theorem live_or_closed (settlement : ExactSettlementEdge P source) :
    Nonempty (LiveResidualAt settlement) ∨
      Nonempty (ClosedSettlementAt settlement) := by
  cases dispositionEq : settlement.disposition with
  | carry carry =>
      exact Or.inl ⟨⟨carry.target, by rw [dispositionEq]; rfl⟩⟩
  | terminal receipt =>
      cases receipt with
      | final finalReceipt =>
          exact Or.inr
            ⟨⟨⟨settlement.obligation, settlement.sourceEvent, finalReceipt⟩,
              by rw [dispositionEq]; rfl⟩⟩
      | superseded supersession =>
          exact Or.inl
            ⟨⟨supersession.successor, by rw [dispositionEq]; rfl⟩⟩
  | bearerRelease release =>
      exact Or.inl ⟨⟨release.target, by rw [dispositionEq]; rfl⟩⟩

theorem live_not_closed (settlement : ExactSettlementEdge P source) :
    Nonempty (LiveResidualAt settlement) →
      ¬ Nonempty (ClosedSettlementAt settlement) := by
  rintro ⟨openSettlement⟩ ⟨closedSettlement⟩
  have impossible :
      ObligationSlot.live openSettlement.obligation =
        .terminal closedSettlement.archive :=
    openSettlement.targetSlot_eq.symm.trans closedSettlement.targetSlot_eq
  cases impossible

theorem live_target_unique (settlement : ExactSettlementEdge P source) :
    ∀ first last : LiveResidualAt settlement,
      first.obligation = last.obligation := by
  intro first last
  have equalSlots : ObligationSlot.live first.obligation = .live last.obligation :=
    first.targetSlot_eq.symm.trans last.targetSlot_eq
  exact ObligationSlot.live.inj equalSlots

/-- A live residual really occupies the changed slot of the generated target
state. -/
theorem LiveResidualAt.target_live
    {settlement : ExactSettlementEdge P source}
    (openSettlement : LiveResidualAt settlement) :
    settlement.edge.target.slots[settlement.slot.val]? =
      some (.live openSettlement.obligation) := by
  unfold edge
  rw [NativeResponsibilityProcess.cross_target_slot]
  exact congrArg some openSettlement.targetSlot_eq

def targetSlot (settlement : ExactSettlementEdge P source) :
    Fin settlement.edge.target.slots.length :=
  ⟨settlement.slot.val, by
    simp [ExactSettlementEdge.edge,
      NativeResponsibilityProcess.Edge.target,
      settlement.slot.isLt]⟩

theorem LiveResidualAt.target_present
    {settlement : ExactSettlementEdge P source}
    (openSettlement : LiveResidualAt settlement) :
    settlement.edge.target.slots.get settlement.targetSlot =
      .live openSettlement.obligation := by
  have live := openSettlement.target_live
  have getEq :
      settlement.edge.target.slots[settlement.slot.val]? =
        some (settlement.edge.target.slots.get settlement.targetSlot) :=
    List.getElem?_eq_getElem settlement.targetSlot.isLt
  rw [getEq] at live
  exact Option.some.inj live

def LiveResidualAt.residualBearer
    {settlement : ExactSettlementEdge P source}
    (openSettlement : LiveResidualAt settlement) : V.Bearer :=
  openSettlement.obligation.bearer

def LiveResidualAt.protectedInterest
    {settlement : ExactSettlementEdge P source}
    (openSettlement : LiveResidualAt settlement) : V.ProtectedInterest :=
  openSettlement.obligation.beneficiary

def LiveResidualAt.residual
    {settlement : ExactSettlementEdge P source}
    (openSettlement : LiveResidualAt settlement) : V.Residual :=
  openSettlement.obligation.residual

/-- A later activated process event consuming the generated live target
obligation.  This is a downstream edge adapter, not part of current open
authority. -/
structure ResidualConsumerAt
    {settlement : ExactSettlementEdge P source}
    (openSettlement : LiveResidualAt settlement) where
  event : P.BoundaryEvent openSettlement.obligation

/-- The consumer is an exact next process edge from the generated target
state, not an event-shaped promise. -/
def ResidualConsumerAt.edge
    {settlement : ExactSettlementEdge P source}
    {openSettlement : LiveResidualAt settlement}
    (consumer : ResidualConsumerAt openSettlement) :
    P.Edge settlement.edge.target :=
  .cross settlement.targetSlot openSettlement.obligation
    openSettlement.target_present consumer.event

theorem ResidualConsumerAt.history_append
    {settlement : ExactSettlementEdge P source}
    {openSettlement : LiveResidualAt settlement}
    (consumer : ResidualConsumerAt openSettlement) :
    consumer.edge.target.history =
      settlement.edge.target.history ++ [consumer.edge.lifecycleEvent] :=
  consumer.edge.history_append

def ResidualConsumerAt.sourceOwnership
    {settlement : ExactSettlementEdge P source}
    {openSettlement : LiveResidualAt settlement}
    (consumer : ResidualConsumerAt openSettlement) :
    SourceOwnsResponsibilityIncidence V (P.boundarySource consumer.event)
      openSettlement.obligation :=
  P.boundarySourceOwnership consumer.event

/-- Exact full settlement, strictly the `fulfilled` final constructor. -/
structure FulfilledSettlementAt
    (settlement : ExactSettlementEdge P source) where
  receipt : V.FulfilledAt settlement.sourceEvent settlement.obligation.content
    settlement.obligation.scope
  disposition_eq : settlement.disposition =
    .terminal (.final (.fulfilled receipt))

def FulfilledSettlementAt.closed
    {settlement : ExactSettlementEdge P source}
    (fulfilled : FulfilledSettlementAt settlement) :
    ClosedSettlementAt settlement := by
  refine ⟨{
    obligation := settlement.obligation
    sourceEvent := settlement.sourceEvent
    receipt := .fulfilled fulfilled.receipt
  }, ?_⟩
  rw [fulfilled.disposition_eq]
  rfl

/-- Exact supersession is a live rollover, not a final settlement. -/
structure SupersededRolloverAt
    (settlement : ExactSettlementEdge P source) where
  receipt : SupersessionReceipt V settlement.obligation settlement.sourceEvent
  disposition_eq : settlement.disposition = .terminal (.superseded receipt)

def SupersededRolloverAt.open
    {settlement : ExactSettlementEdge P source}
    (rollover : SupersededRolloverAt settlement) :
    LiveResidualAt settlement := by
  exact ⟨rollover.receipt.successor, by rw [rollover.disposition_eq]; rfl⟩

/-- Bearer release keeps a live residual route. -/
structure RoutedResidualAt
    (settlement : ExactSettlementEdge P source) where
  receipt : BearerReleaseReceipt V settlement.obligation settlement.sourceEvent
  disposition_eq : settlement.disposition = .bearerRelease receipt

def RoutedResidualAt.open
    {settlement : ExactSettlementEdge P source}
    (routed : RoutedResidualAt settlement) : LiveResidualAt settlement := by
  exact ⟨routed.receipt.target, by rw [routed.disposition_eq]; rfl⟩

end ExactSettlementEdge
end Settlement
end Society
end ProcessGame
end SaturationMonoid
