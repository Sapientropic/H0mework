import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Rebase.Budget
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Privacy

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.RebaseHistory

open Capitalism.Universal.Source.Program
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open NoFreeProbe
open NoFreeProbe.Prepayment (CanPrepay PaymentOrders registeredTerms)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Community]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {origin leftBase rightBase : RawCurrent Party Good Technology Instrument} {people : List Party} {quantum : ℚ}

variable (home : AnyAuthoritativeRootCurrent.{0}) (replies otherReplies : Replies Party Good Port Technology Instrument)
  (left : Runtime.State (seed := seed) (cut := cut) (community := community) origin people quantum (reserveBase := leftBase))
  (right : Runtime.State (seed := seed) (cut := cut) (community := community) origin people quantum (reserveBase := rightBase))
  (input : OpenPeace.Input Party Good Port Technology Instrument)

structure SameSignedReads : Prop where
  tariff : left.lanes.tariff.read = right.lanes.tariff.read
  payment : left.lanes.payment.read = right.lanes.payment.read
  proposal : left.lanes.openPayment.read = right.lanes.openPayment.read

structure SameReserveContext : Prop where
  claims : leftBase.claims = rightBase.claims
  technology : leftBase.technology = rightBase.technology
  leftStock : ∀ p g, 0 ≤ leftBase.stock p g
  rightStock : ∀ p g, 0 ≤ rightBase.stock p g

local notation "LeftOrders" => OpenPeace.Input.orders
  (ReadAt.read (SignedLanes.payment (Runtime.State.lanes left))) (ReadAt.read (SignedLanes.openPayment (Runtime.State.lanes left))) input
local notation "RightOrders" => OpenPeace.Input.orders
  (ReadAt.read (SignedLanes.payment (Runtime.State.lanes right))) (ReadAt.read (SignedLanes.openPayment (Runtime.State.lanes right))) input
local notation "LeftSee" => (Prepayment.registeredTerms (seed := seed) (cut := cut)
  (community := community) (origin := origin) (people := people) (quantum := quantum) (reserveBase := leftBase))
local notation "RightSee" => (Prepayment.registeredTerms (seed := seed) (cut := cut)
  (community := community) (origin := origin) (people := people) (quantum := quantum) (reserveBase := rightBase))
local notation "LTerms" => registeredTerms (Runtime.State.current left)
local notation "RTerms" => registeredTerms (Runtime.State.current right)

private theorem retained_orders (signed : SameSignedReads left right) : LeftOrders = RightOrders := by
  rw [signed.payment, signed.proposal]

private theorem same_wire_funding (signed : SameSignedReads left right)
    (context : SameReserveContext (leftBase := leftBase) (rightBase := rightBase)
      (Party := Party) (Good := Good) (Technology := Technology) (Instrument := Instrument))
    (terms : LTerms = RTerms) (clock : left.current.physical.raw.clock = right.current.physical.raw.clock)
    (wire : Wire Party Good Port Technology Instrument) :
    CanPrepay LeftSee left.lanes.tariff.read home LeftOrders LTerms left.current.physical.raw.clock wire ↔
      CanPrepay RightSee right.lanes.tariff.read home RightOrders RTerms right.current.physical.raw.clock wire := by
  have law := congrArg Prod.fst terms
  have word := congrArg Prod.snd terms
  change left.current.programme.law = right.current.programme.law at law
  change left.current.recipe.move.word = right.current.recipe.move.word at word
  have sameTariff := signed.tariff
  have sameOrders := retained_orders left right input signed
  have budget := Prepayment.BaseBudget.agrees_across_rebased_reserves left.current.recipe right.current.recipe
    law word context.claims context.technology (bill left.lanes.tariff.read wire) context.leftStock context.rightStock
  constructor
  · intro funded
    refine ⟨funded.scope, funded.stamp.trans clock, sameTariff ▸ funded.screened, funded.standing, ?_, ?_⟩
    · rw [← sameOrders, ← sameTariff, ← clock]
      exact funded.ownOrder
    · apply (Prepayment.uniform_registered_budget_iff right.current _).mpr
      rw [← sameTariff]
      exact budget.mp ((Prepayment.uniform_registered_budget_iff left.current _).mp funded.budget)
  · intro funded
    refine ⟨funded.scope, funded.stamp.trans clock.symm, sameTariff.symm ▸ funded.screened, funded.standing, ?_, ?_⟩
    · rw [sameOrders, sameTariff, clock]
      exact funded.ownOrder
    · apply (Prepayment.uniform_registered_budget_iff left.current _).mpr
      apply budget.mpr
      rw [sameTariff]
      exact (Prepayment.uniform_registered_budget_iff right.current _).mp funded.budget

private theorem same_wire_selection (signed : SameSignedReads left right)
    (context : SameReserveContext (leftBase := leftBase) (rightBase := rightBase))
    (terms : LTerms = RTerms) (clock : left.current.physical.raw.clock = right.current.physical.raw.clock)
    (wire : Wire Party Good Port Technology Instrument) :
    (Prepayment.inspectOrder LeftSee left.lanes.tariff.read home LeftOrders LTerms
      left.current.physical.raw.clock wire).map Subtype.val =
    (Prepayment.inspectOrder RightSee right.lanes.tariff.read home RightOrders RTerms
      right.current.physical.raw.clock wire).map Subtype.val := by
  have equivalent := same_wire_funding home left right input signed context terms clock wire
  unfold Prepayment.inspectOrder
  by_cases funded : CanPrepay LeftSee left.lanes.tariff.read home LeftOrders LTerms left.current.physical.raw.clock wire
  · have rightFunded := equivalent.mp funded
    simp [funded, rightFunded, funded.screened, rightFunded.screened]
  · have rightDenied : ¬ CanPrepay RightSee right.lanes.tariff.read home RightOrders RTerms right.current.physical.raw.clock wire :=
      fun accepted => funded (equivalent.mpr accepted)
    simp [funded, rightDenied]

private theorem findSome_project {α : Type*} {P Q : α → Prop}
    (left : α → Option { a : α // P a }) (right : α → Option { a : α // Q a })
    (equal : ∀ item, (left item).map Subtype.val = (right item).map Subtype.val) :
    ∀ inputs : List α, (inputs.findSome? left).map Subtype.val = (inputs.findSome? right).map Subtype.val := by
  intro inputs
  induction inputs with
  | nil => rfl
  | cons item tail earlier =>
    have exact := equal item
    cases a : left item <;> cases b : right item <;> simp [a, b] at exact
    all_goals simp_all [List.findSome?]

/-- The prepayment gate erases the reserve index at the same public due
agenda. The same signed wire is selected across arbitrary hidden stock
differences, before either side reads private eligibility. -/
theorem same_public_agenda_selects_payment_after_rebase
    (signed : SameSignedReads left right) (context : SameReserveContext (leftBase := leftBase) (rightBase := rightBase))
    (agenda : Runtime.publicAgenda replies left input = Runtime.publicAgenda otherReplies right input) :
    (Runtime.source home replies left input).source.paidWire = (Runtime.source home otherReplies right input).source.paidWire := by
  have terms : LTerms = RTerms := congrArg Prod.fst agenda
  have clock : left.current.physical.raw.clock = right.current.physical.raw.clock :=
    congrArg (fun a => a.2.opensAt) agenda
  have normal : (Prepayment.ordinary left.lanes.tariff.read (input.replies replies) left.current input.due.revision).reply =
      (Prepayment.ordinary right.lanes.tariff.read (input.replies otherReplies) right.current input.due.revision).reply :=
    congrArg (fun a => a.2.reply) agenda
  change AdaptivePeace.paymentAt left.lanes.tariff.read home LeftOrders (input.replies replies)
      left.base.adaptive (fun _ _ => input.due) =
    AdaptivePeace.paymentAt right.lanes.tariff.read home RightOrders (input.replies otherReplies)
      right.base.adaptive (fun _ _ => input.due)
  rw [AdaptivePeace.paymentAt_is_the_original_payment, AdaptivePeace.paymentAt_is_the_original_payment]
  change (Prepayment.advance left.lanes.tariff.read (input.replies replies) left.current registeredTerms home LeftOrders input.due).paidWire =
    (Prepayment.advance right.lanes.tariff.read (input.replies otherReplies) right.current registeredTerms home RightOrders input.due).paidWire
  rw [Prepayment.charged_wire_is_the_selected_order, Prepayment.charged_wire_is_the_selected_order]
  unfold Prepayment.selected Prepayment.selectInAgenda
  rw [normal]
  split
  · rfl
  · unfold Prepayment.selectOrder
    exact findSome_project
      (Prepayment.inspectOrder LeftSee left.lanes.tariff.read home LeftOrders LTerms left.current.physical.raw.clock)
      (Prepayment.inspectOrder RightSee right.lanes.tariff.read home RightOrders RTerms right.current.physical.raw.clock)
      (same_wire_selection home left right input signed context terms clock) input.due.packets

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.RebaseHistory
