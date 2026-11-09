import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Dispatch
import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.AdaptivePeace.Contract

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace

open Capitalism.Universal.Source.Program
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open NoFreeProbe
open NoFreeProbe.Prepayment (PaymentOrders)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {origin : RawCurrent Party Good Technology Instrument} {people : List Party} {quantum : ℚ}

variable (tariff : Tariff Party Good Port Technology Instrument) (home : AnyAuthoritativeRootCurrent.{0})
  (orders : PaymentOrders Party Good Port Technology Instrument)
  (openOrders : OpenOrders Party Good Port Technology Instrument)
  (replies : Replies Party Good Port Technology Instrument)
  (before : State (seed := seed) (cut := cut) (community := community) origin people quantum)

local notation "Packet" => Wire Party Good Port Technology Instrument
local notation "seeTerms" => (Prepayment.registeredTerms (seed := seed) (cut := cut)
  (community := community) (origin := origin) (people := people) (quantum := quantum))

variable (attempt : Proposal Party Good Port Technology Instrument)

local notation "Requested" => (Input.proposal attempt)
local notation "Personal" => Input.orders orders openOrders (Input.proposal attempt)
local notation "Answers" => Input.replies replies (Input.proposal attempt)
local notation "OrderAt" wire => Prepayment.CanPrepay seeTerms tariff home Personal
  (seeTerms before.adaptive.native) before.adaptive.native.physical.raw.clock wire
local notation "Visit" => (source tariff home orders openOrders replies before Requested)

/-- Both original and full-candidate signatures authorize this single
prepaid wire. It is selected at the original material address. -/
theorem proposal_source_paid (consented : OrderAt attempt.wire) :
    (Visit).source = .prepaid attempt.wire consented
      ((consented.budget before.adaptive.native rfl rfl).write (tariff.positive attempt.wire.attempted)) := by
  rw [source, AdaptivePeace.advance, AdaptivePeace.resolve_keeps_the_actual_source,
    Prepayment.registered_dispatch_is_the_exact_private_dispatch]
  have inspected : Prepayment.inspectOrder seeTerms tariff home Personal
      (seeTerms before.adaptive.native) before.adaptive.native.physical.raw.clock attempt.wire =
        some ⟨attempt.wire, consented⟩ := by
    simp [Prepayment.inspectOrder, consented, consented.screened]
  have renewed : (Prepayment.ordinary tariff Answers before.adaptive.native none).reply = .renewed := rfl
  have selection : Prepayment.selected tariff Answers before.adaptive.native seeTerms home Personal (Requested).due =
      some ⟨attempt.wire, consented⟩ := by
    simp [Input.due, Prepayment.selected, Prepayment.selectInAgenda, renewed, Prepayment.selectOrder, inspected]
  simp only [Prepayment.advance, selection, Prepayment.writeSelected]

theorem paid_proposal_scope {wire : Packet} {consented : OrderAt wire}
    {paid : PaidReview before.adaptive.native (bill tariff wire)}
    (actual : (Visit).source = .prepaid wire consented paid) :
    scope tariff home orders openOrders replies before Requested = paidEffects paid attempt.programme := by
  simp only [scope, actual]

theorem a_paid_proposal_gets_the_fixed_refusal {wire : Packet} {consented : OrderAt wire}
    {paid : PaidReview before.adaptive.native (bill tariff wire)}
    (actual : (Visit).source = .prepaid wire consented paid) :
    (observe tariff home orders openOrders replies before Requested).reply = .ordinary (.prepaid .ineligible) := by
  change (Visit).observe.reply = _
  cases landed : Visit with
  | ordinary base quiet =>
    have paidBase : base = .prepaid wire consented paid := by simpa only [landed, AdaptivePeace.Step.source] using actual
    simp only [AdaptivePeace.Step.observe, AdaptivePeace.Step.publicReply, paidBase, Prepayment.Step.reply]
    exact congrArg (fun verdict => AdaptivePeace.Reply.ordinary (.prepaid verdict))
      ((Prepayment.assessment_ineligible_iff Answers paid).mpr rfl)
  | refused _ _ _ _ _ | amended _ _ _ _ => rfl

theorem paid_proposal_payer_loses {wire : Packet} {consented : OrderAt wire}
    {paid : PaidReview before.adaptive.native (bill tariff wire)}
    (actual : (Visit).source = .prepaid wire consented paid)
    (weight : Good → ℚ) (valuable : ∀ good, 0 < weight good) :
    materialPayoff (bill tariff wire)
      (next tariff home orders openOrders replies before Requested).adaptive.native.physical.raw
      before.adaptive.native.move.next weight < 0 := by
  rw [same_physical_successor]
  exact (Visit).paid_attack_is_strictly_costly actual weight valuable

variable (input : Input Party Good Port Technology Instrument)

theorem every_paid_visit_charges_its_actual_payer {wire : Packet}
    (posted : (source tariff home orders openOrders replies before input).source.paidWire = some wire)
    (weight : Good → ℚ) (valuable : ∀ good, 0 < weight good) :
    materialPayoff (bill tariff wire) (next tariff home orders openOrders replies before input).adaptive.native.physical.raw
      before.adaptive.native.move.next weight < 0 := by
  let visit := source tariff home orders openOrders replies before input
  rw [same_physical_successor]
  change visit.source.paidWire = some wire at posted
  cases actual : visit.source with
  | ordinary _ _ => rw [actual] at posted; contradiction
  | prepaid filed consented paid =>
    have selected := congrArg Prepayment.Step.paidWire actual
    have literal : filed = wire := Option.some.inj (selected.symm.trans posted)
    subst wire
    exact visit.paid_attack_is_strictly_costly actual weight valuable

theorem no_unpaid_scope
    (unpaid : (source tariff home orders openOrders replies before input).source.paidWire = none) :
    scope tariff home orders openOrders replies before input = ∅ := by
  cases input with
  | native due => exact scope_native tariff home orders openOrders replies before due
  | proposal packet =>
    cases paid : (source tariff home orders openOrders replies before (.proposal packet)).source with
    | ordinary _ _ => simp only [scope, paid]
    | prepaid wire allowed payment =>
      rw [paid] at unpaid
      contradiction

theorem no_unpaid_repair
    (unpaid : (source tariff home orders openOrders replies before input).source.paidWire = none) :
    amendment tariff home orders openOrders replies before input = none := by
  apply (no_repair_iff tariff home orders openOrders replies before input).mpr
  rw [no_unpaid_scope tariff home orders openOrders replies before input unpaid]
  exact Set.empty_subset _

/-- Failure to post the actual charge gives the same due renewal,
including its generated current and public observation. -/
theorem an_unpaid_proposal_erases_before_the_language_is_read
    (unpaid : (Visit).source.paidWire = none) :
    let renewal : Input Party Good Port Technology Instrument := .native ⟨none, []⟩
    next tariff home orders openOrders replies before Requested =
      next tariff home orders openOrders replies before renewal ∧
    observe tariff home orders openOrders replies before Requested =
      observe tariff home orders openOrders replies before renewal := by
  have posted := AdaptivePeace.resolve_keeps_the_actual_source tariff home Personal Answers before.adaptive
    (Prepayment.advanceRegistered tariff home Personal before.adaptive.native Answers (Requested).due)
  change (Visit).source = _ at posted
  rw [posted, Prepayment.registered_dispatch_is_the_exact_private_dispatch] at unpaid
  have noCharge := Prepayment.unpaid_order_is_the_exact_ordinary_write tariff Answers before.adaptive.native
    seeTerms home Personal (Requested).due unpaid
  have sameVisit :
      (Visit).next = (source tariff home orders openOrders replies before (.native ⟨none, []⟩)).next ∧
      (Visit).observe = (source tariff home orders openOrders replies before (.native ⟨none, []⟩)).observe := by
    unfold source AdaptivePeace.advance
    rw [Prepayment.registered_dispatch_is_the_exact_private_dispatch, noCharge]
    exact ⟨rfl, rfl⟩
  have absent := no_unpaid_repair tariff home orders openOrders replies before Requested (by
    rw [posted, Prepayment.registered_dispatch_is_the_exact_private_dispatch, noCharge]
    rfl)
  have ordinary := (no_repair_iff tariff home orders openOrders replies before (.native ⟨none, []⟩)).mpr
    (Set.empty_subset _)
  exact ⟨by simp only [next, absent, ordinary, sameVisit.1], sameVisit.2⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace
