import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Consumers.OriginalDue.Settlement

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Deployment

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Clearance.Joint.Reinterpreted
open Clearance.Joint.Reinterpreted.OriginalConsumer
open Clearance.Joint.OriginalExchange (claim)
open Clearance (deliveredRaw every_original_row_is_cleared_when_its_key_has_zero_due)
open FixedPoint.OpenPeace.Operational (RecipeConditions)
open FixedPoint.OpenPeace
open FixedPoint.OpenPeace.Network
open FixedPoint.OpenPeace.Network.Runtime.OriginalOrders (quote)
open FixedPoint.NoFreeProbe (bill)
open private afterDue afterSigned dueLaw dueStock signedAfterDue nextRecipe
  from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Consumers.OriginalDue.Settlement
open private original_need_cut from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Consumers.OriginalSource
open private programmeOrder from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Consumers.Original

noncomputable section

/-- The seed is the original unpaid living entrance. The first paid
period lands before the victim is asked to sign. -/
abbrev first := refusingRound 0
abbrev afterRefusal := first.next

private theorem denied : ¬ Funding first.due.next.current (signed false) claim 6 :=
  fun funded => Bool.false_ne_true funded.victim

theorem the_original_victim_refusal_is_written :
    ∃ denied : PaymentIssue first.due.next.current (signed false) claim 6,
      (∃ vote, denied = .victimRefused vote) ∧
      first.motion.event = some (.refused (refuse first.due.next.current denied)) ∧
      afterRefusal.current = (refuse first.due.next.current denied).next := by
  let here := first.due.next.current
  have enough := signedAfterDue
  have wrong : ¬ Funding here (signed false) claim 6 := denied
  cases inspected : checkFunding here (signed false) claim 6 cells allCells with
  | ok funded => exact (wrong funded.down).elim
  | error issue =>
    have event : first.motion.event = some (.refused (refuse here issue)) := by
      change (Scheduled.tryPayment first.due.next (signed false) claim 6 catalogue cells allCells).event = _
      unfold Scheduled.tryPayment
      have literal : checkFunding first.due.next.current (signed false) claim 6 cells allCells = .error issue := inspected
      rw [literal]
      rfl
    refine ⟨issue, ?_, event, first.motion.actual.trans ?_⟩
    · cases issue with
      | sameParty same => exact (enough.distinct same).elim
      | nonpositive bad => exact (bad.not_gt enough.positive).elim
      | overclaim bad => exact (bad.not_ge enough.within).elim
      | notAuthorized bad => exact (bad enough.legal).elim
      | payerRefused bad => cases bad
      | victimRefused vote => exact ⟨vote, rfl⟩
      | shortage person good short => exact (short.not_ge (enough.reserve person good)).elim
    · rw [event]
      rfl

theorem refusedPhysical : afterRefusal.current.physical = first.due.next.current.physical :=
  (Scheduled.refused_funding_keeps_the_paid_due_state
    first.due.next (signed false) claim 6 catalogue cells allCells denied).1

private theorem refusedProgramme : afterRefusal.current.programme = first.due.next.current.programme := by
  change (Scheduled.tryPayment first.due.next (signed false) claim 6 catalogue cells allCells).next.current.programme = _
  unfold Scheduled.tryPayment
  cases checkFunding first.due.next.current (signed false) claim 6 cells allCells with
  | ok fund => exact (denied fund.down).elim
  | error _ => rfl

theorem refusedStock : afterRefusal.current.physical.raw = afterDue :=
  (congrArg (fun physical => physical.raw) refusedPhysical).trans dueStock

theorem refusedLaw : afterRefusal.current.programme = revised :=
  refusedProgramme.trans dueLaw

theorem refusedRows : afterRefusal.current.ledger.stack.balances = [(loss, Original.balance)] :=
  refusal_never_removes_or_delays_the_due_round 1

theorem refusedSix : liveBalance afterRefusal.current claim = 6 := by
  unfold liveBalance
  rw [refusedRows]
  exact the_original_six_survive_the_new_production.1 ▸ the_original_six_survive_the_new_production.2

/-- A fresh answer at the generated refusal current can use the already
paid material period. The receipt binds to that resident and ordinal. -/
private theorem freshFunding : Funding afterRefusal.current (signed true) claim 6 := by
  refine ⟨Bool.false_ne_true, by norm_num, refusedSix.ge, ?_, rfl, rfl, ?_⟩
  · unfold request purpose
    rw [refusedLaw, refusedStock]
    decide +kernel
  · intro person good
    unfold requiredAt
    rw [refusedLaw, refusedStock, original_need_cut]
    cases person <;> cases good <;> decide +kernel

private theorem signedStock : deliveredRaw afterRefusal.current.physical.raw claim 6 = afterSigned :=
  congrArg (fun raw => deliveredRaw raw claim 6) refusedStock

private theorem sustainable :
    cycle ≤ afterRefusal.current.programme.law.duration (deliveredRaw afterRefusal.current.physical.raw claim 6) ∧
    ∃ i : Fin (catalogue afterRefusal.current.programme (deliveredRaw afterRefusal.current.physical.raw claim 6)).length,
      RecipeConditions afterRefusal.current.programme (originalRaw loss) (deliveredRaw afterRefusal.current.physical.raw claim 6)
        (people loss front) (catalogue afterRefusal.current.programme (deliveredRaw afterRefusal.current.physical.raw claim 6))[i] := by
  constructor
  · unfold cycle
    rw [refusedLaw, signedStock, actualTrial.revisedProgramme, actualTrial.revisedStock]
    decide +kernel
  · let input := afterRefusal.current.programme
    let raw := deliveredRaw afterRefusal.current.physical.raw claim 6
    have present : codeFor input refusedLaw raw ∈ catalogue input raw := by
      rw [catalogue_at input refusedLaw]
      exact List.mem_cons_self
    obtain ⟨i, exactCode⟩ := List.mem_iff_get.mp present
    refine ⟨i, ?_⟩
    change RecipeConditions input (originalRaw loss) raw (people loss front) ((catalogue input raw).get i)
    rw [exactCode]
    exact nextRecipe input refusedLaw raw signedStock

private abbrev literalOrder : Proposal Bool Bool Bool Unit Unit :=
  ⟨(Runtime.OriginalOrders.proposal 2).wire, RevisedOrders.shifted⟩

/-- The named source registers its proposed term at the actual review
slot. The original tariff and payment signature are still read there. -/
def reviewOrders : OpenOrders Bool Bool Bool Unit Unit :=
  fun clock bid programme person => programmeOrder literalOrder clock bid programme person

def proposal (home : AnyAuthoritativeRootCurrent.{0}) : Proposal Bool Bool Bool Unit Unit :=
  { literalOrder with wire := { literalOrder.wire with home := home } }

theorem proposal_clock (home : AnyAuthoritativeRootCurrent.{0}) :
    (proposal home).wire.clock = 6 := by
  change (Runtime.OriginalOrders.proposal 2).wire.clock = _
  rw [Runtime.OriginalOrders.clock_at]
  change Settlement.settledCut.raw.clock + (2 : ℚ) = _
  rw [Settlement.settled_raw]
  decide +kernel

theorem original_order (home : AnyAuthoritativeRootCurrent.{0}) :
    (Input.proposal (proposal home)).orders Runtime.OriginalOrders.payment reviewOrders
      (proposal home).wire.clock (bill quote (proposal home).wire) true = true := by
  have original := Runtime.OriginalOrders.original_order 2
  change (Runtime.OriginalOrders.payment literalOrder.wire.clock (bill quote literalOrder.wire) true &&
    Runtime.OriginalOrders.openPayment literalOrder.wire.clock (bill quote literalOrder.wire)
      (Runtime.OriginalOrders.proposal 2).programme true) = true at original
  change (Runtime.OriginalOrders.payment literalOrder.wire.clock (bill quote literalOrder.wire) true &&
    programmeOrder literalOrder literalOrder.wire.clock (bill quote literalOrder.wire) literalOrder.programme true) = true
  refine Bool.and_eq_true_iff.mpr ⟨(Bool.and_eq_true_iff.mp original).1, ?_⟩
  simp [programmeOrder]
  exact ⟨rfl, rfl⟩

abbrev settle := Scheduled.tryPayment afterRefusal (signed true) claim 6 catalogue cells allCells

def clearedCode (paid : PaidWrite afterRefusal.current (signed true) claim 6) :=
  codeFor _ (paid.sameProgramme.trans refusedLaw) paid.next.physical.raw

structure Opening where
  private mk ::
  paid : PaidWrite afterRefusal.current (signed true) claim 6
  disposition : settle.event = some (.paid paid)
  actual : settle.next.current = paid.next
  network : NetworkOpening paid.next quote Runtime.OriginalOrders.payment reviewOrders (clearedCode paid).production
  installed : openNetwork paid.next quote Runtime.OriginalOrders.payment reviewOrders (clearedCode paid) = .inr network
  exactStock : network.state.current.physical.raw = afterSigned
  exactRows : network.state.current.ledger.stack.balances.map Prod.fst = [loss]

theorem opening_is_generated : Nonempty Opening := by
  obtain ⟨paid, actualEvent, actualNext⟩ :=
    Scheduled.tryPayment_writes_when_funded_and_continued afterRefusal (signed true) claim 6 catalogue cells allCells
      freshFunding (.inr sustainable)
  have addresses : paid.next.ledger.stack.balances.map Prod.fst = [loss] := by
    rw [paid.next.origins, ← afterRefusal.current.origins, refusedRows]
    rfl
  have zero := paid.balances claim
  rw [if_pos rfl, refusedSix, sub_self] at zero
  have cleared : ∀ row ∈ paid.next.ledger.stack.balances, row.2.remaining = 0 := by
    intro row listed
    have origin : row.1 = loss := List.mem_singleton.mp (addresses ▸ List.mem_map_of_mem (f := Prod.fst) listed)
    exact every_original_row_is_cleared_when_its_key_has_zero_due claim _ zero row listed
      (congrArg (fun origin => origin.key) origin)
  have stock := paid.stock.trans signedStock
  obtain ⟨network, installed⟩ := opens_network_at_the_original_resident paid.next quote
    Runtime.OriginalOrders.payment reviewOrders (clearedCode paid) cleared
    (nextRecipe _ (paid.sameProgramme.trans refusedLaw) _ stock)
  exact ⟨⟨paid, actualEvent, actualNext, network, installed,
    (congrArg (fun physical => physical.raw) network.physical).trans stock,
    (congrArg (List.map Prod.fst) network.rows).trans addresses⟩⟩

def opening : Opening := Classical.choice opening_is_generated

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Deployment
