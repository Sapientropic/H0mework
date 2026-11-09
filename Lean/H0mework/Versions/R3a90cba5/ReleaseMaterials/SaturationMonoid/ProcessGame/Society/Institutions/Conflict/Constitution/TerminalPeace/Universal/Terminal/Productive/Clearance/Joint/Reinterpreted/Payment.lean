import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Funding
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Allocation

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt)
open Reparation Reparation.Actual
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open private Current.mk from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Current

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {loss : Reparation.Actual.Occurrence seed community} {front : Script Party Good Port Technology Instrument}

variable (before : Current loss front)
  (answers : DeliveryAnswers Party Good Port Technology Instrument)
  (key : Key Party Good) (quantity : ℚ)

local notation "At" => anchor loss front
local notation "Pay" => request before key quantity
local notation "Sign" => signAt before answers key quantity
local notation "Item" => ExecutionItem.mk 0 before.physical.raw Pay

def submittedPayment : PostedMaterial Party Good Port Technology Instrument :=
  ⟨before.ordinal, before.programme, before.physical, .primitive Pay, Sign⟩

structure PaidWrite where
  visit : Installation.Core.Landed seed community (endAt seed At)
    (PostedMaterial Party Good Port Technology Instrument)
  exactVisit : visit = Installation.Core.publish before.ledger (submittedPayment before answers key quantity) true
  ordered : (At).length ≤ visit.read.ordinal
  accepted : visit.read.effect.isAccepted = true
  position : Fin visit.read.effect.execution.items.length
  receipt : JointReceipt seed key
  issued : Settlement.postedOffer (Settlement.postedPosition At visit ordered accepted position) key = some receipt
  item : receipt.item = Item
  amount : receipt.quantity = quantity
  next : Current loss front
  allocated : next.ledger = Settlement.consumePosted At visit ordered accepted position
  afterPhysical : next.physical = visit.read.effect.next
  stock : next.physical.raw = deliveredRaw before.physical.raw key quantity
  kept : ProtectedDelivery before key quantity
  noDamage : ∀ item ∈ visit.read.effect.execution.items, ∀ key,
    Reparation.loss before.programme.law community item key = 0
  balances : ∀ other, liveBalance next other = liveBalance before other -
    (if other = key then quantity else 0)
  ordinal : next.ordinal = before.ordinal + 1
  sameProgramme : next.programme = before.programme

set_option maxHeartbeats 900000 in
/-- Both material acceptance and the two owner responses are read before
publishing. Allocation then consumes the exact published position. -/
def writeFunded (paid : Funding before answers key quantity) : PaidWrite before answers key quantity := by
  let read := submittedPayment before answers key quantity
  let visit := Installation.Core.publish before.ledger read true
  have readAt : visit.read = read := Installation.Core.publish_reads_the_exact_payload _ _ _
  obtain ⟨accept, items, physical⟩ := transfer_is_the_actual_primitive before.programme before.physical
    (purpose before key) key quantity paid.legal
  have accepted : visit.read.effect.isAccepted = true := readAt.symm ▸ accept
  have exactItems : visit.read.effect.execution.items = [Item] := readAt.symm ▸ items
  have ordered : (At).length ≤ visit.read.ordinal := by rw [readAt]; exact before.afterAnchor
  let position : Fin visit.read.effect.execution.items.length :=
    ⟨0, by rw [exactItems]; exact Nat.zero_lt_one⟩
  let site := Settlement.postedPosition At visit ordered accepted position
  have exactItem : site.item = Item := List.mem_singleton.mp (exactItems ▸ List.getElem_mem position.isLt)
  have lawAt : site.material.programme.law = before.programme.law :=
    congrArg (fun payload : PostedMaterial Party Good Port Technology Instrument => payload.programme.law) readAt
  have readReplies : site.material.deliveryReplies = Sign :=
    congrArg PostedMaterial.deliveryReplies readAt
  have exactCredit : payerCredit site.material.programme.law site.item key = quantity := by
    rw [lawAt, exactItem]
    exact transfer_payerCredit before.programme before.physical (purpose before key) key quantity
      paid.legal paid.distinct paid.positive
  have payer : site.material.deliveryReplies key.2.1 = true := by rw [readReplies]; exact paid.payer
  have victim : site.material.deliveryReplies key.1 = true := by rw [readReplies]; exact paid.victim
  have positive : 0 < payerCredit site.material.programme.law site.item key := exactCredit.symm ▸ paid.positive
  let receipt : JointReceipt seed key := .posted site payer victim positive
  have issued : Settlement.postedOffer site key = some receipt := by
    unfold Settlement.postedOffer
    have both : site.material.deliveryReplies key.2.1 = true ∧ site.material.deliveryReplies key.1 = true ∧
        0 < payerCredit site.material.programme.law site.item key := ⟨payer, victim, positive⟩
    rw [dif_pos both]
  have only (other : Key Party Good) (different : other ≠ key) : Settlement.postedOffer site other = none := by
    have zero := transfer_has_only_its_own_key before.programme before.physical (purpose before key) key quantity
      paid.legal other different
    have absent : payerCredit site.material.programme.law site.item other = 0 := by
      rw [lawAt, exactItem]
      exact zero
    unfold Settlement.postedOffer
    have blocked : ¬ (site.material.deliveryReplies other.2.1 = true ∧
        site.material.deliveryReplies other.1 = true ∧ 0 < payerCredit site.material.programme.law site.item other) := by
      rw [absent]
      exact fun checked => (lt_irrefl 0) checked.2.2
    rw [dif_neg blocked]
  let landed := Settlement.consumePosted At visit ordered accepted position
  let next := Current.mk landed visit.read.effect.next before.programme (before.ordinal + 1)
    (before.afterAnchor.trans (Nat.le_succ _)) before.terms
    ((Settlement.consumePosted_keeps_the_original_addresses At visit ordered accepted position).trans before.origins) before.inherited
  have stock : visit.read.effect.next.raw = deliveredRaw before.physical.raw key quantity := by
    rw [readAt]
    exact physical
  refine ⟨visit, rfl, ordered, accepted, position, receipt, issued, exactItem, exactCredit,
    next, rfl, rfl, stock, paid.reserve, ?_, ?_, rfl, rfl⟩
  · intro item actual other
    rw [exactItems] at actual
    rcases List.mem_singleton.mp actual with rfl
    have own : Supply.OwnItem before.programme.law [key.2.1] Item :=
      ⟨rfl, List.mem_cons_self, rfl, paid.legal⟩
    exact own.opens_no_coercive_loss community other
  · intro other
    have balances := posted_key_exact At visit ordered accepted position key issued only before.origins other
    have limit := Settlement.posted_limit_eq_quantity site key receipt issued
    change Settlement.deliveryLimit visit.read.programme.law site.item key.2.2 = receipt.quantity at limit
    have residual : min (Settlement.deliveryLimit visit.read.programme.law site.item key.2.2)
        (liveBalance before key) = quantity := by
      rw [limit, show receipt.quantity = quantity from exactCredit, min_eq_left paid.within]
    change liveBalance next other = liveBalance before other -
      (if other = key then min (Settlement.deliveryLimit visit.read.programme.law site.item key.2.2)
        (liveBalance before key) else 0) at balances
    rwa [residual] at balances

theorem PaidWrite.receipt_is_stamped_on_its_actual_visit (paid : PaidWrite before answers key quantity) :
    paid.receipt.address.1 = before.ordinal := by
  have same := (Settlement.posted_offer_reads_both_actual_replies
    (Settlement.postedPosition At paid.visit paid.ordered paid.accepted paid.position) key paid.receipt paid.issued).1
  rw [same]
  change paid.visit.read.ordinal = before.ordinal
  rw [paid.exactVisit]
  rfl

theorem PaidWrite.whole_successor (paid : PaidWrite before answers key quantity) :
    (⟨paid.visit.state.world,
      ((paid.visit.state.moveFirst
        (Settlement.allocatePosted At paid.visit paid.ordered paid.accepted paid.position).move true).sequential
          paid.visit.state.resident paid.visit.state.exactSupport.symm).target.targetAnswerAndNext.nextCurrent⟩ :
      AnyAuthoritativeRootCurrent) = paid.next.ledger.resident.erase := by
  rw [paid.allocated]
  exact Settlement.consumePosted_is_the_whole_successor _ _ _ _ _

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted
