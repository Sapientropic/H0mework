import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Revision.Payment

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.SourceReserve

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (primitiveScript)
open Reparation (Key)
open Reparation.Actual (ReceiptAnswers Occurrence Script State)
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  (loss : Occurrence seed community) (answers : ReceiptAnswers seed)
  (front : Script Party Good Port Technology Instrument)
  (body : RawEvent Party Good Port Technology Instrument)
  (purpose : Port) (key : Key Party Good)

local notation "Produced" => (front ++ primitiveScript body)
local notation "Amount" => maximumInstallment loss answers Produced key
local notation "Paid" => PaidInstallment loss answers (reserveAt loss Produced) Produced purpose key Amount
abbrev paidSuffix := Produced ++ installment purpose key Amount

/-- This is the original successor indexed by the concatenation of its
literal production, transfer and already generated accounting input. -/
def paidNext (_paid : Paid) :
    State seed community (Occurrence.history loss ++ paidSuffix loss answers front body purpose key) :=
  Occurrence.reached answers loss (paidSuffix loss answers front body purpose key)

theorem the_payment_consumes_the_post_production_material_position
    (actual : ProductionWrite answers loss front body) (paid : Paid) :
    paid.delivery.receipt.item =
      ⟨0, (seed.native.input.law.execute (prefixRaw loss front) 0 body).final,
        paymentRequest purpose key Amount⟩ ∧
    paid.delivery.receipt.address = ((Occurrence.history loss ++ Produced).length, 0) ∧
    paid.delivery.receipt.quantity = Amount := by
  have raw := actual.raw
  rw [Quantities.Execution.endAt_input seed (Occurrence.history loss ++ front)] at raw
  obtain ⟨payer, victim, positive, exactReceipt⟩ :=
    Settlement.the_joint_offer_is_issued_at_the_exact_position _ _ _ _ _ _ paid.delivery.issued
  refine ⟨?_, ?_, paid.delivery.exactQuantity⟩
  · have sameItem := congrArg (fun receipt : Reparation.Actual.JointReceipt seed key => receipt.item) exactReceipt
    rw [sameItem]
    change Reparation.Actual.Allocation.originalItem _ _ _ _ = _
    rw [paid.delivery.item]
    exact congrArg (fun read => ExecutionItem.mk 0 read (paymentRequest purpose key Amount)) raw
  · have exactAddress :=
      (Settlement.a_joint_offer_requires_both_original_replies _ _ _ _ _ _ paid.delivery.issued).2.2
    rw [exactAddress, paid.delivery.position_zero]

theorem the_payment_keeps_all_origins_and_consumes_the_selected_due
    (safe : Occurrence.Eligible answers loss front) (actual : ProductionWrite answers loss front body) (paid : Paid) :
    let next := paidNext loss answers front body purpose key paid
    next.stack.balances.map Prod.fst = (Occurrence.originState loss).stack.balances.map Prod.fst ∧
      dueFor key next.stack.balances = dueFor key (prefixRows loss answers Produced) - Amount ∧
      Quantities.Recorded seed (Occurrence.history loss ++ paidSuffix loss answers front body purpose key) := by
  exact ⟨paid.rows.trans (actual.origins safe),
    (paid.debts key).trans (by rw [if_pos rfl]),
    Occurrence.reached_records_the_whole_history loss _⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.SourceReserve
