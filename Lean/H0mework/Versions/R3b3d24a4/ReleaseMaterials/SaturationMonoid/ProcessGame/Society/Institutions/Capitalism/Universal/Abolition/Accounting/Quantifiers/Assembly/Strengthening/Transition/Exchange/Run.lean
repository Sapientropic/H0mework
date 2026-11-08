import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange.Settlement

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange

open Source.Program PublicFunction.Repayment Abolition.Root Abolition.Root.Registered
open Innovation.Contribution.Pricing.Root.Runtime (Ready ReviewAvailable Trace)

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "P" => Plan Party Good Port Technology Instrument
local notation "Pos" => Position Party Instrument

inductive BeforeDelivery (source : C) (position : Pos) (plan : P) (index : Nat) where
  | originalSlot (failed : ¬ NamesOpenSlot source position index)
  | nativePending (failed : ¬ Ready source)
  | originalReview (failed : ¬ ReviewAvailable source)
  | offer (failed : ¬ plan.OfferAdmitted source position)
  | delivery (offered : plan.OfferAdmitted source position) (failed : ¬ plan.DeliveryAdmitted source position)

inductive AfterDelivery (source : C) (position : Pos) (plan : P) (index : Nat) where
  | selfPayment (same : position.debtor = position.creditor)
  | originalRate (failed : oldRate source position ≤ 0)
  | noPositivePrincipal (failed : upper source position plan ≤ 0)
  | livingShortfall (failed : upper source position plan < lower source position plan)
  | originalAllocation (failed : upper source position plan ≤ priorityBefore source position index)

inductive Outcome (source : C) (position : Pos) (plan : P) (index : Nat) where
  | refused (reason : BeforeDelivery source position plan index)
  | delivered (payment : Delivered source position plan) (reason : AfterDelivery source position plan index)
  | settled (payment : Settled source position plan index)

/-- The unaccepted exchange is screened before releasing a leg. After a
completed exchange, a refused settlement retains both real transfers and
the original debt. Only the final checked branch submits the old payment. -/
def produce (source : C) (position : Pos) (plan : P) (index : Nat) : Outcome source position plan index :=
  if named : NamesOpenSlot source position index then
    if ready : Ready source then
      if review : ReviewAvailable source then
        if offered : plan.OfferAdmitted source position then
          if delivered : plan.DeliveryAdmitted source position then
            let paid := pay_exchange source position plan ready review offered delivered
            if distinct : position.debtor ≠ position.creditor then
              if rate : 0 < oldRate source position then
                if positive : 0 < upper source position plan then
                  if compatible : lower source position plan ≤ upper source position plan then
                    if reaches : priorityBefore source position index < upper source position plan then
                      let candidate := (the_maximum_funded_payment_is_attained source position plan
                        paid distinct rate positive compatible).1
                      let routed := (the_named_slot_is_reached_iff_its_original_priority_is_covered candidate named).mpr reaches
                      .settled (pay_original_slot source position plan index named paid distinct rate positive compatible routed)
                    else .delivered paid (.originalAllocation (le_of_not_gt reaches))
                  else .delivered paid (.livingShortfall (lt_of_not_ge compatible))
                else .delivered paid (.noPositivePrincipal (le_of_not_gt positive))
              else .delivered paid (.originalRate (le_of_not_gt rate))
            else .delivered paid (.selfPayment (Decidable.not_not.mp distinct))
          else .refused (.delivery offered delivered)
        else .refused (.offer offered)
      else .refused (.originalReview review)
    else .refused (.nativePending ready)
  else .refused (.originalSlot named)

def Outcome.script {source : C} {position : Pos} {plan : P} {index : Nat} :
    Outcome source position plan index → List (Option (Compile.RawInput Party Good Port Technology Instrument))
  | .refused _ => []
  | .delivered _ _ => plan.script
  | .settled _ => fullScript source position plan (upper source position plan)

abbrev Outcome.current {source : C} {position : Pos} {plan : P} {index : Nat}
    (outcome : Outcome source position plan index) :=
  Quantities.Execution.endAt source outcome.script

abbrev Outcome.remaining {source : C} {position : Pos} {plan : P} {index : Nat}
    (outcome : Outcome source position plan index) :=
  principalAt outcome.current index position.creditor

theorem Outcome.complete {source : C} {position : Pos} {plan : P} {index : Nat}
    (outcome : Outcome source position plan index) : Quantities.Recorded source outcome.script :=
  Quantities.record source outcome.script

theorem the_source_executes_the_funded_maximum_when_it_reaches_the_original_slot
    (source : C) (position : Pos) (plan : P) (index : Nat)
    (named : NamesOpenSlot source position index) (ready : Ready source) (review : ReviewAvailable source)
    (offer : plan.OfferAdmitted source position) (delivery : plan.DeliveryAdmitted source position)
    (distinct : position.debtor ≠ position.creditor) (rate : 0 < oldRate source position)
    (positive : 0 < upper source position plan) (compatible : lower source position plan ≤ upper source position plan)
    (reaches : ReachesSlot source position plan (upper source position plan) index) :
    ∃ actual : Settled source position plan index, produce source position plan index = .settled actual := by
  have candidate := (the_maximum_funded_payment_is_attained source position plan
    (pay_exchange source position plan ready review offer delivery) distinct rate positive compatible).1
  have routed := (the_named_slot_is_reached_iff_its_original_priority_is_covered candidate named).mp reaches
  simp only [produce, dif_pos named, dif_pos ready, dif_pos review, dif_pos offer, dif_pos delivery,
    dif_pos distinct, dif_pos rate, dif_pos positive, dif_pos compatible, dif_pos routed]
  exact ⟨pay_original_slot source position plan index named
    (pay_exchange source position plan ready review offer delivery) distinct rate positive compatible reaches, trivial⟩

theorem any_funded_payment_reaching_the_old_slot_forces_actual_maximum_settlement
    {source : C} {position : Pos} {plan : P} {index : Nat} {quantity : ℚ}
    (named : NamesOpenSlot source position index) (funded : FundedPayment source position plan quantity)
    (reaches : ReachesSlot source position plan quantity index) :
    ∃ actual : Settled source position plan index, produce source position plan index = .settled actual := by
  have sourceReady : Ready source ∧ ReviewAvailable source := by
    have trace := funded.received.trace
    cases trace with
    | cons _ _ _ _ ready review _ _ _ => exact ⟨ready, review⟩
  obtain ⟨distinct, rate, positive, lowerBound, upperBound⟩ :=
    (the_original_exchange_funded_principal_interval_is_exact _ _ _ funded.received _).mp funded
  have room := positive.trans_le upperBound
  have inside := lowerBound.trans upperBound
  have cap := (the_maximum_funded_payment_is_attained source position plan funded.received distinct rate room inside).1
  have priority := (the_named_slot_is_reached_iff_its_original_priority_is_covered funded named).mp reaches
  have full := (the_named_slot_is_reached_iff_its_original_priority_is_covered cap named).mpr
    (priority.trans_le upperBound)
  exact the_source_executes_the_funded_maximum_when_it_reaches_the_original_slot _ _ _ _
    named sourceReady.1 sourceReady.2 funded.received.offer funded.received.delivery distinct rate room inside full

theorem an_unavailable_delivery_keeps_the_original_stock_and_debt
    (source : C) (position : Pos) (plan : P) (index : Nat)
    (absent : ¬ plan.DeliveryAdmitted source position) :
    (produce source position plan index).script = [] ∧
      (produce source position plan index).current.raw = source.raw ∧
      (produce source position plan index).remaining = principalAt source index position.creditor := by
  have empty : (produce source position plan index).script = [] := by
    unfold produce
    split <;> try rfl
    split <;> try rfl
    split <;> try rfl
    split <;> try rfl
  have current : (produce source position plan index).current = source := by
    change Quantities.Execution.endAt source (produce source position plan index).script = source
    rw [empty]
    rfl
  exact ⟨empty, congrArg Evolving.Epoch.Current.raw current,
    congrArg (fun cut => principalAt cut index position.creditor) current⟩

theorem after_delivery_a_refused_settlement_preserves_the_original_slot
    {source : C} {position : Pos} {plan : P} {index : Nat}
    (delivered : Delivered source position plan) (reason : AfterDelivery source position plan index) :
    (Outcome.delivered delivered reason).remaining = principalAt source index position.creditor ∧
      HEq (nativeAccount (Outcome.delivered delivered reason).current) (nativeAccount source) :=
  ⟨the_exchange_preserves_every_old_slot_balance_at_its_original_address delivered _ _,
    a_paid_exchange_keeps_the_whole_original_native_debt_account delivered⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange
