import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange.Capacity
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Consume

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange

open ResponsibilityLifecycle Source.Program PublicFunction.Repayment
open Abolition.Root Abolition.Root.Registered Abolition.Root.Epoch
open Innovation.Contribution.Pricing.Root.Runtime
open Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Quantities.Exit.Redemption (sourceLaw request)

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "P" => Plan Party Good Port Technology Instrument
local notation "Pos" => Position Party Instrument

def nativeClaims (cut : C) :=
  (nativeAccount cut).current.slots.map (Finance.slotClaim cut.native.input cut.native.depth cut.native.count)

private theorem nativeClaims_heq
    {oldInput newInput : ProgrammeSource.Input Party Good Port Technology Instrument}
    {oldDepth newDepth oldCount newCount : Nat}
    (old : (Finance.process oldInput oldDepth oldCount).GeneratedState)
    (new : (Finance.process newInput newDepth newCount).GeneratedState)
    (input : newInput = oldInput) (depth : newDepth = oldDepth) (count : newCount = oldCount)
    (same : HEq new old) :
    HEq (new.current.slots.map (Finance.slotClaim newInput newDepth newCount))
      (old.current.slots.map (Finance.slotClaim oldInput oldDepth oldCount)) := by
  subst newInput newDepth newCount
  rw [eq_of_heq same]

/-- The actual original settlement spends its full quota on original
registered claims. The address matrix and the ordered claim list are
restrictions of the native account at the root's written successor. -/
structure NativeReconciled (source : C) (position : Pos) (plan : P) (quantity : ℚ) : Prop where
  claims : HEq (nativeClaims (finalAt source position plan quantity)) (nativeClaims source)
  balances : ∀ observed : Pos,
    nativeCapacity (finalAt source position plan quantity) observed = nativeCapacity source observed +
      paymentDelta position.instrument position.debtor position.creditor quantity
        observed.instrument observed.debtor observed.creditor

theorem the_whole_funded_principal_is_consumed_on_its_original_native_address
    {source : C} {position : Pos} {plan : P} {quantity : ℚ}
    (paid : FundedPayment source position plan quantity) :
    NativeReconciled source position plan quantity := by
  let cut := plan.exchanged source
  let settle := request (sourceLaw cut) position quantity
  let body := afterBody cut settle
  let target := finalAt source position plan quantity
  have valid : (sourceLaw cut).Valid cut.raw settle := paid.settles.safe.2.1
  obtain ⟨item, identity, interpreter, consumed⟩ :=
    the_paid_primitive_has_one_literal_native_consumer cut settle
      paid.received.ready paid.received.review rfl valid
  have operation : (item.instruction _ _ _).request.operation =
      .settle position.instrument position.debtor position.creditor quantity :=
    congrArg (fun (entry : ExecutionItem Party Good Port Technology Instrument) => entry.request.operation) identity
  have accepted : (item.interpreter _ _ _).Valid (item.instruction _ _ _).before (item.instruction _ _ _).request := by
    rw [interpreter, identity]
    exact valid
  let account := (Finance.consume _ _ _ item (nativeAccount body)).next _ _ _
  have bodyBook := (the_paid_body_keeps_the_native_account cut settle paid.received.ready).trans
    (a_paid_exchange_keeps_the_whole_original_native_debt_account paid.received)
  have targetBook : HEq (nativeAccount target) account :=
    (nativeAccount_heq_of_eq (finalAt_is_the_original_native_redemption source position plan quantity)).trans consumed
  obtain ⟨tradeInput, tradeDepth, tradeCount⟩ :=
    Quantities.Execution.the_actual_script_keeps_the_original_reader_indices source plan.script
  have parameters := (queued cut settle).advance_parameters
  have bodyInput : body.native.input = source.native.input := parameters.1.trans tradeInput
  have bodyDepth : body.native.depth = source.native.depth := parameters.2.1.trans tradeDepth
  have bodyCount : body.native.count = source.native.count := parameters.2.2.1.trans tradeCount
  obtain ⟨targetInput, targetDepth, targetCount⟩ :=
    Quantities.Execution.the_actual_script_keeps_the_original_reader_indices source
      (fullScript source position plan quantity)
  have original (observed : Pos) : nativeCapacity body observed = nativeCapacity source observed :=
    read_native_same (nativeAccount source) (nativeAccount body) bodyInput bodyDepth bodyCount bodyBook
      (fun input depth count state => ledgerClaims input depth count state.current
        observed.instrument observed.debtor observed.creditor)
  have registered : quantity ≤ nativeCapacity body position := (original position).symm ▸ paid.registered
  have effect (observed : Pos) :=
    the_original_consumer_pays_the_whole_funded_share _ _ _ item position.instrument observed.instrument
      position.debtor position.creditor observed.debtor observed.creditor quantity operation accepted
      (nativeAccount body) registered
  have input := targetInput.trans bodyInput.symm
  have depth := targetDepth.trans bodyDepth.symm
  have count := targetCount.trans bodyCount.symm
  refine ⟨(nativeClaims_heq account (nativeAccount target) input depth count targetBook).trans
    ((heq_of_eq (effect position).2).trans
      (nativeClaims_heq (nativeAccount source) (nativeAccount body) bodyInput bodyDepth bodyCount bodyBook)), ?_⟩
  intro observed
  have balance : nativeCapacity target observed = ledgerClaims body.native.input body.native.depth body.native.count
      account.current observed.instrument observed.debtor observed.creditor :=
    read_native_same account (nativeAccount target) input depth count targetBook
      (fun input depth count state => ledgerClaims input depth count state.current
        observed.instrument observed.debtor observed.creditor)
  rw [balance]
  exact (effect observed).1.trans (congrArg (fun value => value + _) (original observed))

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange
