import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange.Slot
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Redemption.Rate.Readback
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Balances

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange

open Source.Program PublicFunction.Repayment Abolition.Root Abolition.Root.Registered
open Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger
open Quantities.Exit.Redemption (sourceLaw sourceOrigin)

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "P" => Plan Party Good Port Technology Instrument
local notation "Pos" => Position Party Instrument

/-- This is the credit at the second original material position.
Its use as funding follows admission of both material legs. -/
def receivedAt (source : C) (position : Pos) (plan : P) : ℚ :=
  flowAt ((sourceLaw source).actualCredit (plan.middle source).raw plan.delivery) position.debtor
    (Quantities.Exit.Redemption.unit (sourceLaw source) position)

theorem the_old_unit_credit_is_the_original_delivered_quantity
    {source : C} {position : Pos} {plan : P} (paid : Delivered source position plan) :
    receivedAt source position plan = plan.received (sourceLaw source) position := by
  unfold receivedAt
  rw [paid.deliveryFlow.2]
  simp [flowAt, locate, amount, List.map_map, Function.comp_def]

abbrev oldRate (source : C) (position : Pos) := Quantities.Exit.Redemption.rate (sourceLaw source) position

def lower (source : C) (position : Pos) (plan : P) : ℚ :=
  Quantities.Exit.Redemption.lower (sourceLaw source) (sourceOrigin source) (plan.exchanged source).raw position

def materialUpper (source : C) (position : Pos) (plan : P) : ℚ :=
  min (Quantities.Exit.Redemption.upper (sourceLaw source) (sourceOrigin source) (plan.exchanged source).raw position)
    (receivedAt source position plan / oldRate source position)

def nativeCapacity (source : C) (position : Pos) : ℚ :=
  ledgerClaims source.native.input source.native.depth source.native.count (nativeAccount source).current
    position.instrument position.debtor position.creditor

open private entry_le_sum from H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Balances

theorem a_named_principal_is_bounded_by_its_whole_original_address
    (source : C) (position : Pos) (index : Nat) (named : NamesOpenSlot source position index) :
    principalAt source index position.creditor ≤ nativeCapacity source position := by
  obtain ⟨slot, present, address⟩ := Option.map_eq_some_iff.mp named.1
  have instrument := congrArg Prod.fst address
  have debtor := congrArg Prod.snd address
  change (nativeAccount source).current.slots[index]? = some slot at present
  have listed := List.mem_of_getElem? present
  have bound := entry_le_sum (nativeAccount source).current.slots
    (fun slot => slotClaims source.native.input source.native.depth source.native.count slot
      position.instrument position.debtor position.creditor)
    (fun slot member => slotClaims_nonnegative _ _ _ (nativeAccount source) slot member _ _ _) slot listed
  have slotValue : principalAt source index position.creditor =
      slotClaims source.native.input source.native.depth source.native.count slot
        position.instrument position.debtor position.creditor := by
    unfold principalAt slotAt slotClaims
    rw [present]
    have sameInstrument : (Epoch.Finance.slotClaim _ _ _ slot).instrument _ _ _ = position.instrument := instrument
    have sameDebtor : (Epoch.Finance.slotClaim _ _ _ slot).debtor _ _ _ = position.debtor := debtor
    simp only [sameInstrument, sameDebtor, and_self, ↓reduceIte, Option.map_some, Option.getD_some]
  exact slotValue ▸ bound

def upper (source : C) (position : Pos) (plan : P) : ℚ :=
  min (materialUpper source position plan) (nativeCapacity source position)

structure FundedPayment (source : C) (position : Pos) (plan : P) (quantity : ℚ) : Prop where
  received : Delivered source position plan
  positive : 0 < quantity
  settles : Quantities.Exit.Redemption.PaidAt (plan.exchanged source) position quantity
  funded : quantity * oldRate source position ≤ receivedAt source position plan
  registered : quantity ≤ nativeCapacity source position

theorem the_original_exchange_funded_principal_interval_is_exact
    (source : C) (position : Pos) (plan : P) (paid : Delivered source position plan) (quantity : ℚ) :
    FundedPayment source position plan quantity ↔
      position.debtor ≠ position.creditor ∧ 0 < oldRate source position ∧
        0 < quantity ∧ lower source position plan ≤ quantity ∧ quantity ≤ upper source position plan := by
  have domain := Quantities.Exit.Redemption.actual_personal_redemption_domain_is_exact
    (plan.exchanged source) position quantity paid.ready paid.review
  rw [plan.sameLaw, plan.sameOrigin] at domain
  constructor
  · intro payment
    obtain ⟨different, rate, low, high⟩ := domain.mp payment.settles
    exact ⟨different, rate, payment.positive, low,
      le_min (le_min high ((le_div_iff₀ rate).mpr payment.funded)) payment.registered⟩
  · rintro ⟨different, rate, positive, low, high⟩
    have material : quantity ≤ materialUpper source position plan := high.trans (min_le_left _ _)
    exact ⟨paid, positive, domain.mpr ⟨different, rate, low, material.trans (min_le_left _ _)⟩,
      (le_div_iff₀ rate).mp (material.trans (min_le_right _ _)), high.trans (min_le_right _ _)⟩

theorem the_maximum_funded_payment_is_attained
    (source : C) (position : Pos) (plan : P) (paid : Delivered source position plan)
    (different : position.debtor ≠ position.creditor) (rate : 0 < oldRate source position)
    (positive : 0 < upper source position plan) (within : lower source position plan ≤ upper source position plan) :
    FundedPayment source position plan (upper source position plan) ∧
      ∀ quantity, FundedPayment source position plan quantity → quantity ≤ upper source position plan := by
  refine ⟨(the_original_exchange_funded_principal_interval_is_exact _ _ _ paid _).mpr
    ⟨different, rate, positive, within, le_rfl⟩, ?_⟩
  intro quantity payment
  exact ((the_original_exchange_funded_principal_interval_is_exact _ _ _ paid _).mp payment).2.2.2.2

def fullScript (source : C) (position : Pos) (plan : P) (quantity : ℚ) :=
  plan.script ++ Quantities.Exit.Redemption.script (plan.exchanged source) position quantity

abbrev finalAt (source : C) (position : Pos) (plan : P) (quantity : ℚ) :=
  Quantities.Execution.endAt source (fullScript source position plan quantity)

theorem finalAt_is_the_original_native_redemption (source : C) (position : Pos) (plan : P) (quantity : ℚ) :
    finalAt source position plan quantity =
      Innovation.Contribution.Pricing.Root.Runtime.afterNative (plan.exchanged source)
        (Quantities.Exit.Redemption.request (sourceLaw (plan.exchanged source)) position quantity) := by
  change Quantities.Execution.endAt source (plan.script ++ _) = _
  rw [Quantities.Execution.endAt_append]
  rfl

theorem the_actual_exchange_and_redemption_close_the_whole_original_ledger
    {source : C} {position : Pos} {plan : P} {quantity : ℚ}
    (payment : FundedPayment source position plan quantity) :
    Quantities.Recorded source (fullScript source position plan quantity) ∧
      Quantities.Exit.Redemption.Rate.movement (sourceLaw source) position
        (plan.exchanged source).raw (finalAt source position plan quantity).raw =
          ⟨quantity, quantity * oldRate source position, quantity * oldRate source position⟩ ∧
      balance position (finalAt source position plan quantity).raw = balance position source.raw - quantity := by
  refine ⟨Quantities.record source _, ?_, ?_⟩
  · rw [finalAt_is_the_original_native_redemption]
    change Quantities.Exit.Redemption.Rate.movement (sourceLaw source) position (plan.exchanged source).raw
      (Quantities.Execution.endAt (plan.exchanged source) (Quantities.Exit.Redemption.script (plan.exchanged source) position quantity)).raw = _
    rw [payment.settles.readback]
    simpa only [plan.sameLaw] using
      Quantities.Exit.Redemption.Rate.a_paid_leg_reconciles_both_material_addresses_with_its_own_principal
        _ _ _ _ payment.settles.safe.1 payment.settles.safe.2.1
  · rw [finalAt_is_the_original_native_redemption]
    change balance position (Quantities.Execution.endAt (plan.exchanged source)
      (Quantities.Exit.Redemption.script (plan.exchanged source) position quantity)).raw = _
    rw [payment.settles.readback]
    have principal := (Quantities.Exit.Redemption.paid_leg_moves_original_stock_and_claim
      (sourceLaw (plan.exchanged source)) (plan.exchanged source).raw position quantity
      payment.settles.safe.1 payment.settles.safe.2.1).2.2
    exact principal.trans (by simp only [balance, payment.received.originalClaims])

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange
