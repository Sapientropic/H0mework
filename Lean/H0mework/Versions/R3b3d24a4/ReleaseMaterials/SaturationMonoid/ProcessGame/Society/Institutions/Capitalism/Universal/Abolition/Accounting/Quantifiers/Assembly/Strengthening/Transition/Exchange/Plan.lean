import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Redemption.Native

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange

open Source.Program PublicFunction.Repayment Abolition.Root Abolition.Root.Registered

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

local notation "Q" => Request Party Good Port Technology Instrument
local notation "L" => RawLaw Party Good Port Technology Instrument
local notation "R" => RawCurrent Party Good Technology Instrument

/-- Both original instructions are supplied by their respective bearers.
The exchanged bundles are kept in their own physical units. -/
structure Plan (Party Good Port Technology Instrument : Type) where
  supplier : Party
  foreign : Bundle Good
  returns : Bundle Good
  offer : Request Party Good Port Technology Instrument
  delivery : Request Party Good Port Technology Instrument

variable (plan : Plan Party Good Port Technology Instrument)

def Plan.word : RawEvent Party Good Port Technology Instrument :=
  [plan.offer, plan.delivery]

abbrev Plan.received (law : L) (position : Position Party Instrument) : ℚ :=
  amount Good plan.returns (Quantities.Exit.Redemption.unit law position)

def Plan.OfferMatches (law : L) (position : Position Party Instrument) : Prop :=
  plan.supplier ≠ position.debtor ∧ plan.foreign ≠ [] ∧
    (∀ item ∈ plan.foreign,
      item.1 ≠ Quantities.Exit.Redemption.unit law position ∧ 0 < item.2) ∧
    plan.offer.signer = position.debtor ∧ plan.offer.consents = [] ∧
    plan.offer.operation = .transfer position.debtor plan.supplier plan.foreign

def Plan.DeliveryMatches (law : L) (position : Position Party Instrument) : Prop :=
  0 < plan.received law position ∧
    plan.delivery.signer = plan.supplier ∧ plan.delivery.consents = [] ∧
    plan.delivery.operation = .transfer plan.supplier position.debtor plan.returns

private def decideTransfer (operation : Operation Party Good Technology Instrument)
    (sender recipient : Party) (goods : Bundle Good) :
    Decidable (operation = .transfer sender recipient goods) := by
  cases operation
  case transfer actualSender actualRecipient actualGoods =>
    exact if same : actualSender = sender ∧ actualRecipient = recipient ∧ actualGoods = goods then
      isTrue (by obtain ⟨rfl, rfl, rfl⟩ := same; rfl)
    else
      isFalse (fun matched => same (Operation.transfer.inj matched))
  all_goals exact isFalse (fun impossible => by cases impossible)

instance (law : L) (position : Position Party Instrument) :
    Decidable (plan.OfferMatches law position) := by
  unfold Plan.OfferMatches
  letI := decideTransfer plan.offer.operation position.debtor plan.supplier plan.foreign
  infer_instance

instance (law : L) (position : Position Party Instrument) :
    Decidable (plan.DeliveryMatches law position) := by
  unfold Plan.DeliveryMatches
  letI := decideTransfer plan.delivery.operation plan.supplier position.debtor plan.returns
  infer_instance

/-- A debit tests every actual outgoing address against the original
living and maintenance stock. The test precedes any new incoming stock. -/
def Protected (law : L) (origin cut : R) (instruction : Q) : Prop :=
  ∀ item ∈ law.debit cut instruction,
    Quantities.Exit.Redemption.essentials law origin item.1.1 item.1.2 ≤
      cut.stock item.1.1 item.1.2 - flowAt (law.debit cut instruction) item.1.1 item.1.2

instance (law : L) (origin cut : R) (instruction : Q) :
    Decidable (Protected law origin cut instruction) := by
  unfold Protected
  infer_instance

theorem a_material_transfer_retains_every_original_claim (law : L) (cut : R)
    (instruction : Q) (sender recipient : Party) (goods : Bundle Good)
    (transfer : instruction.operation = .transfer sender recipient goods) :
    (law.step cut instruction).claims = cut.claims := by
  unfold RawLaw.step
  split
  · simp [RawLaw.paidStep, RawLaw.nextClaims, transfer]
  · rfl

omit [DecidableEq Instrument] in
theorem a_paid_transfer_has_its_original_debit_and_credit (law : L) (cut : R)
    (instruction : Q) (sender recipient : Party) (goods : Bundle Good)
    (transfer : instruction.operation = .transfer sender recipient goods)
    (valid : law.Valid cut instruction) :
    law.actualDebit cut instruction = locate sender goods ∧
      law.actualCredit cut instruction = locate recipient goods := by
  simp [RawLaw.actualDebit, RawLaw.actualCredit, RawLaw.debit, RawLaw.credit, valid, transfer]

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange
