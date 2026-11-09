import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Occurrence

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]

local notation "Cut" => Root.Cut Party Good Port Technology Instrument
local notation "Word" => Script Party Good Port Technology Instrument
local notation "Proposal" => Input Party Good Port Technology Instrument
local notation "Law" => RawLaw Party Good Port Technology Instrument
local notation "Item" => ExecutionItem Party Good Port Technology Instrument

omit [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Community] in
/-- Real delivery by the original debtor acting as payer. The claimant's
independent acceptance is read separately at the same material position. -/
def payerCredit (law : Law) (item : Item) (key : Key Party Good) : ℚ :=
  if key.1 ≠ key.2.1 ∧ item.request.signer = key.2.1 ∧ law.Valid item.before item.request then
    match item.request.operation with
    | .transfer payer payee _ =>
        if payer = key.2.1 ∧ payee = key.1 then
          max 0 (flowAt (law.actualCredit item.before item.request) key.1 key.2.2)
        else 0
    | _ => 0
  else 0

omit [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Community] in
theorem positive_payer_credit_has_the_original_payer_and_delivery
    (law : Law) (item : Item) (key : Key Party Good) (positive : 0 < payerCredit law item key) :
    key.1 ≠ key.2.1 ∧ item.request.signer = key.2.1 ∧ law.Valid item.before item.request ∧
      ∃ goods, item.request.operation = .transfer key.2.1 key.1 goods ∧
        flowAt (law.actualCredit item.before item.request) key.1 key.2.2 = payerCredit law item key := by
  by_cases signed : key.1 ≠ key.2.1 ∧ item.request.signer = key.2.1 ∧ law.Valid item.before item.request
  · cases form : item.request.operation <;> simp only [payerCredit, if_pos signed, form] at positive
    case transfer payer payee goods =>
      by_cases exactAddress : payer = key.2.1 ∧ payee = key.1
      · rw [if_pos exactAddress, lt_max_iff] at positive
        have incoming := positive.resolve_left (lt_irrefl 0)
        exact ⟨signed.1, signed.2.1, signed.2.2, goods,
          by rw [← exactAddress.1, ← exactAddress.2],
          by simp only [payerCredit, if_pos signed, form, if_pos exactAddress, max_eq_right incoming.le]⟩
      · simp [exactAddress] at positive
    all_goals exact (lt_irrefl 0 positive).elim
  · simp [payerCredit, signed] at positive

omit [DecidableEq Community] in
/-- This is the same position-indexed function as the installed personal
answer lanes. A payment request supplies neither answer. -/
abbrev ReceiptAnswers (seed : Cut) :=
  (past : Word) → (input : Proposal) →
    Fin (Boundary.Actual.items (endAt seed past) input).length → Party → Bool

/-- Two distinct original parties authorize the same actual material
delivery. The debtor signs the original request and the victim confirms it
through her independent personal answer at that literal position. -/
structure JointReceipt (seed : Cut) (key : Key Party Good) where
  past : Word
  input : Proposal
  position : Fin (Boundary.Actual.items (endAt seed past) input).length
  answers : ReceiptAnswers seed
  payer : answers past input position key.2.1 = true
  victim : answers past input position key.1 = true
  positive : 0 < payerCredit seed.native.input.law
    (Boundary.Actual.items (endAt seed past) input)[position] key

namespace JointReceipt

variable {seed : Root.Cut Party Good Port Technology Instrument} {key : Key Party Good}
  (receipt : JointReceipt seed key)

abbrev item := (Boundary.Actual.items (endAt seed receipt.past) receipt.input)[receipt.position]
abbrev quantity := payerCredit seed.native.input.law receipt.item key
abbrev address : Nat × Nat := (receipt.past.length, receipt.position.val)

theorem original (receipt : JointReceipt seed key) :
    receipt.item ∈ Boundary.Actual.items (endAt seed receipt.past) receipt.input ∧
      key.1 ≠ key.2.1 ∧ receipt.item.request.signer = key.2.1 :=
  let signed := positive_payer_credit_has_the_original_payer_and_delivery
    seed.native.input.law receipt.item key receipt.positive
  ⟨List.getElem_mem _, signed.1, signed.2.1⟩

end JointReceipt

variable {seed : Root.Cut Party Good Port Technology Instrument}
  {community : Party → Community}

omit [DecidableEq Community] in
def jointLater (origin : Occurrence seed community) (receipt : JointReceipt seed origin.key) : Prop :=
  (origin.past ++ [origin.input]).IsPrefix receipt.past ∨
    origin.past = receipt.past ∧ origin.input = receipt.input ∧
      origin.damage.position.val < receipt.position.val

structure JointShare (origin : Occurrence seed community) where
  receipt : JointReceipt seed origin.key
  amount : ℚ
  positive : 0 < amount
  within : amount ≤ receipt.quantity
  afterBirth : jointLater origin receipt

end
end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual
