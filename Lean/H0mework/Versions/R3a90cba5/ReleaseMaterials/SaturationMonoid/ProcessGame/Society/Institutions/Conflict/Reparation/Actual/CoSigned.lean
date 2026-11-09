import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.CoSigned.Posted

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

/-- Both interpretations feed the same signed receipt and the same original
liability law. A revised position obtains its item from the published root face. -/
inductive JointReceipt (seed : Cut) (key : Key Party Good) where
  | mk (past : Word) (input : Proposal) (position : Fin (Boundary.Actual.items (endAt seed past) input).length)
      (answers : ReceiptAnswers seed)
      (payer : answers past input position key.2.1 = true)
      (victim : answers past input position key.1 = true)
      (positive : 0 < payerCredit seed.native.input.law (Boundary.Actual.items (endAt seed past) input)[position] key)
  | posted (site : PostedPosition seed)
      (payer : site.material.deliveryReplies key.2.1 = true) (victim : site.material.deliveryReplies key.1 = true)
      (positive : 0 < payerCredit site.material.programme.law site.item key)

namespace JointReceipt

variable {seed : Root.Cut Party Good Port Technology Instrument} {key : Key Party Good}

def law : JointReceipt seed key → RawLaw Party Good Port Technology Instrument
  | .mk .. => seed.native.input.law
  | .posted site .. => site.material.programme.law

def items : JointReceipt seed key → List (ExecutionItem Party Good Port Technology Instrument)
  | .mk past input .. => Boundary.Actual.items (endAt seed past) input
  | .posted site .. => site.material.effect.execution.items

def item : JointReceipt seed key → ExecutionItem Party Good Port Technology Instrument
  | .mk past input position .. => (Boundary.Actual.items (endAt seed past) input)[position]
  | .posted site .. => site.item

def replies : JointReceipt seed key → Party → Bool
  | .mk past input position answers .. => answers past input position
  | .posted site .. => site.material.deliveryReplies

def address : JointReceipt seed key → Nat × Nat
  | .mk past _ position .. => (past.length, position.val)
  | .posted site .. => site.address

abbrev quantity (receipt : JointReceipt seed key) := payerCredit receipt.law receipt.item key

theorem payer (receipt : JointReceipt seed key) : receipt.replies key.2.1 = true := by
  cases receipt with
  | mk _ _ _ _ signed _ _ | posted _ signed _ _ => exact signed

theorem victim (receipt : JointReceipt seed key) : receipt.replies key.1 = true := by
  cases receipt with
  | mk _ _ _ _ _ signed _ | posted _ _ signed _ => exact signed

theorem positive (receipt : JointReceipt seed key) : 0 < receipt.quantity := by
  cases receipt with
  | mk _ _ _ _ _ _ positive | posted _ _ _ positive => exact positive

theorem original (receipt : JointReceipt seed key) :
    receipt.item ∈ receipt.items ∧ key.1 ≠ key.2.1 ∧ receipt.item.request.signer = key.2.1 := by
  have signed := positive_payer_credit_has_the_original_payer_and_delivery _ _ _ receipt.positive
  refine ⟨?_, signed.1, signed.2.1⟩
  cases receipt <;> exact List.getElem_mem _

end JointReceipt

variable {seed : Root.Cut Party Good Port Technology Instrument}
  {community : Party → Community}

omit [DecidableEq Community] in
def jointLater (origin : Occurrence seed community) : JointReceipt seed origin.key → Prop
  | .mk past input position .. =>
    (origin.past ++ [origin.input]).IsPrefix past ∨
      origin.past = past ∧ origin.input = input ∧ origin.damage.position.val < position.val
  | .posted site .. => (origin.past ++ [origin.input]).IsPrefix site.anchor

structure JointShare (origin : Occurrence seed community) where
  receipt : JointReceipt seed origin.key
  amount : ℚ
  positive : 0 < amount
  within : amount ≤ receipt.quantity
  afterBirth : jointLater origin receipt

end
end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual
