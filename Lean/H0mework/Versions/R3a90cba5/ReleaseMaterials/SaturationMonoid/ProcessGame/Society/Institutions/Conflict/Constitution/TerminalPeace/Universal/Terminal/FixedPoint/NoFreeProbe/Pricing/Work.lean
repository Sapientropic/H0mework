import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment.Finitary

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Pricing

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "Law" => RawLaw Party Good Port Technology Instrument
local notation "Raw" => RawCurrent Party Good Technology Instrument
local notation "Word" => RawEvent Party Good Port Technology Instrument
local notation "Item" => ExecutionItem Party Good Port Technology Instrument

/-- Measure native resource consumption at its actual inventory positions.
Transfers and returning stock must be reconciled before they can enter a fee. -/
def workAdmissible (law : Law) (bearer : Party) (item : Item) : Prop :=
  law.Valid item.before item.request ∧
  (∀ lot ∈ law.actualDebit item.before item.request, lot.1.1 = bearer) ∧
  law.actualCredit item.before item.request = []

instance (law : Law) (bearer : Party) (item : Item) : Decidable (workAdmissible law bearer item) := by
  unfold workAdmissible
  infer_instance

structure MeteredWork (law : Law) (before : Raw) (bearer : Party) where
  word : Word
  admitted : ∀ item ∈ law.rawItems before word, workAdmissible law bearer item

def WorkFailure (law : Law) (before : Raw) (bearer : Party) (word : Word) :=
  { item : Item // item ∈ law.rawItems before word ∧ ¬ workAdmissible law bearer item }

def inspectWork (law : Law) (before : Raw) (bearer : Party) (word : Word) :
    WorkFailure law before bearer word ⊕ { work : MeteredWork law before bearer // work.word = word } :=
  let items := law.rawItems before word
  match first : items.find? (fun item => decide (¬ workAdmissible law bearer item)) with
  | some item =>
    let inspected := List.find?_some first
    .inl ⟨item, List.mem_of_find?_eq_some first, of_decide_eq_true inspected⟩
  | none =>
    .inr ⟨⟨word, fun item listed => by
      have rejected := List.find?_eq_none.mp first item listed
      by_contra failed
      simp only [decide_eq_true failed] at rejected
      exact rejected trivial⟩, rfl⟩

namespace MeteredWork

variable {law : RawLaw Party Good Port Technology Instrument}
  {before : RawCurrent Party Good Technology Instrument} {bearer : Party} (work : MeteredWork law before bearer)

def bundle : Bundle Good :=
  (law.rawItems before work.word).flatMap fun item =>
    (law.actualDebit item.before item.request).map fun lot => (lot.1.2, lot.2)

omit [DecidableEq Port] in
theorem nonnegative : NonnegativeBundle Good work.bundle := by
  intro lot listed
  obtain ⟨item, actual, fromDebit⟩ := List.mem_flatMap.mp listed
  obtain ⟨original, debit, rfl⟩ := List.mem_map.mp fromDebit
  have valid := (work.admitted item actual).1
  have paid := valid.2.2.2.1
  rw [RawLaw.actualDebit, if_pos valid] at debit
  exact paid original debit

omit [DecidableEq Port] [DecidableEq Instrument] in
private theorem ownerAmount (flow : Flow Party Good) (good : Good)
    (own : ∀ lot ∈ flow, lot.1.1 = bearer) :
    amount Good (flow.map fun lot => (lot.1.2, lot.2)) good = flowAt flow bearer good := by
  induction flow with
  | nil => rfl
  | cons head tail earlier =>
    have headOwn : head.1.1 = bearer := own head List.mem_cons_self
    have tailOwn : ∀ lot ∈ tail, lot.1.1 = bearer := fun lot mem => own lot (List.mem_cons_of_mem _ mem)
    change (if head.1.2 = good then head.2 else 0) + amount Good (tail.map fun lot => (lot.1.2, lot.2)) good =
      (if head.1 = (bearer, good) then head.2 else 0) + flowAt tail bearer good
    rw [earlier tailOwn]
    simp [Prod.ext_iff, headOwn]

omit [DecidableEq Port] in
theorem actual_address (good : Good) :
    amount Good work.bundle good = law.totalDebit (law.rawItems before work.word) bearer good := by
  let debit := fun (item : Item) => (law.actualDebit item.before item.request).map fun lot => (lot.1.2, lot.2)
  have scan (items : List Item) :
      amount Good (items.flatMap debit) good = (items.map fun item => amount Good (debit item) good).sum := by
    induction items with
    | nil => rfl
    | cons item tail previous =>
      change amount Good (debit item ++ tail.flatMap debit) good =
        amount Good (debit item) good + (tail.map fun item => amount Good (debit item) good).sum
      rw [← previous]
      simp [amount, List.map_append, List.sum_append]
  change amount Good ((law.rawItems before work.word).flatMap debit) good = _
  rw [scan]
  unfold RawLaw.totalDebit
  congr 1
  apply List.map_congr_left
  intro item listed
  exact ownerAmount _ _ (work.admitted item listed).2.1

end MeteredWork

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Pricing
