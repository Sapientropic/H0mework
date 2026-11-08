import Mathlib.Tactic.Linarith
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Liquidity.Assignment

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Reserve

/-- One original ordered material item. Payments from every original row
share its single debit. A credit on this item comes after the debit gate. -/
structure Step (Row Address Item : Type*) where
  item : Item
  clock : ℚ
  debit : Address → ℚ
  credit : Address → ℚ
  paid : Row → ℚ

variable {Row Address Item : Type*} [DecidableEq Address]

def atAddress (address : Row → Address) (amount : Row → ℚ)
    (key : Address) (row : Row) : ℚ :=
  if address row = key then amount row else 0

def held (rows : List Row) (address : Row → Address)
    (remaining : Row → ℚ) (key : Address) : ℚ :=
  (rows.map (atAddress address remaining key)).sum

def initialRemaining (required priorPaid : Row → ℚ) : Row → ℚ :=
  fun row => required row - priorPaid row

def Step.after (step : Step Row Address Item) (remaining : Row → ℚ) : Row → ℚ :=
  fun row => remaining row - step.paid row

def Step.balance (step : Step Row Address Item) (key : Address) (stock : ℚ) : ℚ :=
  stock + step.credit key - step.debit key

/-- Each original ordered prefix protects the outstanding amount. The
current item's debit and the rows it leaves unpaid fit before its credit. -/
def Protects (rows : List Row) (address : Row → Address) (key : Address) :
    List (Step Row Address Item) → (Row → ℚ) → ℚ → Prop
  | [], remaining, stock => 0 ≤ stock ∧ held rows address remaining key ≤ stock
  | step :: tail, remaining, stock =>
      0 ≤ stock ∧ held rows address remaining key ≤ stock ∧
      step.debit key ≤ stock ∧
      step.debit key + held rows address (step.after remaining) key ≤ stock ∧
      Protects rows address key tail (step.after remaining) (step.balance key stock)

theorem held_after_one_original_debit
    (rows : List Row) (address : Row → Address) (key : Address)
    (step : Step Row Address Item) (remaining : Row → ℚ) :
    held rows address (step.after remaining) key =
      held rows address remaining key - held rows address step.paid key := by
  induction rows with
  | nil => simp [held]
  | cons row rows ih =>
      simp only [held, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]
      by_cases same : address row = key <;> (simp only [atAddress, same, if_true, if_false, Step.after]; ring)

private def scanOpening (rows : List Row) (address : Row → Address) (key : Address) :
    List (Step Row Address Item) → ℚ → ℚ
  | [], retained => max 0 retained
  | step :: tail, retained =>
      let after := retained - held rows address step.paid key
      max (max 0 retained)
        (max (max (step.debit key) (step.debit key + after))
          (scanOpening rows address key tail after + step.debit key - step.credit key))

/-- Exact opening stock for this fixed original ordered word and address.
Each item subtracts its assigned shares from the running retained total. -/
def openingNeed (rows : List Row) (address : Row → Address) (key : Address)
    (steps : List (Step Row Address Item)) (remaining : Row → ℚ) : ℚ :=
  scanOpening rows address key steps (held rows address remaining key)

private theorem openingNeed_cons (rows : List Row) (address : Row → Address)
    (key : Address) (step : Step Row Address Item) (tail : List (Step Row Address Item))
    (remaining : Row → ℚ) :
    openingNeed rows address key (step :: tail) remaining =
      max (max 0 (held rows address remaining key))
        (max (max (step.debit key) (step.debit key + held rows address (step.after remaining) key))
          (openingNeed rows address key tail (step.after remaining) +
            step.debit key - step.credit key)) := by
  simp only [openingNeed, scanOpening, held_after_one_original_debit]

theorem openingNeed_fits_iff (rows : List Row) (address : Row → Address)
    (key : Address) (steps : List (Step Row Address Item))
    (remaining : Row → ℚ) (stock : ℚ) :
    openingNeed rows address key steps remaining ≤ stock ↔
      Protects rows address key steps remaining stock := by
  induction steps generalizing remaining stock with
  | nil => simp only [openingNeed, scanOpening, Protects, max_le_iff]
  | cons step tail ih =>
      simp only [openingNeed_cons, Protects, max_le_iff, ← ih, Step.balance]
      constructor
      · rintro ⟨⟨stock_nonneg, outstanding⟩, ⟨⟨debit, protection⟩, suffix⟩⟩
        exact ⟨stock_nonneg, outstanding, debit, protection, by linarith⟩
      · rintro ⟨stock_nonneg, outstanding, debit, protection, suffix⟩
        exact ⟨⟨stock_nonneg, outstanding⟩, ⟨⟨debit, protection⟩, by linarith⟩⟩

theorem openingNeed_attains (rows : List Row) (address : Row → Address)
    (key : Address) (steps : List (Step Row Address Item)) (remaining : Row → ℚ) :
    Protects rows address key steps remaining (openingNeed rows address key steps remaining) :=
  (openingNeed_fits_iff rows address key steps remaining _).mp le_rfl

def topup (rows : List Row) (address : Row → Address) (key : Address)
    (steps : List (Step Row Address Item)) (remaining : Row → ℚ) (stock : ℚ) : ℚ :=
  max 0 (openingNeed rows address key steps remaining - stock)

theorem topup_fits_iff (rows : List Row) (address : Row → Address)
    (key : Address) (steps : List (Step Row Address Item)) (remaining : Row → ℚ)
    (stock addition : ℚ) :
    topup rows address key steps remaining stock ≤ addition ↔
      0 ≤ addition ∧ Protects rows address key steps remaining (stock + addition) := by
  rw [topup, max_le_iff, ← openingNeed_fits_iff]
  constructor
  · exact fun ⟨nonnegative, enough⟩ => ⟨nonnegative, by linarith⟩
  · exact fun ⟨nonnegative, enough⟩ => ⟨nonnegative, by linarith⟩

theorem debit_and_remaining_separate_one_shared_payment
    (rows : List Row) (address : Row → Address) (key : Address)
    (step : Step Row Address Item) (remaining : Row → ℚ) :
    step.debit key + held rows address (step.after remaining) key =
      held rows address remaining key + (step.debit key - held rows address step.paid key) := by
  rw [held_after_one_original_debit]
  ring

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Reserve
