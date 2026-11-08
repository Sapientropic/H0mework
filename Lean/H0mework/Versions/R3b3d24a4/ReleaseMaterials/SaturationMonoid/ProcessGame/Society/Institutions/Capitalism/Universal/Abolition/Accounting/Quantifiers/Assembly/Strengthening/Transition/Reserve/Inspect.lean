import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Reserve.Deficit

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Reserve

variable {Row Address Item : Type*} [DecidableEq Address]

/-- The predecessor checks are retained in `later`, so an inspector reports
the first violated gate in the original order, including ties on the clock. -/
inductive Failure (rows : List Row) (address : Row → Address) (key : Address) :
    List (Step Row Address Item) → (Row → ℚ) → ℚ → ℚ → Type _
  | stock {steps remaining stock clock} (short : stock < 0) :
      Failure rows address key steps remaining stock clock
  | openingRow {steps remaining stock clock} (nonnegative : 0 ≤ stock)
      (gap : RowGap rows address key remaining stock) :
      Failure rows address key steps remaining stock clock
  | grossDebit {step tail remaining stock clock}
      (nonnegative : 0 ≤ stock) (opening : held rows address remaining key ≤ stock)
      (short : stock < step.debit key) :
      Failure rows address key (step :: tail) remaining stock clock
  | postDebitRow {step tail remaining stock clock}
      (nonnegative : 0 ≤ stock) (opening : held rows address remaining key ≤ stock)
      (debit : step.debit key ≤ stock)
      (gap : RowGap rows address key (step.after remaining) (stock - step.debit key)) :
      Failure rows address key (step :: tail) remaining stock clock
  | later {step tail remaining stock clock}
      (nonnegative : 0 ≤ stock)
      (opening : held rows address remaining key ≤ stock)
      (debit : step.debit key ≤ stock)
      (retention : step.debit key + held rows address (step.after remaining) key ≤ stock)
      (failure : Failure rows address key tail (step.after remaining)
        (step.balance key stock) step.clock) :
      Failure rows address key (step :: tail) remaining stock clock

inductive Gate where
  | stock
  | openingRow
  | grossDebit
  | postDebitRow
  deriving Repr, DecidableEq

structure Location (Row Address Item : Type*) where
  position : ℕ
  clock : ℚ
  key : Address
  gate : Gate
  item : Option Item
  row : Option Row
  missing : ℚ
  positive : 0 < missing

namespace Failure

variable {rows : List Row} {address : Row → Address} {key : Address}
variable {steps : List (Step Row Address Item)} {remaining : Row → ℚ}
variable {stock clock : ℚ}

def location {steps : List (Step Row Address Item)} {remaining : Row → ℚ} {stock clock : ℚ}
    (failure : Failure rows address key steps remaining stock clock) :
    Location Row Address Item :=
  match failure with
  | .stock short =>
      ⟨0, clock, key, .stock, none, none, -stock, neg_pos.mpr short⟩
  | .openingRow _ gap =>
      ⟨0, clock, key, .openingRow, none, some gap.row, gap.quantity, gap.quantity_positive⟩
  | .grossDebit (step := step) _ _ short =>
      ⟨0, step.clock, key, .grossDebit, some step.item, none, step.debit key - stock,
        sub_pos.mpr short⟩
  | .postDebitRow (step := step) _ _ _ gap =>
      ⟨0, step.clock, key, .postDebitRow, some step.item, some gap.row, gap.quantity,
        gap.quantity_positive⟩
  | .later _ _ _ _ failure =>
      let result := failure.location
      { result with position := result.position + 1 }

/-- The reported original gate refutes protection on this path. -/
theorem refutes (failure : Failure rows address key steps remaining stock clock) :
    ¬ Protects rows address key steps remaining stock := by
  induction failure with
  | stock short =>
      rename_i steps remaining stock clock
      cases steps with
      | nil => exact fun fits => not_le_of_gt short fits.1
      | cons step tail => exact fun fits => not_le_of_gt short fits.1
  | openingRow nonnegative gap =>
      rename_i steps remaining stock clock
      cases steps with
      | nil => exact fun fits => not_le_of_gt gap.totalShort fits.2
      | cons step tail => exact fun fits => not_le_of_gt gap.totalShort fits.2.1
  | grossDebit _ _ short => exact fun fits => not_le_of_gt short fits.2.2.1
  | postDebitRow _ _ _ gap =>
      exact fun fits => not_le_of_gt gap.totalShort (by linarith only [fits.2.2.2.1])
  | later _ _ _ _ _ ih =>
      exact fun fits => ih fits.2.2.2.2

theorem requires_positive_topup (failure : Failure rows address key steps remaining stock clock) :
    0 < topup rows address key steps remaining stock := by
  have below : stock < openingNeed rows address key steps remaining :=
    lt_of_not_ge fun fits => failure.refutes
      ((openingNeed_fits_iff rows address key steps remaining stock).mp fits)
  exact (sub_pos.mpr below).trans_le (le_max_right _ _)

end Failure

inductive Decision (rows : List Row) (address : Row → Address) (key : Address)
    (steps : List (Step Row Address Item)) (remaining : Row → ℚ) (stock clock : ℚ) where
  | safe (protects : Protects rows address key steps remaining stock)
  | short (failure : Failure rows address key steps remaining stock clock)

private def inspectWithRetained (rows : List Row) (address : Row → Address) (key : Address) :
    (steps : List (Step Row Address Item)) → (remaining : Row → ℚ) → (stock clock retained : ℚ) →
      retained = held rows address remaining key → Decision rows address key steps remaining stock clock
  | [], remaining, stock, clock, retained, exactHeld => by
      by_cases nonnegative : 0 ≤ stock
      · by_cases opening : retained ≤ stock
        · exact .safe ⟨nonnegative, exactHeld ▸ opening⟩
        · exact .short (.openingRow nonnegative (selectRowGap address key remaining rows stock
            nonnegative (exactHeld ▸ lt_of_not_ge opening)))
      · exact .short (.stock (lt_of_not_ge nonnegative))
  | step :: tail, remaining, stock, clock, retained, exactHeld => by
      by_cases nonnegative : 0 ≤ stock
      · by_cases opening : retained ≤ stock
        · have openingExact : held rows address remaining key ≤ stock := exactHeld ▸ opening
          by_cases debit : step.debit key ≤ stock
          · let after := retained - held rows address step.paid key
            have afterExact : after = held rows address (step.after remaining) key := by
              simp only [after, exactHeld, held_after_one_original_debit]
            by_cases retention : step.debit key + after ≤ stock
            · have retentionExact : step.debit key + held rows address (step.after remaining) key ≤ stock :=
                afterExact ▸ retention
              exact match inspectWithRetained rows address key tail (step.after remaining)
                    (step.balance key stock) step.clock after afterExact with
                | .safe fits => .safe ⟨nonnegative, openingExact, debit, retentionExact, fits⟩
                | .short failure => .short (.later nonnegative openingExact debit retentionExact failure)
            · have shortage : stock < step.debit key + held rows address (step.after remaining) key :=
                afterExact ▸ lt_of_not_ge retention
              exact .short (.postDebitRow nonnegative openingExact debit
                (selectRowGap address key (step.after remaining) rows (stock - step.debit key)
                  (sub_nonneg.mpr debit) (by linarith only [shortage])))
          · exact .short (.grossDebit nonnegative openingExact (lt_of_not_ge debit))
        · exact .short (.openingRow nonnegative (selectRowGap address key remaining rows stock
            nonnegative (exactHeld ▸ lt_of_not_ge opening)))
      · exact .short (.stock (lt_of_not_ge nonnegative))

/-- The normal path carries one retained total per address. The row scan
runs at a failed gate to identify the original row and its exact quantity. -/
def inspect (rows : List Row) (address : Row → Address) (key : Address)
    (steps : List (Step Row Address Item)) (remaining : Row → ℚ) (stock clock : ℚ) :
    Decision rows address key steps remaining stock clock :=
  inspectWithRetained rows address key steps remaining stock clock (held rows address remaining key) rfl

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Reserve
