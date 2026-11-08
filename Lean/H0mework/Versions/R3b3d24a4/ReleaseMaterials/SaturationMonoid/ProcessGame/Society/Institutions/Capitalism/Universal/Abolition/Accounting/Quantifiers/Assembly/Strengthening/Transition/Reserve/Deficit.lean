import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Reserve.Opening

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Reserve

variable {Row Address : Type*} [DecidableEq Address]

/-- A shortage names the first original row that does not fit in the
roster order at the failing address. The quantity is the shortage at that row. -/
structure RowGap (rows : List Row) (address : Row → Address) (key : Address)
    (remaining : Row → ℚ) (available : ℚ) where
  before : List Row
  row : Row
  after : List Row
  original : rows = before ++ row :: after
  sameAddress : address row = key
  earlier : ∀ index ≤ before.length, held (before.take index) address remaining key ≤ available
  short : available < held before address remaining key + remaining row
  totalShort : available < held rows address remaining key

namespace RowGap

variable {rows : List Row} {address : Row → Address} {key : Address}
variable {remaining : Row → ℚ} {available : ℚ}

def quantity (gap : RowGap rows address key remaining available) : ℚ :=
  held gap.before address remaining key + remaining gap.row - available

theorem quantity_positive (gap : RowGap rows address key remaining available) :
    0 < gap.quantity :=
  sub_pos.mpr gap.short

theorem row_is_original (gap : RowGap rows address key remaining available) :
    gap.row ∈ rows := by
  exact (congrArg (fun roster => gap.row ∈ roster) gap.original).mpr
    (List.mem_append_right _ (List.mem_cons_self ..))

end RowGap

/-- Scan the authoritative ordered roster. The aggregate shortage only
enters this function together with a proof that an original row fails. -/
def selectRowGap (address : Row → Address) (key : Address) (remaining : Row → ℚ) :
    (rows : List Row) → (available : ℚ) →
      0 ≤ available → available < held rows address remaining key →
        RowGap rows address key remaining available
  | [], available, nonnegative, short =>
      False.elim (not_lt_of_ge nonnegative (by simpa [held] using short))
  | first :: rest, available, nonnegative, short => by
      let amount := atAddress address remaining key first
      by_cases fits : amount ≤ available
      · have restShort : available - amount < held rest address remaining key := by
          have total : held (first :: rest) address remaining key =
              amount + held rest address remaining key := rfl
          rw [total] at short
          linarith only [short]
        let found := selectRowGap address key remaining rest (available - amount)
          (sub_nonneg.mpr fits) restShort
        exact {
          before := first :: found.before
          row := found.row
          after := found.after
          original := congrArg (List.cons first) found.original
          sameAddress := found.sameAddress
          earlier := by
            intro index bounded
            cases index with
            | zero => simpa [held] using nonnegative
            | succ index =>
                have h := found.earlier index (Nat.succ_le_succ_iff.mp bounded)
                change amount + held (found.before.take index) address remaining key ≤ available
                linarith only [h]
          short := by
            have h := found.short
            change available < amount + held found.before address remaining key +
              remaining found.row
            linarith only [h]
          totalShort := short
        }
      · have same : address first = key := by
          by_contra different
          exact fits (by simpa [amount, atAddress, different] using nonnegative)
        exact {
          before := []
          row := first
          after := rest
          original := rfl
          sameAddress := same
          earlier := by
            intro index _
            simpa [held] using nonnegative
          short := by simpa [held, amount, atAddress, same] using lt_of_not_ge fits
          totalShort := short
        }

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Reserve
