import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Repayment.Local
import Mathlib.Algebra.Order.Field.Rat

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Redemption

open Source.Program PublicFunction.Repayment

section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Good]

variable (law : RawLaw Party Good Port Technology Instrument)
  (origin current : RawCurrent Party Good Technology Instrument)
  (position : Position Party Instrument)

abbrev unit := law.settlementUnit position.instrument
abbrev rate := law.settlementRate position.instrument

/-- Life and maintenance debit the same stock, so their requirements add
at this address. No monetary valuation of other goods enters this leg. -/
def essentials (bearer : Party) (good : Good) : ℚ :=
  max 0 (amount Good (law.necessities origin bearer) good +
    amount Good (law.mandatoryMaintenance origin bearer) good)

def creditorStock : ℚ := current.stock position.creditor (unit law position)
def debtorStock : ℚ := current.stock position.debtor (unit law position)

def lower : ℚ :=
  max 0 (essentials law origin position.creditor (unit law position) - creditorStock law current position) /
    rate law position

def upper : ℚ :=
  min (balance position current)
    ((debtorStock law current position - essentials law origin position.debtor (unit law position)) /
      rate law position)

theorem minimum_is_the_actual_material_shortfall (positive : 0 < rate law position) :
    lower law origin current position * rate law position =
      max 0 (essentials law origin position.creditor (unit law position) - creditorStock law current position) :=
  div_mul_cancel₀ _ (ne_of_gt positive)

def Within (quantity : ℚ) : Prop :=
  lower law origin current position ≤ quantity ∧ quantity ≤ upper law origin current position

def MateriallySafe (quantity : ℚ) : Prop :=
  0 ≤ quantity ∧ quantity ≤ balance position current ∧
  essentials law origin position.creditor (unit law position) ≤
    creditorStock law current position + quantity * rate law position ∧
  essentials law origin position.debtor (unit law position) ≤
    debtorStock law current position - quantity * rate law position

theorem safe_iff_within (quantity : ℚ) (positive : 0 < rate law position) :
    MateriallySafe law origin current position quantity ↔ Within law origin current position quantity := by
  unfold MateriallySafe Within lower upper
  rw [div_le_iff₀ positive, max_le_iff, le_min_iff, le_div_iff₀ positive]
  constructor
  · rintro ⟨nonneg, principal, receiver, payer⟩
    exact ⟨⟨mul_nonneg nonneg positive.le, by linarith⟩, principal, by linarith⟩
  · rintro ⟨⟨nonneg, receiver⟩, principal, payer⟩
    exact ⟨nonneg_of_mul_nonneg_left nonneg positive, principal, by linarith, by linarith⟩

theorem lower_is_the_attained_material_minimum (positive : 0 < rate law position)
    (capacity : lower law origin current position ≤ upper law origin current position) :
    MateriallySafe law origin current position (lower law origin current position) ∧
      ∀ quantity, MateriallySafe law origin current position quantity → lower law origin current position ≤ quantity :=
  ⟨(safe_iff_within law origin current position _ positive).mpr ⟨le_rfl, capacity⟩,
    fun quantity safe => ((safe_iff_within law origin current position quantity positive).mp safe).1⟩

theorem upper_is_the_attained_material_maximum (positive : 0 < rate law position)
    (capacity : lower law origin current position ≤ upper law origin current position) :
    MateriallySafe law origin current position (upper law origin current position) ∧
      ∀ quantity, MateriallySafe law origin current position quantity → quantity ≤ upper law origin current position :=
  ⟨(safe_iff_within law origin current position _ positive).mpr ⟨capacity, le_rfl⟩,
    fun quantity safe => ((safe_iff_within law origin current position quantity positive).mp safe).2⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Redemption
