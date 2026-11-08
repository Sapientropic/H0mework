import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.Stock
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Scan

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production

open Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good]

local notation "Current" => RawCurrent Party Good Technology Instrument
local notation "Word" => RawEvent Party Good Port Technology Instrument

def addresses (word : Word) : List (Party × Good) :=
  word.flatMap fun request => (material request).map Prod.fst

theorem required_is_zero_at_an_unmentioned_address (word : Word) (party : Party) (good : Good)
    (absent : (party, good) ∉ addresses word) : required word party good = 0 := by
  unfold required
  apply List.sum_eq_zero
  intro quantity listed
  obtain ⟨request, original, rfl⟩ := List.mem_map.mp listed
  apply amount_zero_of_absent
  intro entry used same
  exact absent (List.mem_flatMap.mpr ⟨request, original, List.mem_map.mpr ⟨entry, used, same⟩⟩)

def extraStock (current : Current) (word held : Word) (key : Party × Good) : ℚ :=
  max 0 (required word key.1 key.2 + required held key.1 key.2 - current.stock key.1 key.2)

theorem exact_additional_opening_stock (current : Current) (word held : Word)
    (key : Party × Good) (extra : ℚ) :
    extraStock current word held key ≤ extra ↔ 0 ≤ extra ∧
      required word key.1 key.2 + required held key.1 key.2 ≤ current.stock key.1 key.2 + extra := by
  rw [extraStock, max_le_iff, sub_le_iff_le_add, add_comm extra]

structure FundingShortage (current : Current) (word held : Word) where
  address : Party × Good
  original : address ∈ addresses word ++ addresses held
  short : current.stock address.1 address.2 <
    required word address.1 address.2 + required held address.1 address.2

theorem FundingShortage.missing_is_exactly_positive {current : Current} {word held : Word}
    (issue : FundingShortage current word held) :
    0 < extraStock current word held issue.address := by
  exact lt_max_of_lt_right (sub_pos.mpr issue.short)

inductive Funding (current : Current) (word held : Word)
  | funded (everyAddress : ∀ party good, required word party good + required held party good ≤
      current.stock party good)
  | short (issue : FundingShortage current word held)

structure AddressShortage (current : Current) (need : Party × Good → ℚ) (support : List (Party × Good)) where
  address : Party × Good
  original : address ∈ support
  short : current.stock address.1 address.2 < need address

inductive StockDecision (current : Current) (need : Party × Good → ℚ) (support : List (Party × Good))
  | funded (all : ∀ key, need key ≤ current.stock key.1 key.2)
  | short (issue : AddressShortage current need support)

def inspectStock (current : Current) (need : Party × Good → ℚ) (support : List (Party × Good))
    (zeroOutside : ∀ key ∉ support, need key = 0)
    (opening : ∀ party good, 0 ≤ current.stock party good) : StockDecision current need support :=
  match Abolition.Material.inspectList (fun key => need key ≤ current.stock key.1 key.2) support with
  | .failure key original fails => .short ⟨key, original, lt_of_not_ge fails⟩
  | .clear funded => .funded fun key => by
    by_cases present : key ∈ support
    · exact funded key present
    · rw [zeroOutside key present]
      exact opening key.1 key.2

/-- The support comes from the two literal source words. Unmentioned
addresses cannot account for a missing service payment. -/
def inspectFunding (current : Current) (word held : Word)
    (opening : ∀ party good, 0 ≤ current.stock party good) : Funding current word held := by
  let need (key : Party × Good) := required word key.1 key.2 + required held key.1 key.2
  have outside (key : Party × Good) (absent : key ∉ addresses word ++ addresses held) : need key = 0 := by
    unfold need
    rw [required_is_zero_at_an_unmentioned_address _ _ _ (fun member => absent (List.mem_append_left _ member)),
        required_is_zero_at_an_unmentioned_address _ _ _ (fun member => absent (List.mem_append_right _ member)), zero_add]
  match inspectStock current need (addresses word ++ addresses held) outside opening with
  | .short issue => exact .short ⟨issue.address, issue.original, issue.short⟩
  | .funded funds => exact .funded fun party good => funds (party, good)

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production
