import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.Conservation
import Mathlib.Algebra.BigOperators.Group.List.Basic

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Continuation.Balance

open Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)
  (current : RawCurrent Party Good Technology Instrument)
  (word : RawEvent Party Good Port Technology Instrument)

/-- This is the finite support of actual effects, not a second inventory of
claims or receipts. Repeated occurrences keep their original contributions. -/
def cells : List (Party × Good) :=
  (law.rawItems current word).flatMap fun item =>
    (law.actualDebit item.before item.request).map Prod.fst ++
      (law.actualCredit item.before item.request).map Prod.fst

def gain (person : Party) (good : Good) : ℚ :=
  law.totalCredit (law.rawItems current word) person good -
    law.totalDebit (law.rawItems current word) person good

def Regenerative : Prop :=
  ∀ cell ∈ cells law current word,
    law.totalDebit (law.rawItems current word) cell.1 cell.2 ≤
      law.totalCredit (law.rawItems current word) cell.1 cell.2

def Balanced : Prop :=
  ∀ cell ∈ cells law current word,
    law.totalDebit (law.rawItems current word) cell.1 cell.2 =
      law.totalCredit (law.rawItems current word) cell.1 cell.2

instance : Decidable (Regenerative law current word) := by unfold Regenerative; infer_instance
instance : Decidable (Balanced law current word) := by unfold Balanced; infer_instance

theorem no_effect_outside_original_support (person : Party) (good : Good)
    (absent : (person, good) ∉ cells law current word) :
    law.totalDebit (law.rawItems current word) person good = 0 ∧
      law.totalCredit (law.rawItems current word) person good = 0 := by
  constructor
  · unfold RawLaw.totalDebit
    apply List.sum_eq_zero
    intro quantity member
    obtain ⟨item, original, rfl⟩ := List.mem_map.mp member
    apply amount_zero_of_absent
    intro lot inside same
    apply absent
    exact List.mem_flatMap.mpr ⟨item, original,
      List.mem_append_left _ (List.mem_map.mpr ⟨lot, inside, same⟩)⟩
  · unfold RawLaw.totalCredit
    apply List.sum_eq_zero
    intro quantity member
    obtain ⟨item, original, rfl⟩ := List.mem_map.mp member
    apply amount_zero_of_absent
    intro lot inside same
    apply absent
    exact List.mem_flatMap.mpr ⟨item, original,
      List.mem_append_right _ (List.mem_map.mpr ⟨lot, inside, same⟩)⟩

theorem regenerative_gain_nonnegative (checked : Regenerative law current word)
    (person : Party) (good : Good) : 0 ≤ gain law current word person good := by
  by_cases present : (person, good) ∈ cells law current word
  · unfold gain
    exact sub_nonneg.mpr (checked (person, good) present)
  · obtain ⟨debit, credit⟩ := no_effect_outside_original_support law current word person good present
    simp only [gain, credit, debit, sub_self, le_refl]

theorem balanced_gain_zero (checked : Balanced law current word)
    (person : Party) (good : Good) : gain law current word person good = 0 := by
  by_cases present : (person, good) ∈ cells law current word
  · unfold gain
    exact sub_eq_zero.mpr (checked (person, good) present).symm
  · obtain ⟨debit, credit⟩ := no_effect_outside_original_support law current word person good present
    simp only [gain, credit, debit, sub_self]

theorem exact_stock_after_original_effects (person : Party) (good : Good) :
    ((law.execute current 0 word).final).stock person good =
      current.stock person good + gain law current word person good := by
  have conserved := law.execute_material_balance current 0 word person good
  change (law.execute current 0 word).final.stock person good +
    law.totalDebit (law.rawItems current word) person good =
      current.stock person good + law.totalCredit (law.rawItems current word) person good at conserved
  unfold gain
  linarith

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Continuation.Balance
