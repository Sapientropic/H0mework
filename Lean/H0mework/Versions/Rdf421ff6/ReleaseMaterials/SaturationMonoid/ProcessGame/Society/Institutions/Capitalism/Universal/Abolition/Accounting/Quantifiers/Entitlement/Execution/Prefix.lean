import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Entitlement.Duty.State

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Entitlement.Execution

open Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)

/-- Source syntax is checked at each actual intermediate stock. The first
failed request remains in the suffix instead of cancelling prior payments. -/
def payable (before : RawCurrent Party Good Technology Instrument) :
    RawEvent Party Good Port Technology Instrument → RawEvent Party Good Port Technology Instrument
  | [] => []
  | request :: rest => if law.Valid before request then request :: payable (law.step before request) rest else []

def ValidAt (before : RawCurrent Party Good Technology Instrument) : RawEvent Party Good Port Technology Instrument → Prop
  | [] => True
  | request :: rest => law.Valid before request ∧ ValidAt (law.step before request) rest

theorem the_source_prefix_is_valid (before : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) : ValidAt law before (payable law before word) := by
  induction word generalizing before with
  | nil => trivial
  | cons request rest inherited =>
      unfold payable
      split
      · rename_i accepted
        exact ⟨accepted,inherited (law.step before request)⟩
      · trivial

theorem validity_reaches_every_original_inventory_item
    (before : RawCurrent Party Good Technology Instrument) (word : RawEvent Party Good Port Technology Instrument)
    (checked : ValidAt law before word) (index : Nat) :
    ∀ item ∈ (law.execute before index word).items, law.Valid item.before item.request := by
  induction word generalizing before index with
  | nil => intro item listed; cases listed
  | cons request rest inherited =>
      intro item listed
      simp only [RawLaw.execute,List.mem_cons] at listed
      rcases listed with same | later
      · subst item; exact checked.1
      · exact inherited (law.step before request) checked.2 (index + 1) item later

theorem the_source_prefix_is_an_original_prefix (before : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) : payable law before word <+: word := by
  induction word generalizing before with
  | nil => exact List.prefix_refl _
  | cons request rest inherited =>
      unfold payable
      split
      · obtain ⟨suffix,same⟩ := inherited (law.step before request)
        exact ⟨suffix,congrArg (List.cons request) same⟩
      · exact List.nil_prefix

theorem a_fully_funded_original_word_is_selected_whole
    (before : RawCurrent Party Good Technology Instrument) (word : RawEvent Party Good Port Technology Instrument)
    (checked : ValidAt law before word) : payable law before word = word := by
  induction word generalizing before with
  | nil => rfl
  | cons request rest inherited =>
      rw [payable,if_pos checked.1,inherited _ checked.2]

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Entitlement.Execution
