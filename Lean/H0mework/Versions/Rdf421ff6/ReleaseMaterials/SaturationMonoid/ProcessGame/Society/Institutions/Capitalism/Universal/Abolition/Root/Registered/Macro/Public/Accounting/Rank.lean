import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Head

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (oldPast : List (Compile.RawInput Party Good Port Technology Instrument))
  (start : Physical.Cursor Party Good Port Technology Instrument)
  {anchor : (Epoch.Finance.process input depth count).GeneratedState}

/-- One body and this occurrence's actual unconsumed positions. No future
success table, new reserve, or external countdown supplies the bound. -/
def mass (current : Current input depth count anchor) : Nat :=
  if current.bodyPaid then (items input depth count prefixLimit renewalLimit oldPast start).length - current.position
  else (items input depth count prefixLimit renewalLimit oldPast start).length + 1

theorem an_actual_head_is_inside_the_original_inventory
    (current : Current input depth count anchor) (paid : current.bodyPaid = true)
    (item : Epoch.Finance.ActualItem input depth count)
    (present : item? input depth count prefixLimit renewalLimit oldPast start current = some item) :
    current.position < (items input depth count prefixLimit renewalLimit oldPast start).length := by
  simp only [item?, paid, if_true] at present
  exact (List.getElem?_eq_some_iff.mp present).choose

theorem the_first_body_spends_exactly_its_own_source_step :
    mass input depth count prefixLimit renewalLimit oldPast start
        (next input depth count prefixLimit renewalLimit oldPast start (initial input depth count anchor)) + 1 =
      mass input depth count prefixLimit renewalLimit oldPast start (initial input depth count anchor) := by
  rfl

theorem every_ordinary_financial_head_spends_one_actual_position
    (current : Current input depth count anchor) (paid : current.bodyPaid = true)
    (item : Epoch.Finance.ActualItem input depth count)
    (present : item? input depth count prefixLimit renewalLimit oldPast start current = some item)
    (noNewClaim : Epoch.Finance.readNewClaim input depth count item = none) :
    mass input depth count prefixLimit renewalLimit oldPast start
        (next input depth count prefixLimit renewalLimit oldPast start current) + 1 =
      mass input depth count prefixLimit renewalLimit oldPast start current := by
  have inside := an_actual_head_is_inside_the_original_inventory input depth count prefixLimit renewalLimit oldPast start
    current paid item present
  have after := Current.after_item_reads_the_source_generated_native_account current paid item
  rw [next, dif_pos paid, present]
  dsimp only
  rw [noNewClaim]
  simp only [mass, after.2.1, after.2.2, paid, if_true]
  omega

theorem the_original_admission_spends_exactly_its_actual_head
    {current : Current input depth count anchor}
    (registered : Registration input depth count prefixLimit renewalLimit oldPast start current) :
    mass input depth count prefixLimit renewalLimit oldPast start registered.next + 1 =
      mass input depth count prefixLimit renewalLimit oldPast start current := by
  have inside := an_actual_head_is_inside_the_original_inventory input depth count prefixLimit renewalLimit oldPast start
    current registered.paid registered.item registered.present
  have after := registered.the_born_current_consumes_exactly_the_registered_head
  simp only [mass, after.2.1, after.2.2, registered.paid, if_true]
  omega

theorem zero_source_mass_has_no_unpaid_internal_work
    (current : Current input depth count anchor)
    (zero : mass input depth count prefixLimit renewalLimit oldPast start current = 0) :
    current.bodyPaid = true ∧ item? input depth count prefixLimit renewalLimit oldPast start current = none := by
  by_cases paid : current.bodyPaid = true
  · refine ⟨paid, ?_⟩
    have consumed : (items input depth count prefixLimit renewalLimit oldPast start).length ≤ current.position := by
      simp only [mass, paid, if_true] at zero
      omega
    simp only [item?, paid, if_true]
    exact List.getElem?_eq_none consumed
  · have unpaid : current.bodyPaid = false := by
      cases flag : current.bodyPaid <;> simp_all
    simp [mass, unpaid] at zero

#print axioms mass
#print axioms every_ordinary_financial_head_spends_one_actual_position
#print axioms the_original_admission_spends_exactly_its_actual_head
#print axioms zero_source_mass_has_no_unpaid_internal_work

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting
