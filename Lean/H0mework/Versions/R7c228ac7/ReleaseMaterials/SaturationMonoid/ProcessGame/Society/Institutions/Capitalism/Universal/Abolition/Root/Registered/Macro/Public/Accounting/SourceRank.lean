import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Rank
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.SourceStep

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (oldPast : List (Compile.RawInput Party Good Port Technology Instrument))
  (start : Physical.Cursor Party Good Port Technology Instrument)
  {anchor : (Epoch.Finance.process input depth count).GeneratedState}

theorem the_source_body_spends_its_actual_step :
    mass input depth count prefixLimit renewalLimit oldPast start
        (nativeNext input depth count prefixLimit renewalLimit oldPast start (initial input depth count anchor)) + 1 =
      mass input depth count prefixLimit renewalLimit oldPast start (initial input depth count anchor) := rfl

/-- The actual source consumes every financial position. At issuance the
root must additionally admit its born row; the source projection cannot
replace that joint write by the ordinary hold strategy. -/
theorem every_native_financial_head_spends_its_actual_position
    (current : Current input depth count anchor) (paid : current.bodyPaid = true)
    (item : Epoch.Finance.ActualItem input depth count)
    (present : item? input depth count prefixLimit renewalLimit oldPast start current = some item) :
    mass input depth count prefixLimit renewalLimit oldPast start
        (nativeNext input depth count prefixLimit renewalLimit oldPast start current) + 1 =
      mass input depth count prefixLimit renewalLimit oldPast start current := by
  have inside := an_actual_head_is_inside_the_original_inventory input depth count prefixLimit renewalLimit oldPast start
    current paid item present
  have after := Current.after_item_reads_the_source_generated_native_account current paid item
  rw [nativeNext, dif_pos paid, present]
  simp only [mass, after.2.1, after.2.2, paid, if_true]
  omega

theorem every_positive_source_mass_is_strictly_consumed
    (current : Current input depth count anchor)
    (positive : 0 < mass input depth count prefixLimit renewalLimit oldPast start current) :
    mass input depth count prefixLimit renewalLimit oldPast start
      (nativeNext input depth count prefixLimit renewalLimit oldPast start current) <
        mass input depth count prefixLimit renewalLimit oldPast start current := by
  by_cases paid : current.bodyPaid = true
  · cases present : item? input depth count prefixLimit renewalLimit oldPast start current with
    | some item =>
        have spent := every_native_financial_head_spends_its_actual_position input depth count
          prefixLimit renewalLimit oldPast start current paid item present
        omega
    | none =>
        have exhausted : (items input depth count prefixLimit renewalLimit oldPast start).length ≤ current.position := by
          simp only [item?, paid, if_true] at present
          exact List.getElem?_eq_none_iff.mp present
        simp only [mass, paid, if_true] at positive
        omega
  · rw [the_unexecuted_body_is_the_original_initial_state current paid]
    have spent := the_source_body_spends_its_actual_step input depth count prefixLimit renewalLimit
      oldPast start (anchor := anchor)
    omega

#print axioms every_native_financial_head_spends_its_actual_position
#print axioms every_positive_source_mass_is_strictly_consumed

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting
