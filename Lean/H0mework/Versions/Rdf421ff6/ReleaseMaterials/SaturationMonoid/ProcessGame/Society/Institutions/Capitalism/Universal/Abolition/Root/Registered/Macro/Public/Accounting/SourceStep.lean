import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Head

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (oldPast : List (Compile.RawInput Party Good Port Technology Instrument))
  (start : Physical.Cursor Party Good Port Technology Instrument)
  {anchor : (Epoch.Finance.process input depth count).GeneratedState}

/-- This is the old-world restriction of the actual write, including a
new issue. The Engine must consume that occurrence through debt admission;
the ordinary hold strategy is not its authoritative successor. -/
def nativeNext (current : Current input depth count anchor) : Current input depth count anchor :=
  if paid : current.bodyPaid = true then
    match item? input depth count prefixLimit renewalLimit oldPast start current with
    | none => current
    | some item => current.afterItem paid item
  else bodyTarget input depth count anchor

def nativeTransitionAt (current : Current input depth count anchor) :
    (Epoch.Finance.process input depth count).Run current.account.current
      (nativeNext input depth count prefixLimit renewalLimit oldPast start current).account.current := by
  by_cases paid : current.bodyPaid = true
  · rw [nativeNext, dif_pos paid]
    cases found : item? input depth count prefixLimit renewalLimit oldPast start current with
    | none => exact .nil
    | some item =>
        rw [(Current.after_item_reads_the_source_generated_native_account current paid item).1]
        exact (Epoch.Finance.consume input depth count item current.account).transition input depth count
  · have same := the_unexecuted_body_is_the_original_initial_state current paid
    subst current
    exact .nil

theorem every_actual_head_has_its_literal_source_account
    (current : Current input depth count anchor) (paid : current.bodyPaid = true)
    (item : Epoch.Finance.ActualItem input depth count)
    (present : item? input depth count prefixLimit renewalLimit oldPast start current = some item) :
    (nativeNext input depth count prefixLimit renewalLimit oldPast start current).account =
      (Epoch.Finance.consume input depth count item current.account).next input depth count := by
  rw [nativeNext, dif_pos paid, present]
  exact (Current.after_item_reads_the_source_generated_native_account current paid item).1

theorem the_macro_hold_does_not_erase_a_new_issue_write
    {current : Current input depth count anchor}
    (registered : Registration input depth count prefixLimit renewalLimit oldPast start current) :
    (nativeNext input depth count prefixLimit renewalLimit oldPast start current).account = registered.admitted := by
  rw [every_actual_head_has_its_literal_source_account input depth count prefixLimit renewalLimit oldPast start
    current registered.paid registered.item registered.present]
  have original := Epoch.Finance.readNewClaim_origin input depth count registered.item registered.claim registered.issued
  have accepted := registered.claim.accepted
  rw [original] at accepted
  unfold Epoch.Finance.consume
  rw [dif_neg (not_not_intro accepted)]
  split
  · rename_i actual found
    cases Option.some.inj (found.symm.trans registered.issued)
    rfl
  · rename_i absent
    cases absent.symm.trans registered.issued

#print axioms nativeNext
#print axioms nativeTransitionAt
#print axioms the_macro_hold_does_not_erase_a_new_issue_write

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting
