import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Step

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

def nativeTransition (current : Current input depth count anchor) :
    (Epoch.Finance.process input depth count).Run current.account.current
      (next input depth count prefixLimit renewalLimit oldPast start current).account.current := by
  by_cases paid : current.bodyPaid = true
  · simp only [next, dif_pos paid]
    cases found : item? input depth count prefixLimit renewalLimit oldPast start current with
    | none => exact .nil
    | some item =>
        dsimp only
        cases issued : Epoch.Finance.readNewClaim input depth count item with
        | some claim => exact .nil
        | none =>
            rw [(Current.after_item_reads_the_source_generated_native_account current paid item).1]
            exact (Epoch.Finance.consume input depth count item current.account).transition input depth count
  · have same := the_unexecuted_body_is_the_original_initial_state current paid
    subst current
    exact .nil

theorem every_actual_step_keeps_the_original_claim_order
    (current : Current input depth count anchor) :
    current.account.current.slots.map (Epoch.Finance.slotClaim input depth count) <+:
      (next input depth count prefixLimit renewalLimit oldPast start current).account.current.slots.map
        (Epoch.Finance.slotClaim input depth count) :=
  Epoch.Finance.run_retains_all_claims input depth count
    (nativeTransition input depth count prefixLimit renewalLimit oldPast start current)

theorem every_actual_step_keeps_the_complete_original_history
    (current : Current input depth count anchor) :
    current.account.current.history <+:
      (next input depth count prefixLimit renewalLimit oldPast start current).account.current.history := by
  rw [(nativeTransition input depth count prefixLimit renewalLimit oldPast start current).history_eq]
  exact List.prefix_append _ _

#print axioms nativeTransition
#print axioms every_actual_step_keeps_the_original_claim_order
#print axioms every_actual_step_keeps_the_complete_original_history

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting
