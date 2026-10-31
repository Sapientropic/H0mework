import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.SourceStep

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld DebtActivationLedger
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit : Nat}
  {oldPast : List (Compile.RawInput Party Good Port Technology Instrument)}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  {world : WorldRelationNetwork} {anchor : (Epoch.Finance.process input depth count).GeneratedState}
  (prior : Epoch.Finance.Future.Continuation.AccountFamily input depth count world anchor)
  (current : Current input depth count anchor)
  (registered : Registration input depth count prefixLimit renewalLimit oldPast start current)

theorem the_same_actual_item_is_the_original_native_admission :
    (Epoch.Finance.consume input depth count registered.item current.account).next input depth count = registered.admitted := by
  have origin := registered.the_new_row_has_the_same_actual_source
  have accepted := registered.claim.accepted
  rw [origin] at accepted
  unfold Epoch.Finance.consume
  rw [dif_neg (not_not_intro accepted)]
  split
  · rename_i actual same
    cases Option.some.inj (same.symm.trans registered.issued)
    rfl
  · rename_i absent
    cases absent.symm.trans registered.issued

theorem admittedNative : Nonempty ((Epoch.Finance.process input depth count).Run anchor.current registered.admitted.current) :=
  current.native.map fun earlier => earlier.concatRuns (Epoch.Finance.process input depth count) registered.nativeAdmission

private theorem support_congr
    (left right : (Epoch.Finance.process input depth count).GeneratedState)
    (leftRun : Nonempty ((Epoch.Finance.process input depth count).Run anchor.current left.current))
    (rightRun : Nonempty ((Epoch.Finance.process input depth count).Run anchor.current right.current))
    (same : left = right) : prior.support left leftRun = prior.support right rightRun := by
  cases same
  rfl

theorem target_reads_the_same_complete_actual_account :
    (targetSupport prior current registered).1 =
      prior.support ((Epoch.Finance.consume input depth count registered.item current.account).next input depth count)
        (current.native.map fun earlier => earlier.concatRuns (Epoch.Finance.process input depth count)
          ((Epoch.Finance.consume input depth count registered.item current.account).transition input depth count)) := by
  change prior.support registered.admitted _ = prior.support _ _
  exact support_congr prior _ _ _ _ (the_same_actual_item_is_the_original_native_admission current registered).symm

theorem the_complete_old_support_is_the_same_source_target :
    (targetSupport prior current registered).1 = Accounting.support input depth count prior
      (Accounting.nativeNext input depth count prefixLimit renewalLimit oldPast start current) := by
  change prior.support registered.admitted _ = prior.support _ _
  exact support_congr prior _ _ _ _
    (Accounting.the_macro_hold_does_not_erase_a_new_issue_write
      input depth count prefixLimit renewalLimit oldPast start registered).symm

theorem the_same_admission_keeps_all_original_claims_and_history :
    current.account.current.slots.map (Epoch.Finance.slotClaim input depth count) <+:
        registered.admitted.current.slots.map (Epoch.Finance.slotClaim input depth count) ∧
      current.account.current.history <+: registered.admitted.current.history := by
  refine ⟨Epoch.Finance.run_retains_all_claims input depth count registered.nativeAdmission, ?_⟩
  rw [registered.nativeAdmission.history_eq]
  exact List.prefix_append _ _

#print axioms the_same_actual_item_is_the_original_native_admission
#print axioms target_reads_the_same_complete_actual_account
#print axioms the_same_admission_keeps_all_original_claims_and_history

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born
