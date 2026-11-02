import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Contribution.Epoch.Complete
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Contribution.Source.Receipts

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Contribution.EpochHistory

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat)

/-- Literal read of the existing two source folds on the existing registered account. -/
abbrev completeAccount (oldPast past) :=
  Epoch.Finance.PublicPast.account input depth count prefixLimit renewalLimit oldPast past
    (Epoch.Finance.ActualPast.account input depth count prefixLimit renewalLimit oldPast
      (registeredBase input depth count sourceDepth sourceCount))

theorem the_public_source_fold_splits_at_its_actual_prefix (oldPast prior first second)
    (before : (Epoch.Finance.process input depth count).GeneratedState) :
    Epoch.Finance.PublicPast.foldFrom input depth count prefixLimit renewalLimit oldPast prior (first ++ second) before =
      Epoch.Finance.PublicPast.foldFrom input depth count prefixLimit renewalLimit oldPast (prior ++ first) second
        (Epoch.Finance.PublicPast.foldFrom input depth count prefixLimit renewalLimit oldPast prior first before) := by
  induction first generalizing prior before with
  | nil => simp only [List.nil_append,Epoch.Finance.PublicPast.foldFrom,List.append_nil]
  | cons raw rest inherited =>
      simp only [List.cons_append,Epoch.Finance.PublicPast.foldFrom,inherited,List.append_assoc,List.nil_append]

def originalPublicContinuation (oldPast past further) :
    (Epoch.Finance.process input depth count).Run
      (completeAccount input depth count prefixLimit renewalLimit sourceDepth sourceCount oldPast past).current
      (completeAccount input depth count prefixLimit renewalLimit sourceDepth sourceCount oldPast (past ++ further)).current := by
  change (Epoch.Finance.process input depth count).Run _
    (Epoch.Finance.PublicPast.foldFrom input depth count prefixLimit renewalLimit oldPast [] (past ++ further)
      (Epoch.Finance.ActualPast.account input depth count prefixLimit renewalLimit oldPast
        (registeredBase input depth count sourceDepth sourceCount))).current
  rw [the_public_source_fold_splits_at_its_actual_prefix,List.nil_append]
  exact Epoch.Finance.PublicPast.runFrom input depth count prefixLimit renewalLimit oldPast past further _

theorem every_actual_public_suffix_bounds_the_entire_original_contribution
    (oldPast past further)
    (index : Fin (completeAccount input depth count prefixLimit renewalLimit sourceDepth sourceCount oldPast past).current.slots.length) :
    Source.receivedForOrigin input depth count
      (originalPublicContinuation input depth count prefixLimit renewalLimit sourceDepth sourceCount oldPast past further)
      ((Epoch.Finance.slotClaim input depth count
        ((completeAccount input depth count prefixLimit renewalLimit sourceDepth sourceCount oldPast past).current.slots.get index)).origin input depth count) ≤
      (Epoch.Finance.slotClaim input depth count
        ((completeAccount input depth count prefixLimit renewalLimit sourceDepth sourceCount oldPast past).current.slots.get index)).quantity input depth count :=
  Source.a_source_unique_account_lifts_the_original_slot_bound input depth count _ _ index
    (the_complete_actual_account_cannot_reregister_an_original_contribution input depth count prefixLimit renewalLimit sourceDepth sourceCount oldPast (past ++ further))

theorem no_public_prefix_can_reregister_an_original_contribution_to_fund_unbounded_receipts
    (oldPast past)
    (index : Fin (completeAccount input depth count prefixLimit renewalLimit sourceDepth sourceCount oldPast past).current.slots.length)
    (demand : Nat → ℚ) (unbounded : ∀ bound : ℚ,∃ stage,demand stage > bound) :
    ¬ (∀ stage,∃ further,demand stage ≤ Source.receivedForOrigin input depth count
      (originalPublicContinuation input depth count prefixLimit renewalLimit sourceDepth sourceCount oldPast past further)
      ((Epoch.Finance.slotClaim input depth count
        ((completeAccount input depth count prefixLimit renewalLimit sourceDepth sourceCount oldPast past).current.slots.get index)).origin input depth count)) := by
  intro paid
  obtain ⟨stage,above⟩ := unbounded ((Epoch.Finance.slotClaim input depth count
    ((completeAccount input depth count prefixLimit renewalLimit sourceDepth sourceCount oldPast past).current.slots.get index)).quantity input depth count)
  obtain ⟨further,enough⟩ := paid stage
  exact (not_le_of_gt above) (enough.trans
    (every_actual_public_suffix_bounds_the_entire_original_contribution input depth count prefixLimit renewalLimit sourceDepth sourceCount oldPast past further index))

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Contribution.EpochHistory
