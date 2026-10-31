import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.ActualPast.Fold
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.PublicPast.Fold
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Pending

/-! A fold of the existing root history, not an additional history registry.
Each source occurrence contributes its actual inventory once, after the
previous native account. Material execution stays with the original root. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count : Nat) (tag : Interface.Tag input depth count)

def initialAccount : Interface.Tag input depth count → (process input depth count).GeneratedState
  | .review .. | .migration .. => (settleCommitted input depth count).after
  | .actual prefixLimit renewalLimit start =>
      ActualPast.account input depth count prefixLimit renewalLimit start.past (settleCommitted input depth count).after
  | .publicActual prefixLimit renewalLimit oldPast start =>
      PublicPast.account input depth count prefixLimit renewalLimit oldPast start.past
        (ActualPast.account input depth count prefixLimit renewalLimit oldPast (settleCommitted input depth count).after)

def initialRun : (tag : Interface.Tag input depth count) →
    (process input depth count).Run (settleCommitted input depth count).after.current
      (initialAccount input depth count tag).current
  | .review .. | .migration .. => .nil
  | .actual prefixLimit renewalLimit start =>
      ActualPast.run input depth count prefixLimit renewalLimit start.past (settleCommitted input depth count).after
  | .publicActual prefixLimit renewalLimit oldPast start =>
      (ActualPast.run input depth count prefixLimit renewalLimit oldPast (settleCommitted input depth count).after).concatRuns
        (process input depth count)
        (PublicPast.run input depth count prefixLimit renewalLimit oldPast start.past
          (ActualPast.account input depth count prefixLimit renewalLimit oldPast (settleCommitted input depth count).after))

private def beforeFold : {current : (Interface.V input depth count tag).Current} →
    (Interface.root input depth count tag).ReachableAt current → (process input depth count).GeneratedState
  | _, .initial => initialAccount input depth count tag
  | _, .step prior _ => consumeVisit input depth count tag ⟨_, prior⟩ (beforeFold prior)

def beforeVisit (visit : Interface.Visit input depth count tag) : (process input depth count).GeneratedState :=
  beforeFold input depth count tag visit.history

def afterVisit (visit : Interface.Visit input depth count tag) : (process input depth count).GeneratedState :=
  consumeVisit input depth count tag visit (beforeVisit input depth count tag visit)

def visitRun (visit : Interface.Visit input depth count tag) :
    (process input depth count).Run (beforeVisit input depth count tag visit).current
      (afterVisit input depth count tag visit).current :=
  consumeVisit_run input depth count tag visit (beforeVisit input depth count tag visit)

theorem next_uses_the_same_continued_account (visit : Interface.Visit input depth count tag)
    {target : (Interface.V input depth count tag).Current}
    (nextEq : ((Interface.root input depth count tag).evolutionAt visit.current).nextCurrent? = some target) :
    beforeVisit input depth count tag (visit.next nextEq) = afterVisit input depth count tag visit := rfl

private def prefixRun : {current : (Interface.V input depth count tag).Current} →
    (history : (Interface.root input depth count tag).ReachableAt current) →
    (process input depth count).Run (initialAccount input depth count tag).current
      (beforeFold input depth count tag history).current
  | _, .initial => .nil
  | _, .step prior _ => (prefixRun prior).concatRuns (process input depth count)
      (consumeVisit_run input depth count tag ⟨_, prior⟩ (beforeFold input depth count tag prior))

def completeRun (visit : Interface.Visit input depth count tag) :
    (process input depth count).Run (inheritedAccount input depth count).current
      (afterVisit input depth count tag visit).current :=
  (((settleCommitted input depth count).transition.concatRuns (process input depth count)
    (initialRun input depth count tag)).concatRuns (process input depth count)
      (prefixRun input depth count tag visit.history)).concatRuns (process input depth count)
        (visitRun input depth count tag visit)

theorem original_history_is_a_prefix_at_every_epoch (visit : Interface.Visit input depth count tag) :
    (Settlement.oldCursor input depth count).account.current.history.map (Legacy.lifecycle input depth count) <+:
      (afterVisit input depth count tag visit).current.history :=
  Legacy.old_history_remains_a_prefix_of_every_native_extension input depth count _
    (completeRun input depth count tag visit)

theorem original_claims_keep_their_order_at_every_epoch (visit : Interface.Visit input depth count tag) :
    (Settlement.oldCursor input depth count).account.current.slots.map
        (fun slot => (Sum.inl (Financial.slotClaim input slot) : Claim input depth count)) <+:
      (afterVisit input depth count tag visit).current.slots.map (slotClaim input depth count) := by
  have retained := run_retains_all_claims input depth count (completeRun input depth count tag visit)
  rw [(inherited_actual_account_is_not_restarted input depth count).1, List.map_map] at retained
  have same : (fun slot => slotClaim input depth count (Legacy.slot input depth count slot)) =
      (fun slot => (Sum.inl (Financial.slotClaim input slot) : Claim input depth count)) := by
    funext slot
    cases slot <;> rfl
  simpa only [Function.comp_def, same] using retained

theorem epoch_successor_keeps_the_existing_debts (visit : Interface.Visit input depth count tag)
    {target : (Interface.V input depth count tag).Current}
    (nextEq : ((Interface.root input depth count tag).evolutionAt visit.current).nextCurrent? = some target) :
    (afterVisit input depth count tag visit).current.slots.map (slotClaim input depth count) <+:
      (afterVisit input depth count tag (visit.next nextEq)).current.slots.map (slotClaim input depth count) := by
  change _ <+: (consumeVisit input depth count tag (visit.next nextEq) _).current.slots.map _
  exact consumeVisit_preserves_original_claims input depth count tag _ _

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.completeRun
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.original_history_is_a_prefix_at_every_epoch
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.epoch_successor_keeps_the_existing_debts
