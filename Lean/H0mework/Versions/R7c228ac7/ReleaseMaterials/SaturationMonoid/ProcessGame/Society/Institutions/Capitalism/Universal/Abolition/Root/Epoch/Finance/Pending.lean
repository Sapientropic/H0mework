import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Inherited

/-! Finish already occurred original requests through their original native
consumer. Its Run is then transported into the extended account. Deferred
prospective requests remain attached to the old source and are not issued. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count : Nat)

private def originalPendingRun := Financial.consumeOrigins_run input
  (committedPending input depth count) (Settlement.oldCursor input depth count).account

structure SettledInherited where
  private mk ::
  after : (process input depth count).GeneratedState
  transition : (process input depth count).Run
    (inheritedAccount input depth count).current after.current
  faithful : after.current = Legacy.state input depth count
    (Financial.consumeOrigins input (committedPending input depth count)
      (Settlement.oldCursor input depth count).account).current

private def settleCommittedRun : SettledInherited input depth count :=
  let computed := Legacy.foldRun input depth count (originalPendingRun input depth count)
  let continuation : (process input depth count).Run
      (inheritedAccount input depth count).current computed.target := by
    rw [inheritedAccount, Legacy.generated_current]
    exact computed.run
  ⟨⟨computed.target, (inheritedAccount input depth count).generated.concatRuns
      (process input depth count) continuation⟩, continuation, computed.faithful⟩

/-- With no occurred pending request, retain the literal carried account.
This branch generates neither a native event nor a replacement history. -/
def settleCommitted : SettledInherited input depth count :=
  match pending : committedPending input depth count with
  | [] => ⟨inheritedAccount input depth count, .nil, by
      simpa only [pending, Financial.consumeOrigins, inheritedAccount] using
        (Legacy.generated_current input depth count (Settlement.oldCursor input depth count).account)⟩
  | _ :: _ => settleCommittedRun input depth count

theorem empty_pending_keeps_the_literal_inherited_account
    (empty : committedPending input depth count = []) :
    (settleCommitted input depth count).after = inheritedAccount input depth count := by
  unfold settleCommitted
  split
  · rfl
  · rename_i head tail nonempty
    cases nonempty.symm.trans empty

theorem settlement_appends_original_history :
    (Settlement.oldCursor input depth count).account.current.history.map (Legacy.lifecycle input depth count) <+:
      (settleCommitted input depth count).after.current.history :=
  Legacy.old_history_remains_a_prefix_of_every_native_extension input depth count _
    (settleCommitted input depth count).transition

theorem no_prospective_request_is_consumed
    (origin : Financial.InstructionOrigin input) (deferred : origin ∈ deferredRequests input depth count) :
    origin ∉ committedPending input depth count := by
  intro committed
  exact (of_decide_eq_true (List.mem_filter.mp deferred).2)
    (of_decide_eq_true (List.mem_filter.mp committed).2)

theorem every_consumed_request_has_the_original_committed_visit
    (origin : Financial.InstructionOrigin input) (consumed : origin ∈ committedPending input depth count) :
    ∃ ordinal < Settlement.physicalIndex input depth count,
      origin.visit = ProgrammeHistory.visitAt input ordinal :=
  actual_pending_has_a_strictly_committed_origin input depth count origin consumed

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.settleCommitted
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.no_prospective_request_is_consumed
