import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Runtime.Ingress
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Observation.Runtime

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered
open Functions.Revision

noncomputable section

variable (nature : RequestAt)
  {origin : Context (input := input) (review := none) 0 count 0 0 0 count}
  {admission : InitialAdmissionAt origin}
  (frame : Macro.Public.Runtime.Frame origin admission) (tick : Nat)
  (actual : current nature tick = .enacted origin admission frame)

include actual

theorem the_actual_trial_source_uses_its_original_installed_reader :
    Macro.Runtime.originalProposal frame = selected nature frame.actual.readerCursor.past := by
  have sourced := Observation.the_actual_origin_reader_is_not_caller_supplied frame tick actual
  exact congrFun (congrFun sourced frame.actual.readerCursor) frame.account

omit actual in
theorem the_trial_reader_cursor_is_the_literal_absolute_source_prefix :
    frame.actual.readerCursor.past = origin.germ.snapshot.past ++ frame.snapshot.past := by
  change (Physical.receive (Physical.Prefix.cursor
    (origin.germ.snapshot.past ++ frame.actual.snapshot.past)) frame.actual.snapshot.incoming).past = _
  exact Physical.Prefix.past_readback _

theorem every_explicit_trial_attempt_is_the_actual_public_selection
    (raw : InputAt) (source : selected nature frame.actual.readerCursor.past = raw)
    (explicit : raw ≠ .advance) : frame.actual.proposal frame.reader = raw := by
  have selected := Macro.Runtime.every_actual_public_proposal_is_the_current_source_selection datum (reader nature)
    frame tick actual
  rw [the_actual_trial_source_uses_its_original_installed_reader nature frame tick actual, source] at selected
  cases raw <;> first | exact False.elim (explicit rfl) | exact selected

theorem every_actual_trial_primitive_is_consumed_with_its_literal_next
    (request : RequestAt) (source : selected nature frame.actual.readerCursor.past = .primitive request)
    (complete : ¬ frame.HasWork) :
    frame.actual.proposal frame.reader = .primitive request ∧
      frame.next.snapshot = Physical.next (Physical.receive frame.snapshot (.primitive request)) ∧
      frame.next.account = frame.account := by
  have proposal := every_explicit_trial_attempt_is_the_actual_public_selection nature frame tick actual
    (.primitive request) source (by intro impossible; cases impossible)
  refine ⟨proposal, ?_, ?_⟩
  · rw [Macro.Public.Runtime.Frame.next, dif_neg complete]
    change Physical.next (Macro.Public.Scope.selectedCursor input 0 count 0 0 origin.germ.snapshot.past
      frame.snapshot (frame.actual.proposal frame.reader)) = _
    rw [proposal]
    rfl
  · rw [Macro.Public.Runtime.Frame.next, dif_neg complete]
    exact frame.raw_reentry_keeps_the_literal_complete_account complete

theorem every_actual_trial_code_is_consumed_with_its_literal_next
    (word : Source.Program.RawEvent Party Good Bool Nat Unit)
    (source : selected nature frame.actual.readerCursor.past = .code ⟨word⟩)
    (complete : ¬ frame.HasWork) :
    frame.next.snapshot = Physical.next (Physical.receive frame.snapshot (.code ⟨word⟩)) ∧
      frame.next.account = frame.account := by
  have proposal := every_explicit_trial_attempt_is_the_actual_public_selection nature frame tick actual
    (.code ⟨word⟩) source (by intro impossible; cases impossible)
  constructor
  · rw [Macro.Public.Runtime.Frame.next, dif_neg complete]
    change Physical.next (Macro.Public.Scope.selectedCursor input 0 count 0 0 origin.germ.snapshot.past
      frame.snapshot (frame.actual.proposal frame.reader)) = _
    rw [proposal]
    rfl
  · rw [Macro.Public.Runtime.Frame.next, dif_neg complete]
    exact frame.raw_reentry_keeps_the_literal_complete_account complete

theorem every_actual_trial_period_passes_the_original_scope_before_its_literal_next
    (word : Source.Program.RawEvent Party Good Bool Nat Unit)
    (source : selected nature frame.actual.readerCursor.past = .execute word)
    (checked : Macro.Public.Scope.Checks input 0 count 0 0 origin.germ.snapshot.past frame.snapshot
      (PublicPlan.executable word)) (complete : ¬ frame.HasWork) :
    frame.next.snapshot = Physical.next (Physical.receive frame.snapshot (.execute word)) ∧
      frame.next.account = frame.account := by
  have proposal := every_explicit_trial_attempt_is_the_actual_public_selection nature frame tick actual
    (.execute word) source (by intro impossible; cases impossible)
  have forwarded := (Macro.Public.Scope.every_checked_period_executes_the_original_proposal
    input 0 count 0 0 origin.germ.snapshot.past frame.snapshot (.execute word)
    (PublicPlan.executable word) rfl checked).1
  constructor
  · rw [Macro.Public.Runtime.Frame.next, dif_neg complete]
    change Physical.next (Macro.Public.Scope.selectedCursor input 0 count 0 0 origin.germ.snapshot.past
      frame.snapshot (frame.actual.proposal frame.reader)) = _
    rw [proposal]
    exact congrArg Physical.next (congrArg (Physical.receive frame.snapshot) forwarded)
  · rw [Macro.Public.Runtime.Frame.next, dif_neg complete]
    exact frame.raw_reentry_keeps_the_literal_complete_account complete

omit actual in
theorem the_original_next_still_contains_every_prior_claim_and_history :
    frame.account.current.history <+: frame.next.account.current.history ∧
      frame.account.current.slots.map (Epoch.Finance.slotClaim input 0 count) <+:
        frame.next.account.current.slots.map (Epoch.Finance.slotClaim input 0 count) :=
  ⟨frame.next_keeps_the_complete_original_history, frame.next_keeps_all_original_claims⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation
