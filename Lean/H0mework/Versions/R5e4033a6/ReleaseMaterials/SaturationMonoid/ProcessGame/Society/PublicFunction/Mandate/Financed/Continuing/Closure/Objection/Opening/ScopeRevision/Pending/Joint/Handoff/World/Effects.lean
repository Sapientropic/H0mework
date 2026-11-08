import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Source

/-! Past-cohort transitions preserve complete native runs and actual
observation traces. Financial migration follows every finite epoch chain. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section

theorem GrantCohort.actual_receipts_extend_the_complete_native_run (entry : GrantCohort)
    (source : Mandate.Challenge.ScopeBoundary.Source base) (receipts : List (Mandate.Challenge.ScopeBoundary.Receipt source)) :
    (entry.advance source receipts).saved.entire.events = entry.saved.entire.events ++
      receipts.map (Continuation.Grant.image source entry.origin.2.history.obligation) :=
  Continuation.Grant.Saved.consume_events entry.saved source receipts

theorem ChallengeCohort.actual_receipts_extend_the_complete_native_run {scope : Scope} (entry : ChallengeCohort scope)
    (source : Mandate.Challenge.ScopeBoundary.Source base) (follow : scope.task.earliest ≤ source.scope.task.earliest)
    (receipts : List (Mandate.Challenge.ScopeBoundary.Receipt source)) :
    (entry.advance source follow receipts).saved.state.generated.events = entry.saved.state.generated.events ++
      Continuation.Challenge.images entry.saved source (lt_of_lt_of_le entry.later follow) receipts :=
  Continuation.Challenge.Saved.consume_events entry.saved source _ receipts

theorem ChallengeCohort.original_slots_and_admissions_are_literal {scope : Scope} (entry : ChallengeCohort scope)
    (source : Mandate.Challenge.ScopeBoundary.Source base) (follow : scope.task.earliest ≤ source.scope.task.earliest)
    (receipts : List (Mandate.Challenge.ScopeBoundary.Receipt source)) :
    (entry.advance source follow receipts).saved.state.current.slots = entry.saved.state.current.slots :=
  Continuation.Challenge.Saved.consume_slots entry.saved source _ receipts

theorem ServiceCohort.actual_trace_extends_from_the_complete_saved_run {initialClock : ℚ} (entry : ServiceCohort initialClock)
    (source : Mandate.Challenge.ScopeBoundary.Source base) (clock : initialClock ≤ source.bound.source.seed.initial.clock)
    (start count : Nat)
    (live : entry.origin.original.state.current.slots =
      [.live (OutstandingSource.History.NativeService.obligation entry.origin.source entry.origin.originInputs entry.origin.index)]) :
    OutstandingSource.History.NativeService.Expired.actualTrace entry.origin.source entry.origin.originInputs
      (entry.advance source clock start count).saved.state.generated =
    OutstandingSource.History.NativeService.Expired.actualTrace entry.origin.source entry.origin.originInputs entry.saved.state.generated ++
      entry.observations source start count :=
  OutstandingSource.History.NativeService.Expired.Continuation.consume_trace entry.origin.source entry.saved live _

theorem ServiceCohort.terminal_state_is_literal {initialClock : ℚ} (entry : ServiceCohort initialClock)
    (source : Mandate.Challenge.ScopeBoundary.Source base) (clock : initialClock ≤ source.bound.source.seed.initial.clock)
    (start count : Nat) (terminal : entry.origin.original.state.current.TerminalAt 0) :
    (entry.advance source clock start count).saved.state = entry.saved.state :=
  OutstandingSource.History.NativeService.Expired.Continuation.terminal_state_is_literal entry.origin.source entry.saved terminal _

variable {epoch : Epoch} (inventory : Inventory epoch)

def reviewServiceRun (index : epoch.source.Slot) :
    (OutstandingSource.History.NativeService.threadProcess epoch.source (epochInputs epoch.fresh)).Run
      (inventory.services index).state.current ((reviewed inventory).services index).state.current :=
  ((inventory.services index).actualRun epoch.source (reviewWord inventory)).concatRuns _
    (((staged inventory).services index).actualRun epoch.source (repaymentWord inventory))

def every_original_financial_slot_follows_the_actual_epoch_chain (count index : Nat)
    (slot : ObligationSlot (Financial.Family.vocabulary sources))
    (present : inventory.finance.current.slots[index]? = some slot) :=
  Financial.Family.Migration.follow sources (evolutionFinancialRun ⟨epoch,inventory⟩ count) index slot present

theorem every_finite_epoch_chain_has_the_actual_complete_matrix (packet : Packet) (count : Nat) :
    Financial.Family.ledgerClaims sources (evolve packet count).2.finance.current =
      (current (evolve packet count).1 (evolve packet count).2.inputs).claims := (evolve packet count).2.matrix

theorem every_finite_external_input_chain_has_the_actual_complete_matrix (packet : Packet) (words : List (List Action)) :
    Financial.Family.ledgerClaims sources (alternate packet words).2.finance.current =
      (current (alternate packet words).1 (alternate packet words).2.inputs).claims := (alternate packet words).2.matrix

theorem generated_packet_of_selected (fresh : Handoff.Ready epoch.bound inventory.inputs)
    (selected : Handoff.choose epoch.bound inventory.inputs = some fresh) :
    (generate inventory).packet inventory = ⟨Epoch.ofFresh fresh,handoff inventory fresh⟩ := by
  unfold generate
  split
  · rename_i actual found
    have same : actual = fresh := Option.some.inj (found.symm.trans selected)
    cases same
    rfl
  · rename_i absent
    have impossible := absent.symm.trans selected
    cases impossible

theorem Result.all_original_cohorts_are_prefixes (result : Result inventory) :
    inventory.pastGrants.map GrantCohort.origin <+: (result.packet inventory).2.pastGrants.map GrantCohort.origin ∧
    inventory.pastChallenges.map ChallengeCohort.origin <+: (result.packet inventory).2.pastChallenges.map ChallengeCohort.origin ∧
    inventory.pastServices.map ServiceCohort.origin <+: (result.packet inventory).2.pastServices.map ServiceCohort.origin := by
  cases result
  next fresh selected next same =>
    subst next
    have census := all_cohort_censuses_include_every_old_and_every_current_birth inventory fresh
    refine ⟨?_,?_,?_⟩
    · exact ⟨_,census.1.symm⟩
    · exact ⟨_,census.2.1.symm⟩
    · exact ⟨_,census.2.2.symm⟩
  next absent reason => exact ⟨List.prefix_rfl,List.prefix_rfl,List.prefix_rfl⟩

theorem next_preserves_all_original_cohort_prefixes :
    inventory.pastGrants.map GrantCohort.origin <+: (next inventory).2.pastGrants.map GrantCohort.origin ∧
    inventory.pastChallenges.map ChallengeCohort.origin <+: (next inventory).2.pastChallenges.map ChallengeCohort.origin ∧
    inventory.pastServices.map ServiceCohort.origin <+: (next inventory).2.pastServices.map ServiceCohort.origin := by
  have first := every_past_origin_keeps_order_and_multiplicity inventory (reviewWord inventory)
  have second := every_past_origin_keeps_order_and_multiplicity (staged inventory) (repaymentWord inventory)
  have result := Result.all_original_cohorts_are_prefixes (reviewed inventory) (cycleResult inventory)
  refine ⟨?_,?_,?_⟩
  · have same : (reviewed inventory).pastGrants.map GrantCohort.origin = inventory.pastGrants.map GrantCohort.origin := second.1.trans first.1
    rw [← same]; exact result.1
  · have same : (reviewed inventory).pastChallenges.map ChallengeCohort.origin = inventory.pastChallenges.map ChallengeCohort.origin := second.2.1.trans first.2.1
    rw [← same]; exact result.2.1
  · have same : (reviewed inventory).pastServices.map ServiceCohort.origin = inventory.pastServices.map ServiceCohort.origin := second.2.2.trans first.2.2
    rw [← same]; exact result.2.2

theorem finite_epoch_chains_preserve_every_original_cohort (packet : Packet) (count : Nat) :
    packet.2.pastGrants.map GrantCohort.origin <+: (evolve packet count).2.pastGrants.map GrantCohort.origin ∧
    packet.2.pastChallenges.map ChallengeCohort.origin <+: (evolve packet count).2.pastChallenges.map ChallengeCohort.origin ∧
    packet.2.pastServices.map ServiceCohort.origin <+: (evolve packet count).2.pastServices.map ServiceCohort.origin := by
  induction count generalizing packet with
  | zero => exact ⟨List.prefix_rfl,List.prefix_rfl,List.prefix_rfl⟩
  | succ count ih =>
    have first := next_preserves_all_original_cohort_prefixes packet.2
    have later := ih (next packet.2)
    exact ⟨first.1.trans later.1,first.2.1.trans later.2.1,first.2.2.trans later.2.2⟩

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World
