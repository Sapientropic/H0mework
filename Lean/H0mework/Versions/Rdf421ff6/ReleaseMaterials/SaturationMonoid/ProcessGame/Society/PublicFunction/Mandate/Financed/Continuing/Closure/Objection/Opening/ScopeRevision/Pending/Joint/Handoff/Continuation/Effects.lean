import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Continuation.Source

/-! Joint continuation consumes saved native histories, including every
expired service visit and the complete old/new financial matrix. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Continuation

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section

section NativeHistories
variable {oldScope : Mandate.Scope (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)}
  {bound : BoundSource base oldScope} {inputs : List (List Action)} {fresh : Handoff.Ready bound inputs}

theorem Grant.Saved.consume_events {record : Mandate.Challenge.Cross.GrantResident bound inputs} (saved : Grant.Saved fresh record)
    (source : Mandate.Challenge.ScopeBoundary.Source base) (receipts : List (Mandate.Challenge.ScopeBoundary.Receipt source)) :
    (saved.consume source receipts).entire.events = saved.entire.events ++ receipts.map (Grant.image source record.history.obligation) := by
  apply List.append_cancel_left (as := (Grant.origin record).history)
  rw [← List.append_assoc,← saved.entire.history_eq,← (saved.consume source receipts).entire.history_eq]
  exact saved.consume_history source receipts

theorem Challenge.Saved.consume_events {record : Mandate.Challenge.Cross.Resident bound inputs} (saved : Challenge.Saved fresh record)
    (source : Mandate.Challenge.ScopeBoundary.Source base) (later : oldScope.task.deadline < source.scope.task.earliest)
    (receipts : List (Mandate.Challenge.ScopeBoundary.Receipt source)) :
    (saved.consume source later receipts).state.generated.events = saved.state.generated.events ++ Challenge.images saved source later receipts := by
  rw [← NativeResponsibilityProcess.GeneratedState.history_eq,Challenge.Saved.consume_history,saved.state.history_eq]

end NativeHistories

variable {fuel : ℚ} {old : Followup.Joint.Inventory fuel} {authority : ScopeRevision.Ready old}
  {originInputs : List (List Action)} {inventory : Pending.Joint.Inventory authority originInputs}
  {fresh : Handoff.Ready (Pending.B authority) (Future.advance authority inventory .revision).inputs}

private theorem clock_after_initial (inputs : List (List Action)) (ordinal : Nat) :
    (Handoff.I fresh).initial.clock ≤ (OutstandingSource.History.currentAt (source fresh) inputs ordinal).clock := by
  induction ordinal with
  | zero => exact le_refl _
  | succ ordinal ih =>
    have step : (OutstandingSource.History.currentAt (source fresh) inputs ordinal).clock ≤
        (OutstandingSource.History.currentAt (source fresh) inputs (ordinal + 1)).clock := by
      change (ProgrammeSource.rawCurrent (inputAt fresh inputs) (ProgrammeHistory.visitAt (inputAt fresh inputs) ordinal).current).clock ≤
        (ProgrammeSource.rawCurrent (inputAt fresh inputs)
          (ProgrammeSource.next (inputAt fresh inputs) (ProgrammeHistory.visitAt (inputAt fresh inputs) ordinal).current)).clock
      rw [ProgrammeSource.actual_raw_next]
      exact (inputAt fresh inputs).law.next_clock_nondecreasing _ _
    exact ih.trans step

theorem old_service_observation_is_exactly_the_new_actual_visit (saved : Inventory authority inventory fresh) (word : List Action) :
    (observations saved word).map OutstandingSource.History.NativeService.ExpiredInput.depth = [saved.inputs.length + 1] := by
  have expired : (Pending.B authority).source.seed.task.deadline <
      (OutstandingSource.History.currentAt (source fresh) (saved.inputs ++ [word]) (saved.inputs.length + 1 + 1)).clock :=
    lt_of_lt_of_le fresh.actual_successor_is_after_the_expired_scope (clock_after_initial _ _)
  simp only [observations,OutstandingSource.History.NativeService.ExpiredInput.read,dif_pos expired,Option.toList_some,List.map_cons,List.map_nil]

theorem observation_uses_the_exact_submitted_word (saved : Inventory authority inventory fresh) (word : List Action)
    (observation : OutstandingSource.History.NativeService.ExpiredInput (Pending.B authority).source)
    (inside : observation ∈ observations saved word) :
    observation.nextSource = source fresh ∧ observation.nextInputs = (submit saved word).inputs ∧
    observation.depth = saved.inputs.length + 1 ∧
    (observation.actual (Pending.B authority).source).submitted = word := by
  unfold observations OutstandingSource.History.NativeService.ExpiredInput.read at inside
  split at inside
  · simp only [Option.toList_some,List.mem_singleton] at inside
    subst observation
    exact ⟨rfl,rfl,rfl,(actual_word_and_cut saved word).1⟩
  · simp only [Option.toList_none,List.not_mem_nil] at inside

theorem old_service_slots_remain_literal (saved : Inventory authority inventory fresh) (word : List Action)
    (index : (Pending.B authority).source.Slot) :
    ((submit saved word).oldServices index).state.current.slots = (saved.oldServices index).state.current.slots :=
  ((submit saved word).oldServices index).slots.trans (saved.oldServices index).slots.symm

theorem old_service_complete_native_run_consumes_the_saved_state (saved : Inventory authority inventory fresh) (word : List Action)
    (index : (Pending.B authority).source.Slot)
    (live : ((oldInventory authority inventory).services index).state.current.slots =
      [.live (OutstandingSource.History.NativeService.obligation (Pending.B authority).source originInputs index)]) :
    ((submit saved word).oldServices index).state.generated.events = (saved.oldServices index).state.generated.events ++
      (observations saved word).map (OutstandingSource.History.NativeService.Expired.image (Pending.B authority).source originInputs index) := by
  rw [← NativeResponsibilityProcess.GeneratedState.history_eq]
  exact (OutstandingSource.History.NativeService.Expired.Continuation.consume_history
    (Pending.B authority).source (saved.oldServices index) live (observations saved word)).trans
      (congrArg (fun past => past ++ (observations saved word).map
        (OutstandingSource.History.NativeService.Expired.image (Pending.B authority).source originInputs index))
        (saved.oldServices index).state.history_eq)

theorem old_terminal_service_is_literal (saved : Inventory authority inventory fresh) (word : List Action)
    (index : (Pending.B authority).source.Slot)
    (terminal : ((oldInventory authority inventory).services index).state.current.TerminalAt 0) :
    ((submit saved word).oldServices index).state = (saved.oldServices index).state :=
  OutstandingSource.History.NativeService.Expired.Continuation.terminal_state_is_literal _ _ terminal _

theorem finite_joint_evolution_preserves_original_grants (saved : Inventory authority inventory fresh) (count : Nat) :
    (evolve saved count).oldGrants.map Sigma.fst = saved.oldGrants.map Sigma.fst := by
  induction count generalizing saved with
  | zero => rfl
  | succ count ih =>
    change (evolve (advance saved) count).oldGrants.map Sigma.fst = _
    rw [ih,advance,every_saved_grant_keeps_its_original_record_in_order,staged,every_saved_grant_keeps_its_original_record_in_order]

theorem finite_joint_evolution_preserves_original_challenges (saved : Inventory authority inventory fresh) (count : Nat) :
    (evolve saved count).oldChallenges.map Sigma.fst = saved.oldChallenges.map Sigma.fst := by
  induction count generalizing saved with
  | zero => rfl
  | succ count ih =>
    change (evolve (advance saved) count).oldChallenges.map Sigma.fst = _
    rw [ih,advance,every_saved_challenge_keeps_its_original_record_in_order,staged,every_saved_challenge_keeps_its_original_record_in_order]

def evolutionFinancialMigration (saved : Inventory authority inventory fresh) (count index : Nat)
    (slot : ObligationSlot (Financial.Family.vocabulary Pending.Joint.Finance.sources))
    (present : saved.finance.current.slots[index]? = some slot) :=
  Financial.Family.Migration.follow _ (evolutionFinanceRun saved count) index slot present

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Continuation
