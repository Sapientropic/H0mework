import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Outstanding.History.NativeExpired

/-! Old service states consume actual new-source visits after their own
deadline. New services remain independently admitted in the new window. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Service

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open OutstandingSource.History.NativeService
variable {oldScope : Mandate.Scope (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)}
  {bound : BoundSource base oldScope} {inputs : List (List Action)} (fresh : Handoff.Ready bound inputs)
noncomputable section

def observations (count : Nat) : List (ExpiredInput bound.source) :=
  (List.range count).filterMap (ExpiredInput.read bound.source (source fresh) (epochInputs fresh))

private theorem current_clock_after_initial (ordinal : Nat) :
    (I fresh).initial.clock ≤ (current fresh ordinal).clock := by
  induction ordinal with
  | zero => exact le_refl _
  | succ ordinal ih =>
    have step : (current fresh ordinal).clock ≤ (current fresh (ordinal + 1)).clock := by
      change (ProgrammeSource.rawCurrent (I fresh) (ProgrammeHistory.visitAt (I fresh) ordinal).current).clock ≤
        (ProgrammeSource.rawCurrent (I fresh)
          (ProgrammeSource.next (I fresh) (ProgrammeHistory.visitAt (I fresh) ordinal).current)).clock
      rw [ProgrammeSource.actual_raw_next]
      exact (I fresh).law.next_clock_nondecreasing _ _
    exact ih.trans step

theorem every_actual_new_visit_is_after_the_original_deadline
    (original_deadline : bound.source.seed.task.deadline = oldScope.task.deadline) (depth : Nat) :
    bound.source.seed.task.deadline < (current fresh (depth + 1)).clock := by
  rw [original_deadline]
  exact lt_of_lt_of_le fresh.actual_successor_is_after_the_expired_scope (current_clock_after_initial fresh (depth + 1))

theorem complete_observation_sequence_has_every_actual_visit_in_order
    (original_deadline : bound.source.seed.task.deadline = oldScope.task.deadline) (count : Nat) :
    (observations fresh count).map ExpiredInput.depth = List.range count := by
  unfold observations
  rw [List.map_filterMap]
  have select : (fun depth => Option.map ExpiredInput.depth
      (ExpiredInput.read bound.source (source fresh) (epochInputs fresh) depth)) = some := by
    funext depth
    simp only [ExpiredInput.read,dif_pos (every_actual_new_visit_is_after_the_original_deadline fresh original_deadline depth),Option.map_some]
  rw [select,List.filterMap_some]

theorem every_observation_has_its_actual_new_source (count : Nat) (input : ExpiredInput bound.source)
    (inside : input ∈ observations fresh count) :
    input.nextSource = source fresh ∧ input.nextInputs = epochInputs fresh ∧ input.depth < count := by
  obtain ⟨depth,member,selected⟩ := List.mem_filterMap.mp inside
  unfold ExpiredInput.read at selected
  split at selected
  · cases Option.some.inj selected
    exact ⟨rfl,rfl,List.mem_range.mp member⟩
  · cases selected

variable {originInputs : List (List Action)} {index : bound.source.Slot}

def continued (original : Thread bound.source originInputs index inputs) (count : Nat) :=
  (Expired.begin bound.source original).consume bound.source (observations fresh count)

theorem complete_original_slots_are_literal (original : Thread bound.source originInputs index inputs) (count : Nat) :
    (continued fresh original count).state.current.slots = original.state.current.slots :=
  (continued fresh original count).slots

theorem complete_original_history_then_actual_maintenance
    (original : Thread bound.source originInputs index inputs)
    (live : original.state.current.slots = [.live (OutstandingSource.History.NativeService.obligation bound.source originInputs index)]) (count : Nat) :
    (continued fresh original count).state.current.history = original.state.current.history ++
      (observations fresh count).map (Expired.image bound.source originInputs index) :=
  Expired.Continuation.consume_history bound.source _ live _

theorem complete_original_run_then_actual_maintenance
    (original : Thread bound.source originInputs index inputs)
    (live : original.state.current.slots = [.live (OutstandingSource.History.NativeService.obligation bound.source originInputs index)]) (count : Nat) :
    (continued fresh original count).state.generated.events = original.state.generated.events ++
      (observations fresh count).map (Expired.image bound.source originInputs index) :=
  Expired.whole_original_history_precedes_actual_maintenance bound.source original live _

theorem actual_native_trace_is_the_complete_observation_list
    (original : Thread bound.source originInputs index inputs)
    (live : original.state.current.slots = [.live (OutstandingSource.History.NativeService.obligation bound.source originInputs index)]) (count : Nat) :
    Expired.actualTrace bound.source originInputs (continued fresh original count).state.generated = observations fresh count :=
  Expired.complete_actual_trace_is_the_original_observation_list bound.source original live _

theorem original_terminal_state_and_history_are_literal
    (original : Thread bound.source originInputs index inputs) (terminal : original.state.current.TerminalAt 0) (count : Nat) :
    (continued fresh original count).state.current = original.state.current :=
  congrArg NativeResponsibilityProcess.GeneratedState.current
    (Expired.Continuation.terminal_state_is_literal bound.source (Expired.begin bound.source original) terminal _)

theorem every_crossing_has_the_new_sources_actual_write_before_word_and_after
    (count : Nat) (input : ExpiredInput bound.source) (inside : input ∈ observations fresh count) :
    input.nextSource = source fresh ∧ input.nextInputs = epochInputs fresh ∧
    input.depth < count ∧ input.Receipt bound.source ∧
    bound.source.seed.task.deadline < (input.actual bound.source).before.clock :=
  ⟨(every_observation_has_its_actual_new_source fresh count input inside).1,
    (every_observation_has_its_actual_new_source fresh count input inside).2.1,
    (every_observation_has_its_actual_new_source fresh count input inside).2.2,input.receipt bound.source,input.expired⟩

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Service
