import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.IncidentCompletion

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SilentWindow

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

def quiet : Rule code where
  work := ⟨fun _ _ => [], by
    apply code.every_local_policy_is_enumerated
    intro key member
    exact (mem_words_iff _ _ _).mpr (by simp)⟩
  events := fun _ _ => ⟨none, List.mem_cons_self⟩

def environment : Opponent code := fun _ _ _ => none

def cursorAt (cursor : Cursor code) : Nat → Cursor code
  | 0 => cursor
  | count + 1 => (cursorAt cursor count).after quiet environment

def stages : Nat → List (EventHistory.Stage (code := code))
  | 0 => []
  | count + 1 => stages count ++ [(quiet, environment)]

omit [DecidableEq Port] [DecidableEq Technology] in
theorem stage_count (count : Nat) : (stages (code := code) count).length = count := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [stages, List.length_append, List.length_singleton, ih]

theorem execution_is_the_actual_cursor (cursor : Cursor code) (count : Nat) :
    EventHistory.execute cursor (stages count) = cursorAt cursor count := by
  induction count with
  | zero => rfl
  | succ count ih => rw [stages, StageQueue.execute_append, ih]; rfl

theorem no_admitted_event (cursor : Cursor code) :
    decision code (EventStep.applied cursor quiet environment) (EventStep.seed cursor) = none := by
  unfold decision EventStep.applied Cursor.controller driver
  split
  · rfl
  · dsimp only
    split <;> rfl

theorem actual_empty_step (cursor : Cursor code) :
    EventStep.seed (cursor.after quiet environment) =
      ⟨code.law.next (EventStep.seed cursor).current [], (EventStep.seed cursor).history ++ [[]],
        (EventStep.seed cursor).past, (EventStep.seed cursor).frame, (EventStep.seed cursor).remaining - 1⟩ := by
  rw [EventStep.actual_next_state]
  simp only [Reaction.Feedback.advance, word, no_admitted_event]

structure Preserves (first last : Cursor code) (count : Nat) : Prop where
  frame : (EventStep.seed last).frame = (EventStep.seed first).frame
  past : (EventStep.seed last).past = (EventStep.seed first).past
  stock : (EventStep.seed last).current.stock = (EventStep.seed first).current.stock
  claims : (EventStep.seed last).current.claims = (EventStep.seed first).current.claims
  technology : (EventStep.seed last).current.technology = (EventStep.seed first).current.technology
  history : (EventStep.seed last).history.length = (EventStep.seed first).history.length + count
  fuel : (EventStep.seed last).remaining = (EventStep.seed first).remaining - count
  roster : last.ownerStart = first.ownerStart

theorem preserves_the_actual_state (cursor : Cursor code) (count : Nat) : Preserves cursor (cursorAt cursor count) count := by
  induction count with
  | zero => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | succ count ih =>
    have step := actual_empty_step (cursorAt cursor count)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ih.roster⟩
    · exact (congrArg State.frame step).trans ih.frame
    · exact (congrArg State.past step).trans ih.past
    · exact (congrArg (fun state : State code => state.current.stock) step).trans ih.stock
    · exact (congrArg (fun state : State code => state.current.claims) step).trans ih.claims
    · exact (congrArg (fun state : State code => state.current.technology) step).trans ih.technology
    · change (EventStep.seed ((cursorAt cursor count).after _ _)).history.length = _
      rw [step, List.length_append, List.length_singleton, ih.history]
      omega
    · change (EventStep.seed ((cursorAt cursor count).after _ _)).remaining = _
      rw [step, ih.fuel]
      change (EventStep.seed cursor).remaining - count - 1 = (EventStep.seed cursor).remaining - (count + 1)
      omega

-- Pick the next complete roster cycle, using the cursor's original origin.
def targetLength (cursor : Cursor code) (receiver : Fin code.sites) : Nat :=
  cursor.ownerStart + 2 * ((((EventStep.seed cursor).history.length - cursor.ownerStart) / (2 * code.sites) + 1) * code.sites + receiver.val)

def delay (cursor : Cursor code) (receiver : Fin code.sites) : Nat :=
  if Distributed.Recall.Information.Agency.ownerAt code cursor.ownerStart (EventStep.seed cursor).history.length = some receiver then 0
  else targetLength cursor receiver - (EventStep.seed cursor).history.length

theorem target_is_after_the_current_history (cursor : Cursor code) (receiver : Fin code.sites) :
    (EventStep.seed cursor).history.length ≤ targetLength cursor receiver := by
  have positive : 0 < 2 * code.sites := by have := receiver.isLt; omega
  have remainder := Nat.mod_lt ((EventStep.seed cursor).history.length - cursor.ownerStart) positive
  have divided := Nat.mod_add_div ((EventStep.seed cursor).history.length - cursor.ownerStart) (2 * code.sites)
  have shape : 2 * ((((EventStep.seed cursor).history.length - cursor.ownerStart) / (2 * code.sites) + 1) * code.sites + receiver.val) =
      2 * code.sites * (((EventStep.seed cursor).history.length - cursor.ownerStart) / (2 * code.sites)) + 2 * code.sites + 2 * receiver.val := by ring
  unfold targetLength
  rw [shape]
  omega

theorem the_actual_receiver_owns_the_generated_arrival (cursor : Cursor code) (receiver : Fin code.sites) :
    Distributed.Recall.Information.Agency.ownerAt code (cursorAt cursor (delay cursor receiver)).ownerStart
      (EventStep.seed (cursorAt cursor (delay cursor receiver))).history.length = some receiver := by
  have facts := preserves_the_actual_state cursor (delay cursor receiver)
  rw [facts.roster, facts.history]
  unfold delay
  split
  · rename_i owned
    simpa only [Nat.add_zero] using owned
  · rw [Nat.add_sub_of_le (target_is_after_the_current_history cursor receiver)]
    unfold targetLength Distributed.Recall.Information.Agency.ownerAt
    have positive : 0 < code.sites := Nat.zero_lt_of_lt receiver.isLt
    simp only [dif_pos positive, Nat.add_sub_cancel_left, Nat.mul_mod_right, if_true, Nat.mul_div_cancel_left _ (by omega : 0 < 2), Nat.add_mod,
      Nat.mul_mod_left, Nat.zero_add, Nat.mod_eq_of_lt receiver.isLt]

theorem the_generated_delay_has_a_source_roster_bound (cursor : Cursor code) (receiver : Fin code.sites) :
    delay cursor receiver < cursor.ownerStart - (EventStep.seed cursor).history.length + 4 * code.sites := by
  have positive : 0 < code.sites := Nat.zero_lt_of_lt receiver.isLt
  unfold delay
  split
  · omega
  · have remainder := Nat.mod_lt ((EventStep.seed cursor).history.length - cursor.ownerStart) (by omega : 0 < 2 * code.sites)
    have divided := Nat.mod_add_div ((EventStep.seed cursor).history.length - cursor.ownerStart) (2 * code.sites)
    have member := receiver.isLt
    have shape : 2 * ((((EventStep.seed cursor).history.length - cursor.ownerStart) / (2 * code.sites) + 1) * code.sites + receiver.val) =
        2 * code.sites * (((EventStep.seed cursor).history.length - cursor.ownerStart) / (2 * code.sites)) + 2 * code.sites + 2 * receiver.val := by ring
    unfold targetLength
    rw [shape]
    omega

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SilentWindow
