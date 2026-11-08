import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RenewedDispatchSource
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CachedWorkDispatch
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 80000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RenewedDispatchTrace
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open RenewedDispatchSource
abbrev point := DispatchWindowChecks.point
abbrev literalPoint := PaidInvocationRebase.cursor
 (PaidInvocationSource.paid DispatchWindowSource.old DispatchWindowSource.contract DispatchWindowChecks.literalSaved true true) 36

theorem point_is_the_original_checked_paid_successor : point = literalPoint := by
 change PaidInvocationRebase.cursor (PaidInvocationSource.paid DispatchWindowSource.old DispatchWindowSource.contract DispatchWindowSource.saved true true) 36 = _
 rw [DispatchWindowChecks.saved_is_the_original_checked_execution]

def emitted : List LocalCommandSource.Input :=
 [.event 6,.command 0,.event 7,.idle,.event 8,.command 1,.event 9,.command 2,.idle,
  .event 3,.event 13,.command 3,.idle,.event 5,.event 14,.event 2,.event 15,.idle,.idle,.event 4,.event 16]
def inputs := LocalCommandSource.Input.command 0 :: emitted

def checks (saved : Cursor old) : List LocalCommandSource.Input → State saved → Bool :=
 List.rec (fun _ => true) (fun input _ verify state =>
  decide (choose saved state = input) && verify (LocalCommandRun.step (model saved) (start saved) state input))

theorem checked_inputs_generate_the_original_execution
 (saved : Cursor old) (state : State saved) (commands : List LocalCommandSource.Input)
 (checked : checks saved commands state = true) :
 (journey saved state commands.length).1 = commands.foldl (LocalCommandRun.step (model saved) (start saved)) state := by
 induction commands generalizing state with
 | nil => rfl
 | cons input tail ih =>
  have both : decide (choose saved state = input) = true ∧
   checks saved tail (LocalCommandRun.step (model saved) (start saved) state input) = true :=
   by simpa only [checks,Bool.and_eq_true] using checked
  have first := of_decide_eq_true both.1
  have rest := ih (LocalCommandRun.step (model saved) (start saved) state input) both.2
  have resumed := WorkDispatch.resuming_the_actual_state_is_the_same_generated_execution
   (model saved) (start saved) (vocabulary saved) (law saved) work state 1 tail.length
  change (journey saved state (tail.length+1)).1 = _
  rw [Nat.add_comm tail.length 1,resumed]
  change (journey saved (LocalCommandRun.step (model saved) (start saved) state (choose saved state)) tail.length).1 = _
  rw [first]
  exact rest

def cachedChecks (saved : Cursor old) (commands : List LocalCommandSource.Input) :
 {state : State saved} → CachedCommandRun.Cache (model saved) (start saved) state → Bool :=
 commands.rec (motive := fun _ => {state : State saved} →
  CachedCommandRun.Cache (model saved) (start saved) state → Bool)
  (fun {_} _ => true) (fun input _ verify {_} cache =>
  decide (CachedWorkDispatch.choose (vocabulary saved) (law saved) work cache = input) &&
   verify (CachedCommandRun.step (model saved) (start saved) cache input))

theorem cached_checks_are_the_same_original_current_state_checker
 (saved : Cursor old) (commands : List LocalCommandSource.Input)
 {state : State saved} (cache : CachedCommandRun.Cache (model saved) (start saved) state) :
 cachedChecks saved commands cache = checks saved commands state := by
 induction commands generalizing state with
 | nil => rfl
 | cons input tail ih =>
  change (decide (CachedWorkDispatch.choose (vocabulary saved) (law saved) work cache = input) &&
    cachedChecks saved tail (CachedCommandRun.step (model saved) (start saved) cache input)) =
   (decide (choose saved state = input) &&
    checks saved tail (LocalCommandRun.step (model saved) (start saved) state input))
  rw [CachedWorkDispatch.choose_eq,ih]

def initialCache (saved : Cursor old) : CachedCommandRun.Cache (model saved) (start saved) (initial saved) :=
 CachedCommandRun.step (model saved) (start saved) (CachedCommandRun.initial (model saved) (start saved)) (.command 0)
def finalCache (saved : Cursor old) := CachedCommandRun.run (model saved) (start saved) inputs

theorem the_emitted_commands_pass_the_independent_current_state_checker :
 checks point emitted (initial point) = true := by
 rw [point_is_the_original_checked_paid_successor]
 rw [← cached_checks_are_the_same_original_current_state_checker literalPoint emitted (initialCache literalPoint)]
 decide +kernel

theorem actual_is_the_original_execution_of_its_emitted_inputs :
 actual point = LocalCommandRun.run (model point) (start point) inputs := by
 unfold actual
 exact checked_inputs_generate_the_original_execution point (initial point) emitted
  the_emitted_commands_pass_the_independent_current_state_checker

theorem actual_rows_are_the_incrementally_generated_rows :
 StageTrace.records (start point) (actual point).stages = (finalCache point).rows := by
 rw [actual_is_the_original_execution_of_its_emitted_inputs]
 exact (finalCache point).rows_eq.symm

theorem actual_current_is_the_incrementally_generated_cursor :
 (actual point).current (model point) (start point) = (finalCache point).cursor := by
 rw [actual_is_the_original_execution_of_its_emitted_inputs]
 exact (finalCache point).cursor_eq.symm

theorem actual_seed_is_the_incrementally_generated_state :
 EventStep.seed ((actual point).current (model point) (start point)) = (finalCache point).before := by
 rw [actual_current_is_the_incrementally_generated_cursor]
 exact (finalCache point).before_eq.symm

theorem actual_observation_is_the_same_row_consumer (receiver : Fin (code point).sites) :
 observed point (actual point) receiver = CachedWorkDispatch.observed (vocabulary point) (law point) (finalCache point) receiver := by
 rw [actual_is_the_original_execution_of_its_emitted_inputs]
 exact (CachedWorkDispatch.observed_eq (vocabulary point) (law point) (finalCache point) receiver).symm

theorem actual_decision_is_the_same_row_consumer (receiver : Fin (code point).sites) :
 decideAt point (actual point) receiver = CachedWorkDispatch.produce (vocabulary point) (start point) (law point)
  (finalCache point).rows receiver (scope point) 2 := by
 change HeaderQuorum.produce _ _ _ _ _ _ _ = _
 rw [← CachedWorkDispatch.produce_eq,actual_rows_are_the_incrementally_generated_rows]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RenewedDispatchTrace
