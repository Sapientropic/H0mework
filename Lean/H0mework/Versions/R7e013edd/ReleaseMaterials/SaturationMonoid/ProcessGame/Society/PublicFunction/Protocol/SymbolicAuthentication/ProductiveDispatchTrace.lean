import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CachedWorkDispatch
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProductiveDispatchSource

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 80000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProductiveDispatchTrace
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open ProductiveDispatchSource

theorem the_original_native_service_endpoint_funds_twenty_three_invocations :
    (EventStep.seed (initial.current model start)).remaining = 23 :=
  ProductiveHeaderChecks.the_same_saved_endpoint_has_the_original_material_debt_and_fuel.2.2.2.2.2

def emitted : List LocalCommandSource.Input := [.idle,.command 0,.idle,.idle,.idle,.command 1,.idle,.command 2,.idle,
      .event 3,.event 6,.command 3,.idle,.event 5,.event 7,.event 2,.event 8,.idle,.idle,.event 4,.event 9]

-- The checker consumes literal attempted inputs; it does not read a producer verdict.
def checks : List LocalCommandSource.Input → State → Bool :=
  List.rec (fun _ => true) (fun input _ verify state =>
    decide (choose state = input) && verify (LocalCommandRun.step model start state input))

theorem checked_inputs_generate_the_same_actual_execution
    (state : State) (inputs : List LocalCommandSource.Input) (checked : checks inputs state = true) :
    (journey state inputs.length).1 = inputs.foldl (LocalCommandRun.step model start) state := by
  induction inputs generalizing state with
  | nil => rfl
  | cons input tail ih =>
    have both : decide (choose state = input) = true ∧ checks tail (LocalCommandRun.step model start state input) = true :=
      by simpa only [checks,Bool.and_eq_true] using checked
    have first := of_decide_eq_true both.1
    have rest := ih (LocalCommandRun.step model start state input) both.2
    have resumed := resuming_the_actual_state_is_the_same_generated_execution state 1 tail.length
    change (journey state (tail.length+1)).1 = _
    rw [Nat.add_comm tail.length 1]
    rw [resumed]
    change (journey (LocalCommandRun.step model start state (choose state)) tail.length).1 = _
    rw [first]
    exact rest

theorem the_emitted_inputs_pass_the_independent_state_by_state_checker : checks emitted initial = true := by
  have sameChoice (state : State) : WorkDispatch.choose model start vocabulary law work state = choose state := by
    have sameWork : WorkDispatch.nextWork model start work state = nextWork state := rfl
    have sameTest (expected : Option ProductiveMandateSource.Action) :
        WorkDispatch.workingFor model start state expected = workingFor state expected := by
      funext input
      cases input <;> cases expected <;> rfl
    simp only [WorkDispatch.choose, ProductiveDispatchSource.choose, sameWork, sameTest]
  let cachedChecks (inputs : List LocalCommandSource.Input) :
      {state : State} → CachedCommandRun.Cache model start state → Bool :=
    inputs.rec (motive := fun _ => {state : State} → CachedCommandRun.Cache model start state → Bool)
      (fun {_} _ => true) (fun input _ verify {_} cache =>
        decide (CachedWorkDispatch.choose vocabulary law work cache = input) &&
          verify (CachedCommandRun.step model start cache input))
  have cached_eq (inputs : List LocalCommandSource.Input) {state : State}
      (cache : CachedCommandRun.Cache model start state) : cachedChecks inputs cache = checks inputs state := by
    induction inputs generalizing state with
    | nil => rfl
    | cons input tail ih =>
      change (decide (CachedWorkDispatch.choose vocabulary law work cache = input) &&
          cachedChecks tail (CachedCommandRun.step model start cache input)) =
        (decide (choose state = input) && checks tail (LocalCommandRun.step model start state input))
      have choice : CachedWorkDispatch.choose vocabulary law work cache = choose state :=
        (CachedWorkDispatch.choose_eq vocabulary law work cache).trans (sameChoice state)
      exact congrArg₂ (fun selected rest => decide (selected = input) && rest) choice
        (ih (CachedCommandRun.step model start cache input))
  have accepted : cachedChecks emitted (CachedCommandRun.initial model start) = true := by
    dsimp only [cachedChecks]
    decide +kernel
  exact (cached_eq emitted (CachedCommandRun.initial model start)).symm.trans accepted

theorem actual_is_the_original_execution_of_its_emitted_inputs :
    actual = LocalCommandRun.run model start emitted := by
  unfold actual
  exact checked_inputs_generate_the_same_actual_execution initial emitted
    the_emitted_inputs_pass_the_independent_state_by_state_checker

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProductiveDispatchTrace
