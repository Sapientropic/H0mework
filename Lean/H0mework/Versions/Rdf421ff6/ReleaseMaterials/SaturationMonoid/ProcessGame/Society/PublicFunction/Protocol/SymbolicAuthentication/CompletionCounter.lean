import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CompletionExecution

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CompletionCounter

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open CompletionState CompletionTree CompletionExecution

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)
  (allowance : Nat)

-- This enumerates actual admitted branches of the generated route. It says
-- nothing about the impossibility of a different protocol or a larger budget.
def firstFailure {state : State model} : Tree model start vocabulary encoding law allowance state → Option (Result model)
  | .done _ => none
  | .halted reason => some ⟨state, .halted reason, []⟩
  | .node _ children => (CompletionEnvelope.choices start state.past allowance).attach.findSome? fun move =>
      (firstFailure (children move)).map fun result =>
        ⟨result.state, result.status, ⟨(current model start state).cut, move.val, move.val, true⟩ :: result.inputs⟩

theorem failure_is_absent_exactly_when_every_generated_branch_completes {state : State model}
    (tree : Tree model start vocabulary encoding law allowance state) :
    firstFailure model start vocabulary encoding law allowance tree = none ↔
      winning model start vocabulary encoding law allowance tree = true := by
  induction tree with
  | done => simp [firstFailure, winning]
  | halted => simp [firstFailure, winning]
  | @node state plan children ih =>
    simp only [firstFailure, List.findSome?_eq_none_iff, Option.map_eq_none_iff, winning, List.all_eq_true]
    exact ⟨fun missing move member => (ih move).mp (missing move member),
      fun accepted move member => (ih move).mpr (accepted move member)⟩

theorem every_failed_generated_tree_produces_a_concrete_counterexecution {state : State model}
    (tree : Tree model start vocabulary encoding law allowance state)
    (rejected : winning model start vocabulary encoding law allowance tree = false) :
    (firstFailure model start vocabulary encoding law allowance tree).isSome = true := by
  cases found : firstFailure model start vocabulary encoding law allowance tree with
  | some result => rfl
  | none =>
    have accepted := (failure_is_absent_exactly_when_every_generated_branch_completes model start vocabulary encoding law allowance tree).mp found
    rw [rejected] at accepted
    contradiction

theorem the_counterexecution_retains_a_real_halted_branch_and_obeys_the_envelope {state : State model}
    (tree : Tree model start vocabulary encoding law allowance state) (result : Result model)
    (found : firstFailure model start vocabulary encoding law allowance tree = some result) :
    state.past <+: result.state.past ∧ (∃ reason, result.status = .halted reason) ∧
      (result.inputs.all fun input => input.within) = true := by
  induction tree generalizing result with
  | done => contradiction
  | halted reason =>
    have same := Option.some.inj found
    cases same
    exact ⟨List.prefix_refl _, ⟨reason, rfl⟩, rfl⟩
  | @node state plan children ih =>
    obtain ⟨move, _, mapped⟩ := List.exists_of_findSome?_eq_some found
    cases prior : firstFailure model start vocabulary encoding law allowance (children move) with
    | none => simp only [prior, Option.map_none] at mapped; contradiction
    | some previous =>
      have next := ih move previous prior
      have same := Option.some.inj (by simpa only [prior, Option.map_some] using mapped)
      cases same
      exact ⟨(an_actual_edge_preserves_every_prior_stage model start vocabulary encoding law state plan move.val).trans next.1,
        next.2.1, by simpa only [List.all_cons, Bool.true_and] using next.2.2⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CompletionCounter
