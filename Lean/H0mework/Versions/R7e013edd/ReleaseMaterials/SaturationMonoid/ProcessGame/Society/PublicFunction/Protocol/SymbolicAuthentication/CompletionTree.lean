import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CompletionState

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CompletionTree

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open CompletionState

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

abbrev Choices (state : State model) :=
  {move : Move model.source.code // move ∈ CompletionEnvelope.choices start state.past allowance}

inductive Tree : State model → Type where
  | done {state} (complete : Goal model start vocabulary encoding law state) : Tree state
  | halted {state} (reason : Halt) : Tree state
  | node {state} (plan : Plan model start vocabulary encoding law state)
      (children : ∀ move : Choices model start allowance state,
        Tree (after model start vocabulary encoding law state plan move.val)) : Tree state

def build : Nat → (state : State model) → Tree model start vocabulary encoding law allowance state
  | 0, state => if complete : Goal model start vocabulary encoding law state then .done complete
      else if fuel model start state = 0 then .halted .exhausted else .halted .observationCut
  | rounds + 1, state =>
    if complete : Goal model start vocabulary encoding law state then .done complete
    else if fuel model start state = 0 then .halted .exhausted
    else match prepare model start vocabulary encoding law state with
      | .halted reason => .halted reason
      | .ready plan => .node plan fun move => build rounds (after model start vocabulary encoding law state plan move.val)

def winning {state : State model} : Tree model start vocabulary encoding law allowance state → Bool
  | .done _ => true
  | .halted _ => false
  | .node _ children => (CompletionEnvelope.choices start state.past allowance).attach.all fun move => winning (children move)

def height {state : State model} : Tree model start vocabulary encoding law allowance state → Nat
  | .done _ | .halted _ => 0
  | .node _ children => 1 + ((CompletionEnvelope.choices start state.past allowance).attach.map fun move => height (children move)).foldl max 0

def initial (past : BatchReentry.Stages model) : State model := ⟨past, [], []⟩
def produce (past : BatchReentry.Stages model) :=
  build model start vocabulary encoding law allowance (BatchReentry.fuel model start past) (initial model past)

theorem every_branch_of_a_generated_winning_node_is_winning
    {state : State model} (plan : Plan model start vocabulary encoding law state)
    (children : ∀ move : Choices model start allowance state,
      Tree model start vocabulary encoding law allowance (after model start vocabulary encoding law state plan move.val))
    (accepted : winning model start vocabulary encoding law allowance (.node plan children) = true)
    (move : Choices model start allowance state) :
    winning model start vocabulary encoding law allowance (children move) = true :=
  List.all_eq_true.mp accepted move (List.mem_attach _ _)

theorem a_winning_node_has_an_actual_nonempty_communication_domain
    {state : State model} (_tree : Tree model start vocabulary encoding law allowance state) :
    CompletionEnvelope.choices start state.past allowance ≠ [] :=
  CompletionEnvelope.the_generated_communication_domain_is_nonempty start state.past allowance

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CompletionTree
