import Mathlib.Data.Fintype.Card

/-!
# Source-generated finite effective branching reachability

A deterministic spine can miss lawful alternatives.  This kernel explores
the exact Type-valued step relation of a finite source carrier and returns
one of two data-bearing outcomes:

* an actual generated path ending in terminal material; or
* the complete reachable state set, with a path to every member, no terminal
  in the set, and closure under every source-generated step.

The negative branch is therefore a finite rooted obstruction, not an empty
token or a caller-supplied residual-zero premise.  Step types need not be
finite: finiteness of the state carrier is enough to materialize the complete
reachable image.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedFiniteEffectiveBranchingReachability

universe u

/-- A source law may have many lawful outgoing steps.  `classify` guarantees
that every state exposes terminal data or at least one generated step, while
reachability below quantifies over all steps. -/
structure Law (State : Type u) where
  TerminalAt : State → Type u
  StepAt : State → Type u
  target : {state : State} → StepAt state → State
  classify : (state : State) → TerminalAt state ⊕ StepAt state

/-- Chronological source-generated path.  Every edge retains its dependent
step data; no relation-level truncation loses factor/effectivity witnesses. -/
inductive GeneratedPathAt {State : Type u} (law : Law State)
    (start : State) : State → Type u
  | nil : GeneratedPathAt law start start
  | snoc {state : State} (prior : GeneratedPathAt law start state)
      (step : law.StepAt state) : GeneratedPathAt law start (law.target step)

variable {State : Type u} [Fintype State]

/-- Exact finite image of all states admitting an actual generated path from
`start`. -/
noncomputable def reachableSet (law : Law State) (start : State) :
    Finset State := by
  classical
  exact Finset.univ.filter fun state =>
    Nonempty (GeneratedPathAt law start state)

theorem mem_reachableSet_iff (law : Law State) (start state : State) :
    state ∈ reachableSet law start ↔
      Nonempty (GeneratedPathAt law start state) := by
  classical
  simp [reachableSet]

theorem start_mem_reachableSet (law : Law State) (start : State) :
    start ∈ reachableSet law start := by
  rw [mem_reachableSet_iff]
  exact ⟨.nil⟩

theorem target_mem_reachableSet (law : Law State) (start state : State)
    (stateMem : state ∈ reachableSet law start)
    (step : law.StepAt state) :
    law.target step ∈ reachableSet law start := by
  rw [mem_reachableSet_iff] at stateMem ⊢
  exact ⟨(Classical.choice stateMem).snoc step⟩

/-- Positive reachability retains the endpoint, the complete generated path,
and terminal material at that exact endpoint. -/
structure TerminalReachabilityAt (law : Law State) (start : State) : Type u where
  state : State
  path : GeneratedPathAt law start state
  terminal : law.TerminalAt state

/-- Complete negative image.  The state set is definitionally fixed to the
actual reachable set; callers cannot submit a smaller closed component. -/
structure ClosedReachabilityResidualAt
    (law : Law State) (start : State) : Type u where
  private mk ::
  states : Finset State
  states_eq : states = reachableSet law start
  startMem : start ∈ states
  pathAt : ∀ state, state ∈ states → GeneratedPathAt law start state
  terminalEmpty : ∀ state, state ∈ states →
    ¬ Nonempty (law.TerminalAt state)
  stepClosed : ∀ state, state ∈ states → (step : law.StepAt state) →
    law.target step ∈ states

namespace ClosedReachabilityResidualAt

variable {law : Law State} {start : State}

/-- Safe re-rooting mouth for an independently generated exact reachable
carrier.  The private constructor remains sealed; callers must pay the full
`states = reachableSet` equality together with paths, terminal exclusion and
all-channel closure. -/
def ofExactReachable
    (states : Finset State)
    (states_eq : states = reachableSet law start)
    (startMem : start ∈ states)
    (pathAt : ∀ state, state ∈ states → GeneratedPathAt law start state)
    (terminalEmpty : ∀ state, state ∈ states →
      ¬ Nonempty (law.TerminalAt state))
    (stepClosed : ∀ state, state ∈ states → (step : law.StepAt state) →
      law.target step ∈ states) :
    ClosedReachabilityResidualAt law start :=
  ⟨states, states_eq, startMem, pathAt, terminalEmpty, stepClosed⟩

/-- A negative reachable state is never a dead placeholder: the source
classifier must supply an actual outgoing step. -/
def generatedStepAt (residual : ClosedReachabilityResidualAt law start)
    (state : State) (stateMem : state ∈ residual.states) :
    law.StepAt state := by
  cases law.classify state with
  | inl terminal =>
      exact (residual.terminalEmpty state stateMem ⟨terminal⟩).elim
  | inr step => exact step

theorem generatedTargetMem (residual : ClosedReachabilityResidualAt law start)
    (state : State) (stateMem : state ∈ residual.states) :
    law.target (residual.generatedStepAt state stateMem) ∈ residual.states :=
  residual.stepClosed state stateMem _

end ClosedReachabilityResidualAt

abbrev DispositionAt (law : Law State) (start : State) : Type u :=
  TerminalReachabilityAt law start ⊕ ClosedReachabilityResidualAt law start

/-- Total finite branching reachability.  The positive branch is selected
only from an actual path/terminal pair.  Otherwise the framework generates
the complete reachable image and proves closure under every lawful step. -/
noncomputable def settle (law : Law State) (start : State) :
    DispositionAt law start := by
  let terminalExists : Prop :=
    ∃ state, Nonempty (GeneratedPathAt law start state) ∧
      Nonempty (law.TerminalAt state)
  by_cases hasTerminal : terminalExists
  · have terminalNonempty : Nonempty (TerminalReachabilityAt law start) := by
      rcases hasTerminal with ⟨state, path, terminal⟩
      exact ⟨⟨state, Classical.choice path, Classical.choice terminal⟩⟩
    exact .inl (Classical.choice terminalNonempty)
  · exact .inr
      { states := reachableSet law start
        states_eq := rfl
        startMem := start_mem_reachableSet law start
        pathAt := by
          intro state stateMem
          exact Classical.choice ((mem_reachableSet_iff law start state).mp stateMem)
        terminalEmpty := by
          intro state stateMem terminal
          exact hasTerminal
            ⟨state, (mem_reachableSet_iff law start state).mp stateMem, terminal⟩
        stepClosed := by
          intro state stateMem step
          exact target_mem_reachableSet law start state stateMem step }

end SourceGeneratedFiniteEffectiveBranchingReachability
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
