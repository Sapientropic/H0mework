import Mathlib.CategoryTheory.Functor.OfSequence
import H0mework.Foundation.Source.AccountedUnfolding

/-!
# Root-generated cofinal diagram from one successor process

A domain supplies one seed state, one source-local successor constructor,
one object readout and one transition arrow for the current state.  The
framework iterates that process, preserves every generated state in a rooted
observation trace, and builds the resulting `ℕᵒᵖ` diagram.

No `Nat`-indexed completed object table, arrow table, cofinal schedule, limit,
same-component section or determinant enters the mouth.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CofinalProcessDiagram

open CategoryTheory

universe u v w

structure CofinalDiagramSuccessorProcessAt
    (C : Type u) [Category.{v} C] where
  State : Type w
  seed : State
  next : State → State
  object : State → C
  transition : ∀ state, object (next state) ⟶ object state

namespace CofinalDiagramSuccessorProcessAt

variable {C : Type u} [Category.{v} C]
variable (process : CofinalDiagramSuccessorProcessAt C)

def stateAt (stage : Nat) : process.State :=
  Nat.rec process.seed (fun _ current => process.next current) stage

def objectAt (stage : Nat) : C :=
  process.object (process.stateAt stage)

def transitionAt (stage : Nat) :
    objectAt (process := process) (stage + 1) ⟶
      objectAt (process := process) stage :=
  process.transition (process.stateAt stage)

def diagram : ℕᵒᵖ ⥤ C :=
  Functor.ofOpSequence (transitionAt (process := process))

def seedOccurrence : RootedAccountedUnfolding process.State :=
  RootedAccountedUnfolding.zero process.seed

def continuation (state : process.State) :
    RootedAccountedUnfolding process.State :=
  RootedAccountedUnfolding.zero (process.next state)

def observation (stage : Nat) : RootedAccountedUnfolding process.State :=
  Nat.rec process.seedOccurrence
    (fun _ current => current.advance process.continuation) stage

@[simp] theorem observation_zero :
    process.observation 0 = process.seedOccurrence :=
  rfl

@[simp] theorem observation_succ (stage : Nat) :
    process.observation (stage + 1) =
      (process.observation stage).advance process.continuation :=
  rfl

theorem observation_frontier (stage : Nat) :
    (process.observation stage).frontier = [process.stateAt stage] := by
  induction stage with
  | zero => rfl
  | succ stage inductionHypothesis =>
      rw [process.observation_succ,
        RootedAccountedUnfolding.frontier_advance,
        inductionHypothesis]
      change [process.next (process.stateAt stage)] =
        [process.stateAt (stage + 1)]
      rfl

private theorem frontier_mem_trace
    {State : Type*} (occurrence : RootedAccountedUnfolding State) :
    ∀ state, state ∈ occurrence.frontier → state ∈ occurrence.trace :=
  RootedAccountedUnfolding.rec
    (motive_1 := fun current =>
      ∀ state, state ∈ current.frontier → state ∈ current.trace)
    (motive_2 := fun branches =>
      ∀ state,
        state ∈ RootedAccountedUnfolding.frontierBranches branches →
          state ∈ RootedAccountedUnfolding.traceBranches branches)
    (fun root branches branchResult state state_mem => by
      cases branches with
      | nil => exact state_mem
      | cons head tail =>
          exact List.mem_cons_of_mem root (branchResult state state_mem))
    (fun state state_mem => by
      change state ∈ ([] : List State) at state_mem
      exact False.elim (List.not_mem_nil state_mem))
    (fun head tail headResult tailResult state state_mem => by
      change state ∈ head.frontier ++
        RootedAccountedUnfolding.frontierBranches tail at state_mem
      change state ∈ head.trace ++
        RootedAccountedUnfolding.traceBranches tail
      rw [List.mem_append] at state_mem ⊢
      cases state_mem with
      | inl inHead => exact Or.inl (headResult state inHead)
      | inr inTail => exact Or.inr (tailResult state inTail))
    occurrence

theorem stateAt_mem_observation_trace (stage : Nat) :
    process.stateAt stage ∈ (process.observation stage).trace := by
  apply frontier_mem_trace
  rw [process.observation_frontier]
  simp

end CofinalDiagramSuccessorProcessAt

structure RootGeneratedCofinalProcessDiagramAt
    {C : Type u} [Category.{v} C]
    {Root : Type w}
    (rootOccurrence : RootedAccountedUnfolding Root)
    (dependentProcessOccurrence : RootedAccountedUnfolding
      (Root × CofinalDiagramSuccessorProcessAt C))
    (projects : dependentProcessOccurrence.map Prod.fst = rootOccurrence) :
    Type (max u v w) where
  private mk ::

namespace RootGeneratedCofinalProcessDiagramAt

variable {C : Type u} [Category.{v} C]
variable {Root : Type w}
variable {rootOccurrence : RootedAccountedUnfolding Root}
variable {dependentProcessOccurrence : RootedAccountedUnfolding
  (Root × CofinalDiagramSuccessorProcessAt C)}
variable {projects : dependentProcessOccurrence.map Prod.fst = rootOccurrence}

def generate : RootGeneratedCofinalProcessDiagramAt
    rootOccurrence dependentProcessOccurrence projects :=
  ⟨⟩

def root
    (_face : RootGeneratedCofinalProcessDiagramAt
      rootOccurrence dependentProcessOccurrence projects) :=
  dependentProcessOccurrence.map Prod.fst

def actualProcess
    (_face : RootGeneratedCofinalProcessDiagramAt
      rootOccurrence dependentProcessOccurrence projects) :=
  dependentProcessOccurrence.root.2

def stateAt
    (face : RootGeneratedCofinalProcessDiagramAt
      rootOccurrence dependentProcessOccurrence projects) :=
  face.actualProcess.stateAt

def observation
    (face : RootGeneratedCofinalProcessDiagramAt
      rootOccurrence dependentProcessOccurrence projects) :=
  face.actualProcess.observation

def actualDiagram
    (face : RootGeneratedCofinalProcessDiagramAt
      rootOccurrence dependentProcessOccurrence projects) : ℕᵒᵖ ⥤ C :=
  CofinalDiagramSuccessorProcessAt.diagram (process := face.actualProcess)

def dependentDiagramOccurrence
    (_face : RootGeneratedCofinalProcessDiagramAt
      rootOccurrence dependentProcessOccurrence projects) :
    RootedAccountedUnfolding (Root × (ℕᵒᵖ ⥤ C)) :=
  dependentProcessOccurrence.map fun payload =>
    (payload.1,
      CofinalDiagramSuccessorProcessAt.diagram (process := payload.2))

theorem dependentDiagramOccurrence_projects
    (face : RootGeneratedCofinalProcessDiagramAt
      rootOccurrence dependentProcessOccurrence projects) :
    face.dependentDiagramOccurrence.map Prod.fst = rootOccurrence := by
  unfold dependentDiagramOccurrence
  rw [RootedAccountedUnfolding.map_map]
  change dependentProcessOccurrence.map Prod.fst = rootOccurrence
  exact projects

theorem stateAt_mem_observation_trace
    (face : RootGeneratedCofinalProcessDiagramAt
      rootOccurrence dependentProcessOccurrence projects)
    (stage : Nat) :
    face.stateAt stage ∈ (face.observation stage).trace :=
  face.actualProcess.stateAt_mem_observation_trace stage

theorem actualDiagram_obj (face : RootGeneratedCofinalProcessDiagramAt
    rootOccurrence dependentProcessOccurrence projects) (stage : Nat) :
    face.actualDiagram.obj (Opposite.op stage) =
      face.actualProcess.objectAt stage :=
  rfl

theorem actualDiagram_succ (face : RootGeneratedCofinalProcessDiagramAt
    rootOccurrence dependentProcessOccurrence projects) (stage : Nat) :
    face.actualDiagram.map
        (homOfLE (Nat.le_add_right stage 1)).op =
      face.actualProcess.transitionAt stage :=
  Functor.ofOpSequence_map_homOfLE_succ
    (CofinalDiagramSuccessorProcessAt.transitionAt
      (process := face.actualProcess)) stage

theorem preserves_root_process_and_generated_diagram
    (face : RootGeneratedCofinalProcessDiagramAt
      rootOccurrence dependentProcessOccurrence projects) :
    face.root = rootOccurrence ∧
      face.actualProcess = dependentProcessOccurrence.root.2 ∧
      face.actualDiagram =
        CofinalDiagramSuccessorProcessAt.diagram
          (process := dependentProcessOccurrence.root.2) :=
  ⟨projects, rfl, rfl⟩

end RootGeneratedCofinalProcessDiagramAt

end CofinalProcessDiagram
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
