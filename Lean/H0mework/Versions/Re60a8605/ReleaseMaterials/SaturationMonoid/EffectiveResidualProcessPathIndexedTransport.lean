import H0mework.Realization.Residual.PathTransport

/-!
# Effective residual processes as native path transports

`EffectiveResidualProcess` already owns one actual state update, one linear
keep, and the law `residual (update state) = keep (residual state)`.  This
module installs that existing update in the common typed-path framework.

The wrapper vertex records which process owns a state, so distinct processes
on the same state type do not compete for a global `Quiver` instance.  Its
only arrow is the constructor-owned actual update.  No admissibility,
faithfulness, trace, terminal, or obstruction field is added.

The canonical typed update path is proved to have exactly the old Nat-indexed
endpoint, trace, and write-back.  Thus existing domain producers can enter the
path cocycle/morphism network without changing their update semantics.
-/

noncomputable section

namespace SaturationMonoid
namespace ResidualProjection

universe uK uE uS

namespace EffectiveResidualProcess

/-- A state tagged by the actual effective process that owns its update.
This is transport typing, not a second state or semantic certificate. -/
@[ext]
structure UpdateVertex
    {K : Type uK} {E : Type uE} {State : Type uS}
    [Field K] [AddCommGroup E] [Module K E]
    (_P : EffectiveResidualProcess K E State) where
  state : State

/-- Insert an existing process state into its process-owned vertex type. -/
def vertex
    {K : Type uK} {E : Type uE} {State : Type uS}
    [Field K] [AddCommGroup E] [Module K E]
    (P : EffectiveResidualProcess K E State)
    (state : State) : P.UpdateVertex :=
  ⟨state⟩

@[simp] theorem vertex_state
    {K : Type uK} {E : Type uE} {State : Type uS}
    [Field K] [AddCommGroup E] [Module K E]
    (P : EffectiveResidualProcess K E State)
    (state : State) :
    (P.vertex state).state = state := by
  rfl

/-- The sole native arrow is the process's existing actual update. -/
inductive UpdateEdge
    {K : Type uK} {E : Type uE} {State : Type uS}
    [Field K] [AddCommGroup E] [Module K E]
    (P : EffectiveResidualProcess K E State)
    (source : P.UpdateVertex) : P.UpdateVertex → Type
  | step : P.UpdateEdge source (P.vertex (P.update source.state))

/-- Named update quiver.  The process term occurs in the vertex type, so the
instance is unambiguous even when the raw state type supports many processes. -/
@[reducible] def updateQuiver
    {K : Type uK} {E : Type uE} {State : Type uS}
    [Field K] [AddCommGroup E] [Module K E]
    (P : EffectiveResidualProcess K E State) :
    Quiver P.UpdateVertex where
  Hom := P.UpdateEdge

instance updateVertexQuiver
    {K : Type uK} {E : Type uE} {State : Type uS}
    [Field K] [AddCommGroup E] [Module K E]
    (P : EffectiveResidualProcess K E State) :
    Quiver P.UpdateVertex :=
  P.updateQuiver

namespace UpdateEdge

/-- The typed arrow target is the native update of its source state. -/
theorem target_state_eq
    {K : Type uK} {E : Type uE} {State : Type uS}
    [Field K] [AddCommGroup E] [Module K E]
    {P : EffectiveResidualProcess K E State}
    {source target : P.UpdateVertex}
    (edge : source ⟶ target) :
    target.state = P.update source.state := by
  change P.UpdateEdge source target at edge
  cases edge
  rfl

/-- Retain one actual process update as a one-edge typed path. -/
def toPath
    {K : Type uK} {E : Type uE} {State : Type uS}
    [Field K] [AddCommGroup E] [Module K E]
    {P : EffectiveResidualProcess K E State}
    {source target : P.UpdateVertex}
    (edge : source ⟶ target) :
    Quiver.Path source target :=
  .cons .nil edge

end UpdateEdge

/-- The existing effective process, unchanged, as a native path-indexed
residual transport. -/
def toPathIndexedResidualTransport
    {K : Type uK} {E : Type uE} {State : Type uS}
    [Field K] [AddCommGroup E] [Module K E]
    (P : EffectiveResidualProcess K E State) :
    PathIndexedResidualTransport K E P.UpdateVertex where
  residual := fun vertex => P.residual vertex.state
  edgeKeep := fun _ => P.keep
  edge_residual_transport := by
    intro source target edge
    change P.UpdateEdge source target at edge
    cases edge
    exact P.residual_transport_law source.state

/-- One constructor-owned update edge at an actual process state. -/
def updateEdge
    {K : Type uK} {E : Type uE} {State : Type uS}
    [Field K] [AddCommGroup E] [Module K E]
    (P : EffectiveResidualProcess K E State)
    (state : State) :
    P.vertex state ⟶ P.vertex (P.update state) :=
  .step

/-- Canonical typed path of repeated actual updates. -/
def updatePath
    {K : Type uK} {E : Type uE} {State : Type uS}
    [Field K] [AddCommGroup E] [Module K E]
    (P : EffectiveResidualProcess K E State)
    (source : State) :
    (steps : Nat) →
      Quiver.Path (P.vertex source) (P.vertex (P.pathState source steps))
  | 0 => .nil
  | steps + 1 =>
      .cons (P.updatePath source steps)
        (P.updateEdge (P.pathState source steps))

@[simp] theorem updatePath_zero
    {K : Type uK} {E : Type uE} {State : Type uS}
    [Field K] [AddCommGroup E] [Module K E]
    (P : EffectiveResidualProcess K E State)
    (source : State) :
    P.updatePath source 0 = .nil := by
  rfl

@[simp] theorem updatePath_succ
    {K : Type uK} {E : Type uE} {State : Type uS}
    [Field K] [AddCommGroup E] [Module K E]
    (P : EffectiveResidualProcess K E State)
    (source : State) (steps : Nat) :
    P.updatePath source (steps + 1) =
      .cons (P.updatePath source steps)
        (P.updateEdge (P.pathState source steps)) := by
  rfl

@[simp] theorem updatePath_length
    {K : Type uK} {E : Type uE} {State : Type uS}
    [Field K] [AddCommGroup E] [Module K E]
    (P : EffectiveResidualProcess K E State)
    (source : State) (steps : Nat) :
    (P.updatePath source steps).length = steps := by
  induction steps with
  | zero =>
      rfl
  | succ steps inductionHypothesis =>
      change (P.updatePath source steps).length + 1 = steps + 1
      exact congrArg (fun length => length + 1) inductionHypothesis

/-- Gate 1 is exactly the original process update law at the corresponding
typed edge. -/
theorem pathIndexedResidualTransport_actual_update
    {K : Type uK} {E : Type uE} {State : Type uS}
    [Field K] [AddCommGroup E] [Module K E]
    (P : EffectiveResidualProcess K E State)
    (state : State) :
    P.toPathIndexedResidualTransport.residual
          (P.vertex (P.update state)) =
      P.toPathIndexedResidualTransport.edgeKeep
        (P.updateEdge state)
        (P.toPathIndexedResidualTransport.residual (P.vertex state)) := by
  exact P.residual_transport_law state

/-- The common typed-path trace is definitionally the old Nat-indexed
endpoint complement. -/
theorem updatePath_pathTrace_eq
    {K : Type uK} {E : Type uE} {State : Type uS}
    [Field K] [AddCommGroup E] [Module K E]
    (P : EffectiveResidualProcess K E State)
    (source : State) (steps : Nat) :
    P.toPathIndexedResidualTransport.pathTrace
        (P.updatePath source steps) =
      P.pathTrace source steps := by
  rw [P.toPathIndexedResidualTransport.pathTrace_eq_source_sub_target]
  rfl

/-- The common typed-path write-back is exactly the existing effective
process write-back, component by component. -/
theorem updatePath_pathWriteBack_eq
    {K : Type uK} {E : Type uE} {State : Type uS}
    [Field K] [AddCommGroup E] [Module K E]
    (P : EffectiveResidualProcess K E State)
    (source : State) (steps : Nat) :
    P.toPathIndexedResidualTransport.pathWriteBack
        (P.updatePath source steps) =
      P.pathWriteBackState source steps := by
  apply Prod.ext
  · rfl
  · exact P.updatePath_pathTrace_eq source steps

end EffectiveResidualProcess

end ResidualProjection
end SaturationMonoid
