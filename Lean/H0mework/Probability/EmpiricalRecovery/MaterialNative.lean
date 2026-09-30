import H0mework.Realization.ObservationActions.MaterialHistory
import H0mework.Probability.EmpiricalRecovery.FiniteNative

/-! A same-runtime material update transports its finite field-valued recurrence to the original native model fibres. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionObservationHistory.MaterialRecurrence.Native

open SourceGeneratedRuntimeHistoryProbability SourceConditionalTransfer

noncomputable section

universe r u

variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}

private theorem advance_add (runtime : LivingRuntimeState process) (first second : Nat) :
    (runtime.advance first).advance second = runtime.advance (first + second) := by
  induction second with
  | zero => rfl
  | succ second previous => exact congrArg (fun current : LivingRuntimeState process => current.tick.next) previous

theorem rawWindow_cell {B : Type u} (read : process.State → B) (runtime : LivingRuntimeState process)
    (windowBound first : Nat) (index : Fin (windowBound + 1)) :
    FiniteRecurrence.Native.rawWindow read windowBound (runtime.advance first) index =
      read (runtime.advance (first + index.val)).state :=
  congrArg (fun current : LivingRuntimeState process => read current.state) (advance_add runtime first index.val)

theorem query_cell {B : Type u} (read : process.State → B) (runtime : LivingRuntimeState process)
    (windowBound actorBound : Nat) (actor : Fin (actorBound + 1)) (offset : Fin (windowBound + 1)) :
    FiniteRecurrence.Native.query read windowBound runtime actorBound actor offset =
      read (runtime.advance (actor.val + offset.val)).tick.next.state :=
  (rawWindow_cell read runtime windowBound (actor.val + 1) offset).trans
    (congrArg (fun stage => read (runtime.advance stage).state)
      (by omega : actor.val + 1 + offset.val = actor.val + offset.val + 1))

variable {R : Type r} [CommRing R] [Nontrivial R]
variable {C B : Type u} [AddCommGroup C] [Module R C] [Module.Free R C] [Module.Finite R C]
variable [AddCommGroup B] [Module R B]
variable (action : C →ₗ[R] C) (observation : C →ₗ[R] B) (material : Nat → C)
variable (generated : ∀ stage : Nat, material (stage + 1) = action (material stage))
variable (read : process.State → B) (runtime : LivingRuntimeState process)
variable (read_source : ∀ stage : Nat, read (runtime.advance stage).state = observation (material stage))

include read_source

omit [Nontrivial R] in
theorem rawWindow_at (first : Nat) :
    FiniteRecurrence.Native.rawWindow read (bound action) (runtime.advance first) =
      windowAt action observation material first := by
  funext offset
  change read ((runtime.advance first).advance offset.val).state = observation (material (first + offset.val))
  rw [advance_add]
  exact read_source _

include generated

theorem window_fibre_native_model (left right : Nat) :
    FiniteRecurrence.Native.rawWindow read (bound action) (runtime.advance left) =
        FiniteRecurrence.Native.rawWindow read (bound action) (runtime.advance right) ↔
      SourceOperationNative.Observed.modelPoint (process := process) read (runtime.advance left) =
        SourceOperationNative.Observed.modelPoint (process := process) read (runtime.advance right) := by
  rw [rawWindow_at action observation material read runtime read_source,
    rawWindow_at action observation material read runtime read_source,
    window_fibre_iff_future action observation material generated,
    SourceOperationNative.Observed.model_native_fibre_iff]
  simp only [advance_add, read_source]

theorem query_fibre_iff (actorBound : Nat) (left right : Fin (actorBound + 1)) :
    nextAtom read runtime actorBound left = nextAtom read runtime actorBound right ↔
      FiniteRecurrence.Native.query read (bound action) runtime actorBound left =
        FiniteRecurrence.Native.query read (bound action) runtime actorBound right :=
  (SourceConditionalRecovery.nextAtom_model_iff read runtime actorBound left right).trans
    (window_fibre_native_model action observation material generated read runtime read_source (left.val + 1) (right.val + 1)).symm

end
end SourceGeneratedActionObservationHistory.MaterialRecurrence.Native
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
