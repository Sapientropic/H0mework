import H0mework.Realization.Operations.FiniteKernel
import H0mework.Probability.EmpiricalRecovery.Model

/-! The finite source recurrence makes actual raw-window fibres equal to the old complete next-atom fibres. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionObservationHistory.FiniteRecurrence.Native

open SourceGeneratedRuntimeHistoryProbability SourceConditionalTransfer

noncomputable section

universe u

variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}
variable {B : Type u} [AddCommGroup B] (read : process.State → B)

def rawWindow (windowBound : Nat) (runtime : LivingRuntimeState process) : Fin (windowBound + 1) → B :=
  fun index => read (runtime.advance index.val).state

theorem rawWindow_source (windowBound : Nat) (runtime : LivingRuntimeState process) :
    rawWindow read windowBound runtime =
      prefixEvaluator (SourceOperationNative.sourceAction process) (SourceOperationNative.observer process read)
        windowBound (SourceOperationNative.point runtime) := by
  funext index
  change read (runtime.advance index.val).state =
    SourceOperationNative.observer process read
      ((SourceOperationNative.sourceAction process ^ index.val) (SourceOperationNative.point runtime))
  rw [SourceOperationNative.Observed.sourceAction_pow_point, SourceOperationNative.observer_point]

def query (windowBound : Nat) (runtime : LivingRuntimeState process) (actorBound : Nat)
    (index : Fin (actorBound + 1)) : Fin (windowBound + 1) → B :=
  rawWindow read windowBound ((history runtime actorBound).stageAt index).next

variable (windowBound : Nat) (coefficients : Fin (windowBound + 1) → ℤ)
variable (sourceLaw : (SourceOperationNative.observer process read).comp
    (SourceOperationNative.sourceAction process ^ (windowBound + 1)) =
      ∑ index : Fin (windowBound + 1), coefficients index •
        stageEvaluator (SourceOperationNative.sourceAction process) (SourceOperationNative.observer process read) index.val)

include sourceLaw

theorem rawWindow_fibre_model (left right : LivingRuntimeState process) :
    rawWindow read windowBound left = rawWindow read windowBound right ↔
      SourceOperationNative.Observed.modelPoint (process := process) read left =
        SourceOperationNative.Observed.modelPoint (process := process) read right := by
  rw [rawWindow_source, rawWindow_source]
  exact prefix_fibre_iff_model (SourceOperationNative.sourceAction process) (SourceOperationNative.observer process read)
    windowBound coefficients sourceLaw (SourceOperationNative.point left) (SourceOperationNative.point right)

theorem nextAtom_fibre_iff (runtime : LivingRuntimeState process) (actorBound : Nat)
    (left right : Fin (actorBound + 1)) :
    nextAtom read runtime actorBound left = nextAtom read runtime actorBound right ↔
      query read windowBound runtime actorBound left = query read windowBound runtime actorBound right :=
  (SourceConditionalRecovery.nextAtom_model_iff read runtime actorBound left right).trans
    (rawWindow_fibre_model read windowBound coefficients sourceLaw
      ((history runtime actorBound).stageAt left).next ((history runtime actorBound).stageAt right).next).symm

end
end SourceGeneratedActionObservationHistory.FiniteRecurrence.Native
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
