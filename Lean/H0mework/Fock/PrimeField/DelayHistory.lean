import H0mework.Fock.PrimeField.DelayActual

/-! A finite query of the complete original actor history reads one constant field throughout the generated gap. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeObservationDelay

open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
open SourcePrimeHistoryRecovery
open SourceGeneratedActionObservationHistory SourceGeneratedRuntimeHistoryProbability

noncomputable section

def startRuntime (owner : GlobalParentOwner) (bound width : Nat) : LivingRuntimeState process :=
  runtimeAt (firstState owner (bound + width))

abbrev shortQuery (owner : GlobalParentOwner) (bound width : Nat) :=
  FiniteRecurrence.Native.query (process := process) rawField width (startRuntime owner bound width) bound

theorem native_state_advance (runtime : LivingRuntimeState process) (steps : Nat) :
    (runtime.advance steps).state = runtime.state + steps :=
  (SourceOwnedObservationHistory.Runtime.advance_state runtime steps).trans (Nat.succ_iterate runtime.state steps)

theorem sample_state (owner : GlobalParentOwner) (bound width : Nat) (actor : Fin (bound + 1)) :
    sample (startRuntime owner bound width) bound actor = firstState owner (bound + width) + actor.val := by
  change ((startRuntime owner bound width).advance actor.val).state = _
  rw [native_state_advance]
  exact congrArg (· + actor.val) (runtimeAt_state _)

theorem query_value (owner : GlobalParentOwner) (bound width : Nat) (actor : Fin (bound + 1)) (time : Fin (width + 1)) :
    shortQuery owner bound width actor time = rawField (firstState owner (bound + width) + actor.val + time.val + 1) := by
  change rawField (((startRuntime owner bound width).advance actor.val).tick.next.advance time.val).state = _
  rw [SourceOperationRuntime.runtime_tail, native_state_advance, native_state_advance]
  change rawField ((runtimeAt (firstState owner (bound + width))).state + actor.val + (time.val + 1)) = _
  rw [runtimeAt_state]
  congr 1

theorem query_constant (owner : GlobalParentOwner) (bound width : Nat) (actor : Fin (bound + 1)) :
    shortQuery owner bound width actor = fun _ => rawField (firstState owner (bound + width)) := by
  funext time
  rw [query_value]
  rw [show firstState owner (bound + width) + actor.val + time.val + 1 =
    firstState owner (bound + width) + (actor.val + time.val + 1) by omega]
  exact field_constant owner (bound + width) (actor.val + time.val + 1) (by omega)

def completionDepth (owner : GlobalParentOwner) (bound width : Nat) : Nat := firstState owner (bound + width) + bound + width

def cell (owner : GlobalParentOwner) (bound width : Nat) (actor : Fin (bound + 1)) (time : Fin (width + 1)) :
    Fin (completionDepth owner bound width + 1) :=
  ⟨firstState owner (bound + width) + actor.val + time.val, by unfold completionDepth; omega⟩

theorem query_material (owner : GlobalParentOwner) (bound width : Nat) (actor : Fin (bound + 1)) (time : Fin (width + 1)) :
    let stage := (history runtimeSeed (completionDepth owner bound width)).stageAt (cell owner bound width actor time)
    shortQuery owner bound width actor time = rawField stage.next.state ∧
      type_of% (sample_factorizes runtimeSeed (completionDepth owner bound width) (cell owner bound width actor time)) := by
  refine ⟨?_, sample_factorizes runtimeSeed (completionDepth owner bound width) (cell owner bound width actor time)⟩
  exact (query_value owner bound width actor time).trans
    (congrArg rawField (runtimeAt_state (firstState owner (bound + width) + actor.val + time.val + 1))).symm

end
end SourcePrimeObservationDelay
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
