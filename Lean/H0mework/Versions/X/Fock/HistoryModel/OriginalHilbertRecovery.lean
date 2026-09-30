import H0mework.Versions.X.Fock.HistoryModel.OriginalHilbertConditional
import H0mework.Versions.X.Fock.HistoryModel.DynamicHilbertRecovery

/-! The original next-field conditional retains the actor distinguished by the already paid source words. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionWords.Fock.OriginalHilbert

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

local instance recoveryFieldUniform (depth : Nat) : UniformSpace (Field nativeStep (rawWords depth)) :=
  fieldUniform nativeStep (rawWords depth)
local instance recoveryFieldMeasurable (depth : Nat) : MeasurableSpace (Field nativeStep (rawWords depth)) :=
  fieldBorel nativeStep (rawWords depth)
local instance recoveryFieldBorel (depth : Nat) : BorelSpace (Field nativeStep (rawWords depth)) := ⟨rfl⟩
local instance recoveryFieldT2 (depth : Nat) : T2Space (Field nativeStep (rawWords depth)) :=
  Actor.conditionalFieldT2 depth

theorem next_read_actual (depth bound : Nat) (index : Fin (bound + 1)) :
    Actor.nextRead depth bound index =
      originalField depth (Complete.point depth ((runtimeAt (index.val + 1)).current.visit.current : Current)) := by
  let current : Current := (runtimeAt index.val).current.visit.current
  have acted := fieldPoint_action nativeStep (rawWords depth) current
  have next := original_point depth ((runtimeAt (index.val + 1)).current.visit.current : Current)
  exact (congrArg (fieldAction nativeStep (rawWords depth)) (Actor.originalRead_actual depth bound index)).trans
    (acted.trans next.symm)

theorem next_read_injective (depth bound : Nat) : Function.Injective (Actor.nextRead depth bound) := by
  intro left right same
  rw [next_read_actual, next_read_actual] at same
  have states := Dynamic.Hilbert.point_runtime_injective depth ((originalField depth).injective same)
  exact Fin.ext (Nat.add_right_cancel states)

theorem next_posterior (depth bound : Nat) (index : Fin (bound + 1))
    (supported : Actor.nextRead depth bound index ∈ (SourceWeightedRecovery.observed (historyPMF bound) (Actor.nextRead depth bound)).support) :
    SourceConditionalHistory.conditional (historyPMF bound) (Actor.nextRead depth bound)
      (Actor.nextRead depth bound index) supported = PMF.pure index :=
  ObservationRefinement.conditional_injective (historyPMF bound) (Actor.nextRead depth bound)
    (next_read_injective depth bound) index (by simp [historyPMF])

theorem original_next_recovery (depth bound : Nat) (task : Fin (bound + 1) → ℂ) (index : Fin (bound + 1)) :
    IsometricRetainedTransfer.transfer
        (SourceOwnedObservationHistory.pullback nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent bound)
        (Actor.currentTransfer depth bound (taskValue (historyPMF bound) task)) (Actor.nextRead depth bound index) = task index :=
  (Actor.completeTransfer_is_conditional depth bound task (Actor.nextRead depth bound index)).trans
    (ObservationRefinement.optimum_injective (historyPMF bound) (Actor.nextRead depth bound)
      (next_read_injective depth bound) task index (by simp [historyPMF]))

theorem literal_next_atom (depth : Nat) :
    Actor.nextRead (depth + 1) depth (Fin.last depth) = originalField (depth + 1) (Complete.nativeNext depth) := by
  rw [next_read_actual]
  exact congrArg (originalField (depth + 1)) (Complete.next_actual depth).symm

theorem literal_next_recovery (depth : Nat) (task : Fin (depth + 1) → ℂ) :
    IsometricRetainedTransfer.transfer
        (SourceOwnedObservationHistory.pullback nativeStep (rawWords (depth + 1)) CanonicalUnitArithmeticRoot.initialCurrent depth)
        (Actor.currentTransfer (depth + 1) depth (taskValue (historyPMF depth) task))
        (originalField (depth + 1) (Complete.nativeNext depth)) = task (Fin.last depth) := by
  rw [← literal_next_atom]
  exact original_next_recovery (depth + 1) depth task (Fin.last depth)

end
end SourceGeneratedActionWords.Fock.OriginalHilbert
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
