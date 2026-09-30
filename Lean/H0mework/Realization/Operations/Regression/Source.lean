import H0mework.Realization.Operations.ObservationNative
import H0mework.Arithmetic.FockDynamics.RootRuntime

/-!
# Actual coarse observations and their generated future model

The original Fock states zero and one share their current coarse read while their
actual next reads differ. The complete future model preserves this distinction
and its action remains the projection of the same native source action.
-/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationObserved.Controls

open SourceOperationNative SourceOperationNative.Observed
open SourceGeneratedActionObservationHistory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

def coarseRead (state : process.State) : ℤ := (state / 2 : Nat)

theorem actual_current_collision :
    coarseRead (runtimeAt 0).state = coarseRead (runtimeAt 1).state ∧
      coarseRead (runtimeAt 0).tick.next.state ≠ coarseRead (runtimeAt 1).tick.next.state := by
  constructor
  · rfl
  · change (0 : ℤ) ≠ 1
    exact zero_ne_one

theorem current_read_cannot_determine_next :
    ¬ ∃ next : ℤ → ℤ, ∀ runtime : LivingRuntimeState process,
      next (coarseRead runtime.state) = coarseRead runtime.tick.next.state := by
  rintro ⟨next, reads⟩
  exact actual_current_collision.2
    ((reads (runtimeAt 0)).symm.trans
      ((congrArg next actual_current_collision.1).trans (reads (runtimeAt 1))))

theorem history_and_model_separate_actual_points :
    observedPoint coarseRead (runtimeAt 0) ≠ observedPoint coarseRead (runtimeAt 1) ∧
      modelPoint coarseRead (runtimeAt 0) ≠ modelPoint coarseRead (runtimeAt 1) := by
  constructor
  · intro same
    exact actual_current_collision.2
      ((native_fibre_iff coarseRead (runtimeAt 0) (runtimeAt 1)).mp same 1)
  · intro same
    exact actual_current_collision.2
      ((model_native_fibre_iff coarseRead (runtimeAt 0) (runtimeAt 1)).mp same 1)

theorem model_action_is_actual (runtime : LivingRuntimeState process) :
    let stage := SourceGeneratedRuntimeMaterialStageAt.generate runtime
    modelAction (sourceAction process) (observer process coarseRead) (modelPoint coarseRead runtime) =
        modelPoint coarseRead stage.next ∧
      modelReadout (sourceAction process) (observer process coarseRead) (modelPoint coarseRead stage.next) =
        coarseRead stage.next.state ∧
      process.stateAt runtime.state = runtime.current ∧
      (process.toAnswerNextCausalWorld.emitted (ULift.up runtime.state) =
          ULift.up stage.activated.generated ∧
        stage.activated.generated.occurrence =
          runtime.current.root.toAuthoritativeRoot.toLedgerRoot.emitted runtime.current.visit.current ∧
        HEq stage.wholeLedgerWriteBack
          (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
        stage.next.current = stage.activated.nextCurrent) :=
  model_factorizes coarseRead runtime

end

end SourceOperationObserved.Controls
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
