import H0mework.Versions.X.Fock.HistoryModel.CoarseCode.Transfer
import H0mework.Versions.X.Probability.Recovery.Refinement

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWordFieldCode

open SourceGeneratedActionWords.Fock.OriginalHilbert
open SourceGeneratedActionWords.Fock
open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceGeneratedRuntimeHistoryProbability
open SourceConditionalHistory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section

attribute [local instance] fieldUniformSpace fieldMeasurable fieldBorelSpace fieldT2

theorem field_to_code_residual (depth : Nat)
    (word : List (Letter (depth + 1))) (task : Fin (depth + 1) → ℂ) :
    ‖SourceWeightedRecovery.residual (historyPMF depth)
      (fieldCode depth word ∘ Actor.nextRead (depth + 1) depth)
      (SourceWeightedRecovery.taskValue (historyPMF depth) task)‖ ^ 2 =
      ‖SourceWeightedRecovery.residual (historyPMF depth)
        (Actor.nextRead (depth + 1) depth)
        (SourceWeightedRecovery.taskValue (historyPMF depth) task)‖ ^ 2 +
      SourceWeightedRecovery.error (historyPMF depth)
        (fieldCode depth word ∘ Actor.nextRead (depth + 1) depth)
        (fun actor => IsometricRetainedTransfer.transfer
          (SourceOwnedObservationHistory.pullback nativeStep (rawWords (depth + 1))
            CanonicalUnitArithmeticRoot.initialCurrent depth)
          (Actor.currentTransfer (depth + 1) depth
            (SourceWeightedRecovery.taskValue (historyPMF depth) task))
          (Actor.nextRead (depth + 1) depth actor))
        (SourceWeightedRecovery.optimalDecoder (historyPMF depth)
          (fieldCode depth word ∘ Actor.nextRead (depth + 1) depth) task) := by
  have gain := SourceWeightedRecovery.ObservationRefinement.optimal_gain
    (historyPMF depth) (Actor.nextRead (depth + 1) depth) (fieldCode depth word) task
  calc
    _ = SourceWeightedRecovery.error (historyPMF depth)
          (fieldCode depth word ∘ Actor.nextRead (depth + 1) depth) task
          (SourceWeightedRecovery.optimalDecoder (historyPMF depth)
            (fieldCode depth word ∘ Actor.nextRead (depth + 1) depth) task) :=
      (SourceWeightedRecovery.optimal_attains _ _ task).symm
    _ = SourceWeightedRecovery.error (historyPMF depth)
          (Actor.nextRead (depth + 1) depth) task
          (SourceWeightedRecovery.optimalDecoder (historyPMF depth)
            (Actor.nextRead (depth + 1) depth) task) +
        SourceWeightedRecovery.error (historyPMF depth)
          (fieldCode depth word ∘ Actor.nextRead (depth + 1) depth)
          (fun actor => SourceWeightedRecovery.optimalDecoder (historyPMF depth)
            (Actor.nextRead (depth + 1) depth) task
            (Actor.nextRead (depth + 1) depth actor))
          (SourceWeightedRecovery.optimalDecoder (historyPMF depth)
            (fieldCode depth word ∘ Actor.nextRead (depth + 1) depth) task) := gain
    _ = _ := by
      rw [SourceWeightedRecovery.optimal_attains]
      congr 1
      exact congrArg
        (fun taskRead : Fin (depth + 1) → ℂ =>
          SourceWeightedRecovery.error (historyPMF depth)
            (fieldCode depth word ∘ Actor.nextRead (depth + 1) depth) taskRead
            (SourceWeightedRecovery.optimalDecoder (historyPMF depth)
              (fieldCode depth word ∘ Actor.nextRead (depth + 1) depth) task))
        (by
          funext actor
          exact (Actor.completeTransfer_is_conditional (depth + 1) depth task
            (Actor.nextRead (depth + 1) depth actor)).symm)

end
end SourceWordFieldCode
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
