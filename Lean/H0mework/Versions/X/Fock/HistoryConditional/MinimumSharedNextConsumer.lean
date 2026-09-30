import H0mework.Versions.X.Fock.HistoryConditional.MinimumSharedNextBudget
import H0mework.Versions.X.Fock.HistoryConditional.NativePosteriorField

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceMinimumSharedNext

open SourceCopyCurrentCoordinates (maximumIndex realize residual)
open SourceCopyTemporalBoundary (recordedPrefix)
open SourceOperatorObservationAcquisition (decode)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
variable {Key : Type*} [DecidableEq Key]

theorem effect_reconstruction (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (read : Nat → Key) (key : Key) :
    let value := SourceConditionalNativePosterior.decoder runtime read key
    realize runtime.tick.next (maximumIndex runtime.tick.next) 0
      (decode runtime.tick.next (maximumIndex runtime.tick.next) (next_nonunit runtime) 0
        (step runtime nonunit (recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1) value))) +
      SourceJointClockGraph.action (residual runtime (maximumIndex runtime) 0 value) =
        SourceConditionalVector.realizeModel runtime.tick.next (SourceConditionalNativePosterior.effect runtime read key) := by
  dsimp only
  rw [SourceConditionalNativePosterior.effect_realization]
  exact step_reconstruction runtime nonunit _

theorem effect_loss (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (read : Nat → Key) (key : Key) :
    let value := SourceConditionalNativePosterior.decoder runtime read key
    ‖SourceConditionalVector.realizeModel runtime.tick.next (SourceConditionalNativePosterior.effect runtime read key) -
      realize runtime.tick.next (maximumIndex runtime.tick.next) 0
        (decode runtime.tick.next (maximumIndex runtime.tick.next) (next_nonunit runtime) 0
          (step runtime nonunit (recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1) value)))‖ ^ 2 =
      ‖residual runtime (maximumIndex runtime) 0 value‖ ^ 2 := by
  dsimp only
  have paid := step_loss runtime nonunit (SourceConditionalNativePosterior.decoder runtime read key)
  rw [← SourceConditionalNativePosterior.effect_realization runtime read key] at paid
  with_reducible exact paid

end
end SourceMinimumSharedNext
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
