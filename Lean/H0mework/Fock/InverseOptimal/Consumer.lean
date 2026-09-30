import H0mework.Fock.InverseOptimal.Geometry
import H0mework.Fock.InverseDistribution.LossConsumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseDistributionOptimal

open SourceGeneratedActionWords SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceConditionalModel (Actors nextRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem conditional_cost {Key : Type*} [DecidableEq Key] (runtime : LivingRuntimeState process)
    (depth : Nat) (word : List (Fock.Letter depth)) (read : Nat → Key) (key : Key)
    (supported : key ∈ ((historyPMF (inventoryBound runtime)).map (fun actor : Actors runtime => read actor.val)).support)
    (candidate : SourceJointClockGraph.Carrier) :
    (∑ actor : Actors runtime, ((SourceConditionalNativeObservers.generate read (inventoryBound runtime) key).2 actor : ℝ) *
      ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) - SourceCompiledGWord.effect depth word candidate‖ ^ 2) =
    (∑ actor : Actors runtime, ((SourceConditionalNativeObservers.generate read (inventoryBound runtime) key).2 actor : ℝ) *
      ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) - SourceConditionalNativePosterior.decoder runtime read key‖ ^ 2) +
    ((∑ actor : Actors runtime, ‖(((SourceInverseDistributionAction.generate read (word.map SourceCopyNativeWord.encode)
      (inventoryBound runtime) key).2 actor).2 : ℂ)‖ ^ 2) +
      ‖SourceCompiledGWord.effect depth word (SourceGWordInverse.recover depth word
        (SourceConditionalNativePosterior.decoder runtime read key) - candidate)‖ ^ 2) := by
  have paid := SourceConditionalNativePosterior.error_decomposition runtime read key supported
    (SourceCompiledGWord.effect depth word candidate)
  rw [error_decomposition, SourceInverseDistributionLoss.generated_residual_norm] at paid
  exact paid

theorem optimal (depth : Nat) (word : List (Fock.Letter depth)) (value candidate : SourceJointClockGraph.Carrier) :
    ‖value - SourceCompiledGWord.effect depth word (SourceGWordInverse.recover depth word value)‖ ^ 2 ≤
      ‖value - SourceCompiledGWord.effect depth word candidate‖ ^ 2 := by
  change ‖SourceGWordInverse.residual depth word value‖ ^ 2 ≤ _
  rw [error_decomposition]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem optimal_unique (depth : Nat) (word : List (Fock.Letter depth)) (value candidate : SourceJointClockGraph.Carrier) :
    ‖value - SourceCompiledGWord.effect depth word candidate‖ ^ 2 =
      ‖value - SourceCompiledGWord.effect depth word (SourceGWordInverse.recover depth word value)‖ ^ 2 ↔
      candidate = SourceGWordInverse.recover depth word value := by
  constructor
  · intro same
    change ‖value - SourceCompiledGWord.effect depth word candidate‖ ^ 2 = ‖SourceGWordInverse.residual depth word value‖ ^ 2 at same
    rw [error_decomposition] at same
    have vanished : ‖SourceCompiledGWord.effect depth word (SourceGWordInverse.recover depth word value - candidate)‖ ^ 2 = 0 := by
      linarith only [same]
    have zero := norm_eq_zero.mp (sq_eq_zero_iff.mp vanished)
    have original := congrArg (SourceGWordInverse.recover depth word) zero
    rw [SourceGWordInverse.recover_effect, map_zero, sub_eq_zero] at original
    exact original.symm
  · rintro rfl
    rfl

end
end SourceInverseDistributionOptimal
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
