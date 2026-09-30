import H0mework.Fock.CopyGraph.Moments
import H0mework.Fock.PrimeFieldJoint.CofinalConsumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyGraph

open SourceCopyProgram SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionJoint SourceGeneratedAcquisitionContinuation
open SourceGeneratedJointClockGraph
noncomputable section

theorem original_copy_energy (depth bound : Nat) (index : Index depth) (value : FieldSpace depth bound) :
    ‖action depth index (fieldRead depth bound value)‖ ^ 2 =
      ‖value‖ ^ 2 + (bound + 1 : ℝ) *
        ‖∫ actor, SourceGeneratedActionWords.Fock.OriginalHilbert.Actor.currentPullback depth bound value actor
          ∂(SourceGeneratedRuntimeHistoryProbability.historyPMF bound).toMeasure‖ ^ 2 +
      (scale depth index : ℝ) ^ 2 * ‖SourceClockComplex.clock (word depth bound value)‖ ^ 2 := by
  rw [action_energy, original_field_norm]
  have clockRead : SourceJointClockGraph.clock (fieldRead depth bound value) =
      SourceClockComplex.clock (word depth bound value) := rfl
  rw [clockRead]
  ring

theorem original_copy_realization (round depth bound : Nat) (index : Index depth) (value : FieldSpace depth bound) :
    let copied := complexAction depth index (word depth bound value)
    fieldRead (SourceGeneratedAcquisitionJoint.depth (sourceRound round copied))
      (inventoryBound (sourceRound round copied)) (realizeWord round copied) = action depth index (fieldRead depth bound value) := by
  exact (realization_graph round _).trans (action_source depth index (word depth bound value)).symm

theorem original_recovery_realization (round depth : Nat) (index : Index depth) (target : Nat →₀ ℤ) :
    let recovered := SourceClockComplex.ofNative (SourceCopyProgram.recover depth index target)
    let remaining := SourceClockComplex.ofNative (SourceCopyProgram.residual depth index target)
    fieldRead (SourceGeneratedAcquisitionJoint.depth (sourceRound round recovered))
      (inventoryBound (sourceRound round recovered)) (realizeWord round recovered) +
        axes (SourceSuccessorBoundary.mass ℂ remaining)
          ((scale depth index : ℂ)⁻¹ * SourceClockComplex.clock remaining) =
      recover depth index (SourceJointClockGraph.read (SourceClockComplex.ofNative target)) := by
  dsimp only
  rw [realization_graph]
  exact (recovery_native_moments depth index target).symm

theorem original_residual_realization (round depth : Nat) (index : Index depth) (target : Nat →₀ ℤ) :
    let remaining := SourceClockComplex.ofNative (SourceCopyProgram.residual depth index target)
    residual depth index (SourceJointClockGraph.read (SourceClockComplex.ofNative target)) +
      axes (SourceSuccessorBoundary.mass ℂ remaining) (SourceClockComplex.clock remaining) =
        fieldRead (SourceGeneratedAcquisitionJoint.depth (sourceRound round remaining))
          (inventoryBound (sourceRound round remaining)) (realizeWord round remaining) := by
  dsimp only
  rw [realization_graph]
  exact residual_native_moments depth index target

def FieldAt (round depth bound : Nat) (index : Index depth) (value : FieldSpace depth bound) : Prop :=
    let copied := complexAction depth index (word depth bound value)
    type_of% (original_copy_energy depth bound index value) ∧
      type_of% (original_copy_realization round depth bound index value) ∧
      type_of% (source_round_after round copied) ∧
      (∀ future : Nat, ∀ reached : demand round copied ≤ future,
        type_of% (SourceGeneratedJointDecoderCofinal.original_word_exact round copied future reached)) ∧
      type_of% (NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime.coversAt_factorizes
        (sourceRound round copied) .particleWave) ∧
      type_of% (NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime.coversAt_factorizes
        (sourceRound round copied).tick.next .particleWave)

theorem original_field_consumed (round depth bound : Nat) (index : Index depth) (value : FieldSpace depth bound) :
    FieldAt round depth bound index value := by
  dsimp only [FieldAt]
  exact ⟨original_copy_energy depth bound index value, original_copy_realization round depth bound index value,
    source_round_after round _, SourceGeneratedJointDecoderCofinal.original_word_exact round _,
    NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime.coversAt_factorizes (sourceRound round _) .particleWave,
    NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime.coversAt_factorizes (sourceRound round _).tick.next .particleWave⟩

end
end SourceCopyGraph
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
