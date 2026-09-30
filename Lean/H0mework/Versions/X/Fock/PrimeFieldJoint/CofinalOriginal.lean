import H0mework.Versions.X.Fock.PrimeFieldJoint.CofinalExact

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedJointDecoderCofinal

open SourceJointDecoderCofinal SourceGeneratedAcquisitionContinuation SourceGeneratedAcquisitionJoint
open SourceGeneratedActionWords.Fock.OriginalHilbert Filter
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Topology
noncomputable section

theorem original_read (runtime : LivingRuntimeState process) (target : SourceJointClockGraph.Carrier) :
    SourceGeneratedJointClockGraph.fieldRead (depth runtime) (inventoryBound runtime)
      (SourceGeneratedJointFiniteDecoder.decode (depth runtime) (inventoryBound runtime) target) =
        estimate (inventoryBound runtime) target := by
  change SourceJointClockGraph.read (SourceHistoryWord.word (inventoryBound runtime)
    (Actor.currentPullback (depth runtime) (inventoryBound runtime)
      (SourceGeneratedJointFiniteDecoder.decode (depth runtime) (inventoryBound runtime) target))) =
    SourceJointFiniteDecoder.read (inventoryBound runtime) (SourceJointFiniteDecoder.decode (inventoryBound runtime) target)
  rw [SourceGeneratedJointFiniteDecoder.decode_actor, SourceJointFiniteDecoder.read_source]

theorem original_tendsto (round : Nat) (target : SourceJointClockGraph.Carrier) :
    Tendsto (fun future =>
      let runtime := roundRuntime (round + future)
      SourceGeneratedJointClockGraph.fieldRead (depth runtime) (inventoryBound runtime)
        (SourceGeneratedJointFiniteDecoder.decode (depth runtime) (inventoryBound runtime) target)) atTop
          (𝓝 (SourceJointClockGraph.recover target)) := by
  simpa only [original_read] using estimate_tendsto round target

theorem original_word_exact (round : Nat) (sourceWord : Nat →₀ ℂ) (future : Nat)
    (reached : demand round sourceWord ≤ future) :
    let runtime := roundRuntime (round + future)
    word (depth runtime) (inventoryBound runtime)
      (SourceGeneratedJointFiniteDecoder.decode (depth runtime) (inventoryBound runtime)
        (SourceJointClockGraph.action (SourceJointClockGraph.read sourceWord))) = sourceWord := by
  change SourceHistoryWord.word (inventoryBound (roundRuntime (round + future)))
    (Actor.currentPullback (depth (roundRuntime (round + future))) (inventoryBound (roundRuntime (round + future)))
      (SourceGeneratedJointFiniteDecoder.decode (depth (roundRuntime (round + future)))
        (inventoryBound (roundRuntime (round + future)))
        (SourceJointClockGraph.action (SourceJointClockGraph.read sourceWord)))) = sourceWord
  rw [SourceGeneratedJointFiniteDecoder.decode_actor]
  exact source_word_exact round sourceWord future reached

theorem root_cost_tendsto (round : Nat) :
    Tendsto (fun future => ‖SourceJointFiniteDecoder.residual (inventoryBound (roundRuntime (round + future)))
      (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceOwnedObservationHistory.sourcePoint 0)))‖ ^ 2)
        atTop (𝓝 (1 : ℝ)) := by
  have paid := cost_tendsto round (SourceJointClockGraph.read
    (SourceClockComplex.ofNative (SourceOwnedObservationHistory.sourcePoint 0)))
  rw [SourceJointClockDecoder.root_unit_cost] at paid
  exact paid

end
end SourceGeneratedJointDecoderCofinal
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
