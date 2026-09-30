import H0mework.Versions.X.Fock.PrimeFieldJoint.CofinalLimit

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceJointDecoderCofinal

open SourceGeneratedAcquisitionContinuation SourceGeneratedAcquisitionJoint
open SourceGeneratedActionWords.Fock.OriginalHilbert
noncomputable section

private theorem source_member (round : Nat) (sourceWord : Nat →₀ ℂ) :
    SourceJointClockGraph.action (SourceJointClockGraph.read sourceWord) ∈ images round (demand round sourceWord) := by
  let runtime := sourceRound round sourceWord
  let value := realizeWord round sourceWord
  refine ⟨Actor.currentPullback (depth runtime) (inventoryBound runtime) value, ?_⟩
  exact (SourceGeneratedJointFiniteDecoder.actor_action _ _ value).trans
    ((SourceGeneratedJointClockGraph.original_time_square _ _ value).trans
      (congrArg SourceJointClockGraph.action (SourceGeneratedJointClockGraph.realization_graph round sourceWord)))

private theorem member_decoded (bound : Nat) (target : SourceJointClockGraph.Carrier) (present : target ∈ image bound) :
    SourceJointFiniteDecoder.action bound (SourceJointFiniteDecoder.decode bound target) = target := by
  rcases present with ⟨source, rfl⟩
  change SourceJointFiniteDecoder.action bound
    (SourceJointFiniteDecoder.decode bound (SourceJointFiniteDecoder.action bound source)) = _
  rw [SourceJointFiniteDecoder.decode_action]
  rfl

theorem source_exact (round : Nat) (sourceWord : Nat →₀ ℂ) (future : Nat)
    (reached : demand round sourceWord ≤ future) :
    estimate (inventoryBound (roundRuntime (round + future)))
      (SourceJointClockGraph.action (SourceJointClockGraph.read sourceWord)) = SourceJointClockGraph.read sourceWord := by
  have present := images_mono round reached (source_member round sourceWord)
  have recovered := congrArg SourceJointClockGraph.recover (member_decoded _ _ present)
  change SourceJointClockGraph.recover (SourceJointClockGraph.action
    (estimate (inventoryBound (roundRuntime (round + future)))
      (SourceJointClockGraph.action (SourceJointClockGraph.read sourceWord)))) =
        SourceJointClockGraph.recover (SourceJointClockGraph.action (SourceJointClockGraph.read sourceWord)) at recovered
  simpa only [SourceJointClockGraph.recover_action] using recovered

theorem source_word_exact (round : Nat) (sourceWord : Nat →₀ ℂ) (future : Nat)
    (reached : demand round sourceWord ≤ future) :
    SourceHistoryWord.word (inventoryBound (roundRuntime (round + future)))
      (SourceJointFiniteDecoder.decode (inventoryBound (roundRuntime (round + future)))
        (SourceJointClockGraph.action (SourceJointClockGraph.read sourceWord))) = sourceWord := by
  have projected := congrArg SourceJointClockGraph.joint (source_exact round sourceWord future reached)
  change SourceJointClockGraph.joint (SourceJointFiniteDecoder.read (inventoryBound (roundRuntime (round + future)))
    (SourceJointFiniteDecoder.decode (inventoryBound (roundRuntime (round + future)))
      (SourceJointClockGraph.action (SourceJointClockGraph.read sourceWord)))) =
        SourceJointClockGraph.joint (SourceJointClockGraph.read sourceWord) at projected
  rw [SourceJointFiniteDecoder.read_source, SourceJointClockGraph.joint_source, SourceJointClockGraph.joint_source] at projected
  exact SourceMassCompletion.jointRead_injective projected

theorem source_residual_zero (round : Nat) (sourceWord : Nat →₀ ℂ) (future : Nat)
    (reached : demand round sourceWord ≤ future) :
    SourceJointFiniteDecoder.residual (inventoryBound (roundRuntime (round + future)))
      (SourceJointClockGraph.action (SourceJointClockGraph.read sourceWord)) = 0 := by
  rw [residual_formula, member_decoded _ _ (images_mono round reached (source_member round sourceWord)), sub_self]

end
end SourceJointDecoderCofinal
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
