import H0mework.Fock.SourceHistoryClock.DecoderFiniteRecovery
import H0mework.Fock.SourceHistoryClock.DecoderNative

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedJointFiniteDecoder

open SourceGeneratedActionWords.Fock.OriginalHilbert SourceGeneratedAcquisitionMeasure
open SourceGeneratedJointClockGraph SourceGeneratedJointTime
noncomputable section

def decode (depth bound : Nat) : SourceJointClockGraph.Carrier →L[ℂ] FieldSpace depth bound :=
  (Actor.currentTransfer depth bound).comp (SourceJointFiniteDecoder.decode bound)

theorem decode_actor (depth bound : Nat) (target : SourceJointClockGraph.Carrier) :
    Actor.currentPullback depth bound (decode depth bound target) = SourceJointFiniteDecoder.decode bound target :=
  actor_transfer_samples depth bound _

theorem actor_action (depth bound : Nat) (value : FieldSpace depth bound) :
    SourceJointFiniteDecoder.action bound (Actor.currentPullback depth bound value) =
      nextFieldRead depth bound (timeTransfer depth bound value) := by
  change SourceJointClockGraph.action (SourceJointFiniteDecoder.read bound (Actor.currentPullback depth bound value)) = _
  rw [SourceJointFiniteDecoder.read_source, original_time_square]
  rfl

theorem next_realized (depth bound : Nat) (value : NextSpace depth bound) :
    SourceJointFiniteDecoder.action bound (Actor.currentPullback depth bound (timePullback depth bound value)) =
      nextFieldRead depth bound value := by
  rw [actor_action]
  rw [show timeTransfer depth bound (timePullback depth bound value) = value from
    IsometricRetainedTransfer.transfer_pullback (timePullback depth bound) value]

theorem original_K (depth bound : Nat) (value : NextSpace depth bound) :
    decode depth bound (nextFieldRead depth bound value) = timePullback depth bound value := by
  change Actor.currentTransfer depth bound (SourceJointFiniteDecoder.decode bound (nextFieldRead depth bound value)) = _
  rw [← next_realized, SourceJointFiniteDecoder.decode_action]
  exact IsometricRetainedTransfer.transfer_pullback (Actor.currentPullback depth bound) _

theorem error_decomposition (depth bound : Nat) (target : SourceJointClockGraph.Carrier) (proposal : FieldSpace depth bound) :
    ‖target - nextFieldRead depth bound (timeTransfer depth bound proposal)‖ ^ 2 =
      ‖SourceJointFiniteDecoder.residual bound target‖ ^ 2 +
        ‖nextFieldRead depth bound (timeTransfer depth bound (decode depth bound target - proposal))‖ ^ 2 := by
  have original := SourceJointFiniteDecoder.error_decomposition bound target (Actor.currentPullback depth bound proposal)
  have same : SourceJointFiniteDecoder.decode bound target - Actor.currentPullback depth bound proposal =
      Actor.currentPullback depth bound (decode depth bound target - proposal) := by rw [map_sub, decode_actor]
  rw [actor_action, same, actor_action] at original
  exact original

/-- Keep the original Field claim indexed when specializing a generated root inventory. -/
def MinimumAt (depth bound : Nat) (target : SourceJointClockGraph.Carrier) : Prop :=
  IsMinOn (fun proposal : FieldSpace depth bound =>
    ‖target - nextFieldRead depth bound (timeTransfer depth bound proposal)‖ ^ 2) Set.univ (decode depth bound target)

theorem source_minimum (depth bound : Nat) (target : SourceJointClockGraph.Carrier) : MinimumAt depth bound target := by
  dsimp only [MinimumAt]
  apply isMinOn_univ_iff.mpr
  intro proposal
  have minimum := (isMinOn_univ_iff.mp (SourceJointFiniteDecoder.source_minimum bound target))
    (Actor.currentPullback depth bound proposal)
  rw [← decode_actor depth bound target, actor_action, actor_action] at minimum
  exact minimum

theorem minimum_fibre (depth bound : Nat) (target : SourceJointClockGraph.Carrier) (proposal : FieldSpace depth bound) :
    ‖target - nextFieldRead depth bound (timeTransfer depth bound proposal)‖ ^ 2 =
      ‖SourceJointFiniteDecoder.residual bound target‖ ^ 2 ↔ proposal = decode depth bound target := by
  have complete := SourceJointFiniteDecoder.minimum_fibre bound target (Actor.currentPullback depth bound proposal)
  rw [actor_action, ← decode_actor depth bound target] at complete
  exact complete.trans (Actor.currentPullback depth bound).injective.eq_iff

theorem next_residual_zero (depth bound : Nat) (value : NextSpace depth bound) :
    SourceJointFiniteDecoder.residual bound (nextFieldRead depth bound value) = 0 := by
  rw [← next_realized]
  exact SourceJointFiniteDecoder.residual_action bound _

end
end SourceGeneratedJointFiniteDecoder
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
