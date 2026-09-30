import H0mework.Fock.HistoryModel.OriginalHilbertRecovery
import H0mework.Fock.HistoryModel.DynamicHilbertCompression

/-! The original time consumer receives the source task whose snapshot compression already carries a positive cost. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionWords.Fock.OriginalHilbert

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock

noncomputable section

def inputSnapshot (depth : Nat) (value : Field nativeStep (rawWords depth)) : ParentCarrier :=
  Dynamic.Hilbert.present depth ((originalField depth).symm value)

theorem input_snapshot_actual (depth bound : Nat) (index : Fin (bound + 1)) :
    inputSnapshot depth (Actor.originalRead depth bound index) = Dynamic.Hilbert.snapshot bound index := by
  change Dynamic.Hilbert.present depth ((originalField depth).symm (originalField depth (Dynamic.Hilbert.read depth bound index))) = _
  rw [LinearEquiv.symm_apply_apply]
  exact Dynamic.Hilbert.present_read depth bound index

theorem original_snapshot_cost (owner : GlobalParentOwner) (depth : Nat) (decoder : ParentCarrier → ℂ) :
    (1 / (Dynamic.Hilbert.collisionBound owner + 1 : ℝ)) / 2 ≤
      error (historyPMF (Dynamic.Hilbert.collisionBound owner)) (Actor.originalRead depth (Dynamic.Hilbert.collisionBound owner))
        (Dynamic.Hilbert.clockTask (Dynamic.Hilbert.collisionBound owner)) (decoder ∘ inputSnapshot depth) := by
  simpa only [error, Function.comp_apply, input_snapshot_actual] using Dynamic.Hilbert.snapshot_clock_cost owner decoder

theorem original_snapshot_cost_positive (owner : GlobalParentOwner) (depth : Nat) (decoder : ParentCarrier → ℂ) :
    0 < error (historyPMF (Dynamic.Hilbert.collisionBound owner)) (Actor.originalRead depth (Dynamic.Hilbert.collisionBound owner))
      (Dynamic.Hilbert.clockTask (Dynamic.Hilbert.collisionBound owner)) (decoder ∘ inputSnapshot depth) :=
  lt_of_lt_of_le (by positivity) (original_snapshot_cost owner depth decoder)

end
end SourceGeneratedActionWords.Fock.OriginalHilbert
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
