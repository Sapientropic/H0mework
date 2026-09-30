import H0mework.Versions.X.Fock.HistoryModel.DynamicHilbertRecovery
import H0mework.Versions.X.Fock.HistoryModel.DynamicHilbertSnapshot

/-! Original snapshot compression loses a paid distinction that the complete word transfer actually recovers. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionWords.Fock.Dynamic.Hilbert

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock

noncomputable section

local instance (depth : Nat) : UniformSpace (Complete.Carrier depth) := uniform depth
local instance (depth : Nat) : MeasurableSpace (Complete.Carrier depth) := measurable depth
local instance (depth : Nat) : BorelSpace (Complete.Carrier depth) := ⟨rfl⟩
local instance (depth : Nat) : T2Space (Complete.Carrier depth) := field_t2 depth

def present (depth : Nat) (value : Complete.Carrier depth) : ParentCarrier :=
  completeRead (Fock.actions depth) (Fock.observer depth) (.inl ()) [] value 0

theorem present_read (depth bound : Nat) (index : Fin (bound + 1)) :
    present depth (read depth bound index) = snapshot bound index := unit_complete_read depth _

theorem compressed_clock_cost (owner : GlobalParentOwner) (depth : Nat) (decoder : ParentCarrier → ℂ) :
    (1 / (collisionBound owner + 1 : ℝ)) / 2 ≤
      error (historyPMF (collisionBound owner)) (read depth (collisionBound owner))
        (clockTask (collisionBound owner)) (decoder ∘ present depth) := by
  simpa only [error, Function.comp_apply, present_read] using snapshot_clock_cost owner decoder

theorem complete_clock_cost_zero (owner : GlobalParentOwner) (depth : Nat) :
    error (historyPMF (collisionBound owner)) (read depth (collisionBound owner))
      (clockTask (collisionBound owner))
      (optimalDecoder (historyPMF (collisionBound owner)) (read depth (collisionBound owner)) (clockTask (collisionBound owner))) = 0 := by
  rw [optimal_attains, complete_residual_zero, norm_zero]
  exact zero_pow (by decide : 2 ≠ 0)

theorem compressed_clock_gap (owner : GlobalParentOwner) (depth : Nat) (decoder : ParentCarrier → ℂ) :
    0 < error (historyPMF (collisionBound owner)) (read depth (collisionBound owner))
        (clockTask (collisionBound owner)) (decoder ∘ present depth) -
      error (historyPMF (collisionBound owner)) (read depth (collisionBound owner))
        (clockTask (collisionBound owner))
        (optimalDecoder (historyPMF (collisionBound owner)) (read depth (collisionBound owner)) (clockTask (collisionBound owner))) := by
  rw [complete_clock_cost_zero, sub_zero]
  exact lt_of_lt_of_le (by positivity) (compressed_clock_cost owner depth decoder)

theorem no_snapshot_reconstruction (owner : GlobalParentOwner) (depth : Nat) :
    ¬ ∃ decoder : ParentCarrier → Complete.Carrier depth, ∀ index : Fin (collisionBound owner + 1),
      decoder (snapshot (collisionBound owner) index) = read depth (collisionBound owner) index := by
  rintro ⟨decoder, reconstruct⟩
  have compressed := congrArg decoder (actual_snapshot_collision owner)
  rw [reconstruct, reconstruct] at compressed
  exact collision_indices_distinct owner (read_injective depth (collisionBound owner) compressed)

end
end SourceGeneratedActionWords.Fock.Dynamic.Hilbert
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
