import H0mework.Probability.Information.InventoryInformation
import H0mework.Fock.PrimeField.InformationInventory
import H0mework.Fock.PrimeFieldJoint.BornConsumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedConditionalInventory

open SourceConditionalInventory SourceUniformFibreVariance SourceGeneratedRuntimeHistoryProbability
open SourcePrimeHistoryRecovery
open NoIslandNoMagic.CanonicalArithmeticState ParticleWaveFock ParticleWaveFockRuntime
open SourceGeneratedActionWords.Fock.OriginalHilbert
open scoped Classical
noncomputable section

local instance : MeasurableSpace IntegralOneParticle := ⊤

theorem snapshot_source (depth bound : Nat) (actor : Fin (bound + 1)) :
    thetaProjection (inputSnapshot depth (Actor.originalRead depth bound actor)) = rawField actor.val := by
  rw [input_snapshot_actual]
  change thetaProjection (secondQuantizedState (rawField actor.val)) = rawField actor.val
  simp only [secondQuantizedState, map_add, thetaProjection_diagonalInclusion]
  change rawField actor.val + 0 = rawField actor.val
  exact add_zero _

theorem original_decoder_lower (depth bound : Nat) (decoder : Fin (bound + 1) → IntegralOneParticle → ℂ) :
    snapshotCost bound ≤
      ∑ actor, SourceWeightedRecovery.error (historyPMF bound) (Actor.originalRead depth bound)
        (fun index => (unitTask bound actor index : ℂ))
        (fun value => decoder actor (thetaProjection (inputSnapshot depth value))) := by
  have generated := all_decoder_lower bound (fun index => rawField index.val) decoder
  rw [← cost_eq] at generated
  simpa only [SourceWeightedRecovery.error, snapshot_source, snapshotCost] using generated

theorem snapshot_information (bound : Nat) :
    snapshotCost bound / (bound + 1 : ℝ) ≤
      SourceUniformFibreInformation.conditionalEntropy bound (fun index => rawField index.val) :=
  information_cost bound (fun index => rawField index.val)

end
end SourceGeneratedConditionalInventory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
