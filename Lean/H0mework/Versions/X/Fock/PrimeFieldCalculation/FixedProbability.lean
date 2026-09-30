import H0mework.Versions.X.Fock.PrimeFieldCalculation.FixedMaterial

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFixedInventoryRecovery

open SourceGeneratedActionObservationHistory SourceConditionalHistory
open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceUniformFibreVariance SourceConditionalInventory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

local instance probabilityObservationMeasurable (width : Nat) : MeasurableSpace (Observation width) := ⊤

theorem complete_conditional (runtime : LivingRuntimeState process) (width : Nat) (value : Observation width)
    (supported : value ∈ (observed (observed (historyPMF (inventoryBound runtime)) (query runtime (width + 1)))
      (prefixRestriction (R := ℤ) (B := IntegralOneParticle) width)).support) :
    ∃ originalSupported : value ∈ (observed (historyPMF (inventoryBound runtime)) (query runtime width)).support,
      Coarsening.mixture (historyPMF (inventoryBound runtime)) (query runtime (width + 1))
        (prefixRestriction (R := ℤ) (B := IntegralOneParticle) width) value supported =
      conditional (historyPMF (inventoryBound runtime)) (query runtime width) value originalSupported := by
  simpa only [restriction_query] using Coarsening.mixture_is_conditional
    (historyPMF (inventoryBound runtime)) (query runtime (width + 1))
    (prefixRestriction (R := ℤ) (B := IntegralOneParticle) width) value supported

theorem recovered_distinctions (runtime : LivingRuntimeState process) (width : Nat) :
    costAt runtime width - costAt runtime (width + 1) =
      ((outputs (inventoryBound runtime) (query runtime (width + 1))).card : ℝ) -
        (outputs (inventoryBound runtime) (query runtime width)).card := by
  unfold costAt
  rw [cost_eq, cost_eq]
  ring

end
end SourceFixedInventoryRecovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
