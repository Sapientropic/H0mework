import H0mework.Versions.X.Fock.PrimeFieldCalculation.InventoryConsumer
import H0mework.Versions.X.Probability.Recovery.Refinement

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFixedInventoryRecovery

open SourceGeneratedActionObservationHistory SourcePrimeHistoryRecovery
open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceWeightedRecovery SourceConditionalInventory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

abbrev Observation (width : Nat) := Fin (width + 1) → IntegralOneParticle

local instance observationMeasurable (width : Nat) : MeasurableSpace (Observation width) := ⊤

def query (runtime : LivingRuntimeState process) (width : Nat) :
    Fin (inventoryBound runtime + 1) → Observation width :=
  FiniteRecurrence.Native.query (process := process) rawField width runtimeSeed (inventoryBound runtime)

theorem restriction_query (runtime : LivingRuntimeState process) (width : Nat) :
    (prefixRestriction (R := ℤ) (B := IntegralOneParticle) width) ∘ query runtime (width + 1) = query runtime width := rfl

def costAt (runtime : LivingRuntimeState process) (width : Nat) : ℝ :=
  cost (inventoryBound runtime) (query runtime width)

theorem task_refinement (runtime : LivingRuntimeState process) (width : Nat)
    (task : Fin (inventoryBound runtime + 1) → ℂ) :
    error (historyPMF (inventoryBound runtime)) (query runtime width) task
        (optimalDecoder (historyPMF (inventoryBound runtime)) (query runtime width) task) =
      error (historyPMF (inventoryBound runtime)) (query runtime (width + 1)) task
        (optimalDecoder (historyPMF (inventoryBound runtime)) (query runtime (width + 1)) task) +
      error (historyPMF (inventoryBound runtime)) (query runtime width)
        (fun index => optimalDecoder (historyPMF (inventoryBound runtime)) (query runtime (width + 1)) task
          (query runtime (width + 1) index))
        (optimalDecoder (historyPMF (inventoryBound runtime)) (query runtime width) task) := by
  simpa only [restriction_query] using ObservationRefinement.optimal_gain
    (historyPMF (inventoryBound runtime)) (query runtime (width + 1))
    (prefixRestriction (R := ℤ) (B := IntegralOneParticle) width) task

theorem cost_refinement (runtime : LivingRuntimeState process) (width : Nat) :
    costAt runtime width = costAt runtime (width + 1) +
      ∑ actor : Fin (inventoryBound runtime + 1),
        error (historyPMF (inventoryBound runtime)) (query runtime width)
          (fun index => optimalDecoder (historyPMF (inventoryBound runtime)) (query runtime (width + 1))
            (fun point => (unitTask (inventoryBound runtime) actor point : ℂ))
            (query runtime (width + 1) index))
          (optimalDecoder (historyPMF (inventoryBound runtime)) (query runtime width)
            (fun point => (unitTask (inventoryBound runtime) actor point : ℂ))) := by
  have generated := Finset.sum_congr (s₁ := Finset.univ) rfl
    (fun actor _ => task_refinement runtime width (fun point => (unitTask (inventoryBound runtime) actor point : ℂ)))
  simp_rw [optimal_attains] at generated
  rw [Finset.sum_add_distrib] at generated
  exact generated

theorem cost_antitone (runtime : LivingRuntimeState process) : Antitone (costAt runtime) := by
  apply antitone_nat_of_succ_le
  intro width
  rw [cost_refinement runtime width]
  apply le_add_of_nonneg_right
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)

end
end SourceFixedInventoryRecovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
