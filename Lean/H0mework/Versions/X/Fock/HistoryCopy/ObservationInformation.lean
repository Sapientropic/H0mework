import H0mework.Versions.X.Fock.HistoryCopy.ObservationSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyObservation

open SourceWeightedRecovery SourceConditionalInventory SourceUniformFibreVariance
open SourceGeneratedRuntimeHistoryProbability SourceConditionalHistory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open scoped Classical
noncomputable section

local instance informationParentMeasurable : MeasurableSpace ParentCarrier := ⊤

theorem task_gain (depth bound : Nat) (index : Index depth) (task : Fin (bound + 1) → ℂ) :
    error (historyPMF bound) (before depth bound) task (optimalDecoder (historyPMF bound) (before depth bound) task) =
      error (historyPMF bound) (joint depth bound index) task (optimalDecoder (historyPMF bound) (joint depth bound index) task) +
      error (historyPMF bound) (before depth bound)
        (fun actor => optimalDecoder (historyPMF bound) (joint depth bound index) task (joint depth bound index actor))
        (optimalDecoder (historyPMF bound) (before depth bound) task) := by
  simpa only [joint_before] using ObservationRefinement.optimal_gain
    (historyPMF bound) (joint depth bound index) Prod.fst task

theorem inventory_gain (depth bound : Nat) (index : Index depth) :
    cost bound (before depth bound) = cost bound (joint depth bound index) +
      ∑ actor : Fin (bound + 1), error (historyPMF bound) (before depth bound)
        (fun point => optimalDecoder (historyPMF bound) (joint depth bound index)
          (fun original => (unitTask bound actor original : ℂ)) (joint depth bound index point))
        (optimalDecoder (historyPMF bound) (before depth bound) (fun original => (unitTask bound actor original : ℂ))) := by
  have generated := Finset.sum_congr (s₁ := Finset.univ) rfl
    (fun actor _ => task_gain depth bound index (fun original => (unitTask bound actor original : ℂ)))
  simp_rw [optimal_attains] at generated
  rw [Finset.sum_add_distrib] at generated
  exact generated

theorem joint_improves (depth bound : Nat) (index : Index depth) :
    cost bound (joint depth bound index) ≤ cost bound (before depth bound) := by
  rw [inventory_gain depth bound index]
  apply le_add_of_nonneg_right
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)

theorem recovered_distinctions (depth bound : Nat) (index : Index depth) :
    cost bound (before depth bound) - cost bound (joint depth bound index) =
      ((outputs bound (joint depth bound index)).card : ℝ) - (outputs bound (before depth bound)).card := by
  rw [cost_eq, cost_eq]
  ring

theorem complete_conditional (depth bound : Nat) (index : Index depth) (value : ParentCarrier)
    (supported : value ∈ (SourceConditionalHistory.observed (SourceConditionalHistory.observed (historyPMF bound) (joint depth bound index)) Prod.fst).support) :
    ∃ originalSupported : value ∈ (SourceConditionalHistory.observed (historyPMF bound) (before depth bound)).support,
      Coarsening.mixture (historyPMF bound) (joint depth bound index) Prod.fst value supported =
        conditional (historyPMF bound) (before depth bound) value originalSupported := by
  simpa only [joint_before] using Coarsening.mixture_is_conditional
    (historyPMF bound) (joint depth bound index) Prod.fst value supported

theorem conditional_information (depth bound : Nat) (index : Index depth) :
    cost bound (joint depth bound index) / (bound + 1 : ℝ) ≤
      SourceUniformFibreInformation.conditionalEntropy bound (joint depth bound index) :=
  information_cost bound (joint depth bound index)

end
end SourceCopyObservation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
