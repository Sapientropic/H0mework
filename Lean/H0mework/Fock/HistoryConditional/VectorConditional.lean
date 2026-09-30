import H0mework.Fock.HistoryConditional.VectorSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalVector

open SourceConditionalModel (Actors NextModel nextRead)
open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
universe u
variable (runtime : LivingRuntimeState process) {Observed : Type u} (read : Actors runtime → Observed)
variable (value : Observed) (supported : value ∈ ((historyPMF (inventoryBound runtime)).map read).support)

abbrev posterior : PMF (Actors runtime) :=
  SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime)) read value supported

def remaining (index : Actors runtime) : SourceJointClockGraph.Carrier :=
  SourceJointClockGraph.action (actor runtime index) - realizeModel runtime (estimate runtime read value supported)

theorem mean_source : realizeModel runtime (estimate runtime read value supported) =
    SourceVectorMoment.mean (posterior runtime read value supported) (SourceJointClockGraph.action ∘ actor runtime) := by
  rw [estimate_realization]
  apply Finset.sum_congr rfl
  intro i _
  rw [realized_next]
  rfl

theorem mean_action : realizeModel runtime (estimate runtime read value supported) =
    SourceJointClockGraph.action (SourceVectorMoment.mean (posterior runtime read value supported) (actor runtime)) := by
  rw [mean_source, SourceVectorMoment.mean_action]

theorem remaining_action (index : Actors runtime) : remaining runtime read value supported index =
    SourceJointClockGraph.action (actor runtime index -
      SourceVectorMoment.mean (posterior runtime read value supported) (actor runtime)) := by
  rw [remaining, mean_action, map_sub]

theorem reconstruction (index : Actors runtime) :
    realizeModel runtime (estimate runtime read value supported) + remaining runtime read value supported index =
      SourceJointClockGraph.action (actor runtime index) := by
  unfold remaining
  abel

theorem error_decomposition (guess : SourceJointClockGraph.Carrier) :
    SourceVectorMoment.error (posterior runtime read value supported)
      (SourceJointClockGraph.action ∘ actor runtime) guess =
      (∑ i, (posterior runtime read value supported i).toReal * ‖remaining runtime read value supported i‖ ^ 2) +
        ‖realizeModel runtime (estimate runtime read value supported) - guess‖ ^ 2 := by
  rw [SourceVectorMoment.error_decomposition]
  simp only [SourceVectorMoment.variance, SourceVectorMoment.error, remaining, mean_source, Function.comp_apply]

theorem unique_optimal (guess : SourceJointClockGraph.Carrier) :
    SourceVectorMoment.error (posterior runtime read value supported)
      (SourceJointClockGraph.action ∘ actor runtime) guess =
        SourceVectorMoment.variance (posterior runtime read value supported)
          (SourceJointClockGraph.action ∘ actor runtime) ↔
      guess = realizeModel runtime (estimate runtime read value supported) := by
  rw [SourceVectorMoment.unique_optimal, mean_source]

theorem variance_action :
    (∑ i, (posterior runtime read value supported i).toReal * ‖remaining runtime read value supported i‖ ^ 2) =
      SourceVectorMoment.variance (posterior runtime read value supported) (actor runtime) := by
  have paid := SourceVectorMoment.constant_mass_variance (posterior runtime read value supported)
    (actor runtime) 1 (actor_mass runtime)
  simpa only [SourceVectorMoment.variance, SourceVectorMoment.error, remaining, mean_source, Function.comp_apply] using paid

theorem scalar_mean (decode : SourceJointClockGraph.Carrier →ₗ[ℂ] ℂ) :
    decode (realizeModel runtime (estimate runtime read value supported)) =
      SourceWeightedRecovery.conditionalMean (historyPMF (inventoryBound runtime)) read
        (decode ∘ realizeModel runtime ∘ nextRead runtime) value supported := by
  rw [estimate_realization]
  simp only [map_sum, map_smul, SourceWeightedRecovery.conditionalMean, Function.comp_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact Complex.real_smul.symm

end
end SourceConditionalVector
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
