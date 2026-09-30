import H0mework.Versions.X.Fock.CopyGraph.FutureAcquisitionEffect

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyFutureAcquisition

open SourceCopyProgram (Index)
open SourceCopyTimeModel (time)
open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical InnerProductSpace
noncomputable section

theorem old_pairing_zero (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (actor : Fin (inventoryBound runtime + steps + 1)) :
    ⟪SourceColumnForcing.column (inventoryBound runtime) index actor.val, arrival runtime index steps⟫_ℂ = 0 := by
  rw [arrival, SourceCopyRecordedRecurrence.hidden, SourceCopyRecordedRecurrence.difference_time]
  exact SourceCopyRecordedRecurrence.column_difference runtime index steps _ actor

theorem acquired_samples (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (actor : Fin (inventoryBound runtime + steps + 1 + 1)) :
    SourceColumnForcing.samples (inventoryBound runtime) (inventoryBound runtime + steps + 1) index (arrival runtime index steps) actor =
      (Real.sqrt ((inventoryBound runtime + steps + 1 : Nat) + 1 : ℝ) : ℂ) *
        (Finsupp.single (inventoryBound runtime + steps + 1) (1 : ℂ)) actor.val := by
  rw [SourceColumnForcing.samples]
  by_cases newest : actor.val = inventoryBound runtime + steps + 1
  · rw [newest, acquired_pairing, Finsupp.single_eq_same]
    simp only [SourceHistoryWord.coefficient_scale, one_div, Complex.ofReal_inv, inv_inv, mul_one]
  · have inside : actor.val < inventoryBound runtime + steps + 1 := by omega
    have old := old_pairing_zero runtime index steps ⟨actor.val, inside⟩
    rw [old, zero_div, Finsupp.single_eq_of_ne newest, mul_zero]

universe u
variable {Observed : Type u} [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

omit [MeasurableSingletonClass Observed] in
theorem acquired_forcing (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (query : Fin (inventoryBound runtime + steps + 1 + 1) → Observed) :
    SourceColumnForcing.forcing (inventoryBound runtime) (inventoryBound runtime + steps + 1) index query (arrival runtime index steps) =
      transfer (historyPMF (inventoryBound runtime + steps + 1)) query
        (SourceHistoryWord.lift (inventoryBound runtime + steps + 1)
          (Finsupp.single (inventoryBound runtime + steps + 1) (1 : ℂ))) := by
  have samples := funext (acquired_samples runtime index steps)
  rw [SourceColumnForcing.forcing, samples]
  rfl

theorem acquired_conditional (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (query : Fin (inventoryBound runtime + steps + 1 + 1) → Observed) (atom : Observed)
    (supported : atom ∈ (observed (historyPMF (inventoryBound runtime + steps + 1)) query).support) :
    SourceColumnForcing.forcing (inventoryBound runtime) (inventoryBound runtime + steps + 1) index query
        (arrival runtime index steps) atom =
      conditionalMean (historyPMF (inventoryBound runtime + steps + 1)) query
        (fun actor => (Real.sqrt ((inventoryBound runtime + steps + 1 : Nat) + 1 : ℝ) : ℂ) *
          (Finsupp.single (inventoryBound runtime + steps + 1) (1 : ℂ)) actor.val) atom supported := by
  rw [SourceColumnForcing.forcing_conditional]
  exact congrArg (fun samples => conditionalMean (historyPMF (inventoryBound runtime + steps + 1)) query samples atom supported)
    (funext (acquired_samples runtime index steps))

end
end SourceCopyFutureAcquisition
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
