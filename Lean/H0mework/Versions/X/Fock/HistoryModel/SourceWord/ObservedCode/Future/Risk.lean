import H0mework.Versions.X.Fock.HistoryModel.SourceWord.ObservedCode.Future.Kernel

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWordFutureBit

open SourceGeneratedActionWords
open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceConditionalModel (Actors)
open SourceGeneratedAcquisitionContinuation ArithmeticGeneration
open SourceGeneratedRuntimeHistoryProbability
open scoped Classical
open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
noncomputable section

/-- A future-reader's decoder is charged against the original acted-G effect
with the original source weights. -/
def futureRisk (runtime : LivingRuntimeState process)
    (word : List (Fock.Letter (inventoryBound runtime + 1)))
    (decoder : (List (Fock.Letter (inventoryBound runtime + 1)) → ZMod 2) →
      SourceJointClockGraph.Carrier) : ℝ :=
  ∑ actor : Actors runtime, (historyPMF (inventoryBound runtime) actor).toReal *
    ‖SourceCompiledGWord.image runtime (inventoryBound runtime + 1) word actor -
      decoder (futureRead runtime word actor)‖ ^ 2

theorem future_risk_eq_bit (runtime : LivingRuntimeState process)
    (word : List (Fock.Letter (inventoryBound runtime + 1)))
    (decoder : (List (Fock.Letter (inventoryBound runtime + 1)) → ZMod 2) →
      SourceJointClockGraph.Carrier) :
    futureRisk runtime word decoder =
      SourceWordCodeRisk.risk runtime word
        (SourceWordObservedCode.encodeObserved runtime word)
        (fun bit => decoder (fun tail => bitWord (inventoryBound runtime + 1) tail bit)) := by
  rw [SourceWordCodeRisk.risk_eq]
  unfold futureRisk
  apply Finset.sum_congr rfl
  intro actor _
  rw [SourceWordObservedCode.query_actual, future_read_bit]

theorem actual_future_half_risk
    (word : List (Fock.Letter (inventoryBound (runtimeAt 3) + 1)))
    (decoder : (List (Fock.Letter (inventoryBound (runtimeAt 3) + 1)) → ZMod 2) →
      SourceJointClockGraph.Carrier) :
    (1 / 2 : ℝ) ≤ futureRisk (runtimeAt 3) word decoder := by
  rw [future_risk_eq_bit]
  exact SourceWordObservedCode.actual_observed_half_risk word _


end
end SourceWordFutureBit
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
