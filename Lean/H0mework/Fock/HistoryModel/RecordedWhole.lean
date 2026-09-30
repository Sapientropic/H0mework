import H0mework.Fock.HistoryModel.RecordedSource
import H0mework.Fock.HistoryModel.RecordedQuery

/-! The finite actual record generates the original whole word-field point and its complete native output law. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionWords.Fock.OriginalHilbert.Recorded

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceGeneratedActionObservationHistory SourcePrimeHistoryRecovery SourcePrimeCalculation
open SourceGeneratedRuntimeHistoryProbability
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

def whole (depth bound : Nat) : Raw sourceOwner bound →ₗ[ℤ] Field nativeStep (rawWords depth) :=
  (sourceMap (sourceAction nativeStep) (observation (rawWords depth))).comp (sourceWord bound)

theorem whole_recorded (depth bound : Nat) (actor : Fin (bound + 1)) :
    whole depth bound (recordedQuery bound actor) = Actor.nextRead depth bound actor := by
  let current : Current := (runtimeAt (actor.val + 1)).current.visit.current
  have source := congrArg (sourceMap (sourceAction nativeStep) (observation (rawWords depth)))
    (sourceWord_actual_point bound actor)
  exact source.trans ((next_read_actual depth bound actor).trans (original_point depth current)).symm

theorem whole_recorded_fibre (depth bound : Nat) (left right : Fin (bound + 1)) :
    recordedQuery bound left = recordedQuery bound right ↔ Actor.nextRead depth bound left = Actor.nextRead depth bound right := by
  constructor
  · intro same
    have generated := congrArg (whole depth bound) same
    simpa only [whole_recorded] using generated
  · intro same
    have generated := congrArg (recordedRestriction depth bound) same
    simpa only [recordedRestriction_nextRead] using generated

theorem whole_pmf (depth bound : Nat) :
    ((historyPMF bound).map (recordedQuery bound)).map (whole depth bound) =
      fieldPMF nativeStep (rawWords depth) (nativeStep CanonicalUnitArithmeticRoot.initialCurrent) bound :=
  (PMF.map_comp (recordedQuery bound) (historyPMF bound) (whole depth bound)).trans
    ((congrArg (fun reader : Fin (bound + 1) → Field nativeStep (rawWords depth) => (historyPMF bound).map reader)
      (funext (whole_recorded depth bound))).trans (Actor.next_pmf depth bound))

theorem whole_on_actual_support (depth bound : Nat) (value : Field nativeStep (rawWords depth))
    (supported : value ∈ (fieldPMF nativeStep (rawWords depth) (nativeStep CanonicalUnitArithmeticRoot.initialCurrent) bound).support) :
    whole depth bound (recordedRestriction depth bound value) = value := by
  rw [← Actor.next_pmf] at supported
  obtain ⟨actor, _, rfl⟩ := (PMF.mem_support_map_iff (Actor.nextRead depth bound) (historyPMF bound) value).mp supported
  rw [recordedRestriction_nextRead, whole_recorded]

end
end SourceGeneratedActionWords.Fock.OriginalHilbert.Recorded
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
