import H0mework.Probability.Recovery.AtomicTransfer
import H0mework.Fock.HistoryModel.RecordedTransfer
import H0mework.Fock.HistoryModel.OriginalHilbertRecovery

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedAtomicObservation.Recorded

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceGeneratedActionWords.Fock.OriginalHilbert SourceGeneratedActionWords.Fock.OriginalHilbert.Recorded
open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability SourcePrimeHistoryRecovery SourcePrimeCalculation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

local instance recordedAtomicUniform (depth : Nat) : UniformSpace (Field nativeStep (rawWords depth)) :=
  fieldUniform nativeStep (rawWords depth)
local instance recordedAtomicMeasurable (depth : Nat) : MeasurableSpace (Field nativeStep (rawWords depth)) :=
  fieldBorel nativeStep (rawWords depth)
local instance recordedAtomicBorel (depth : Nat) : BorelSpace (Field nativeStep (rawWords depth)) := ⟨rfl⟩
local instance recordedAtomicT2 (depth : Nat) : T2Space (Field nativeStep (rawWords depth)) :=
  Actor.conditionalFieldT2 depth

theorem recorded_mass (depth bound : Nat) (actor : Fin (bound + 1)) :
    fieldPMF nativeStep (rawWords depth) (nativeStep CanonicalUnitArithmeticRoot.initialCurrent) bound
        (whole depth bound (recordedQuery bound actor)) = ((bound + 1 : Nat) : ENNReal)⁻¹ := by
  have supported : Actor.nextRead depth bound actor ∈
      (observed (historyPMF bound) (Actor.nextRead depth bound)).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨actor, by simp [historyPMF], rfl⟩
  have weighted := SourceConditionalHistory.weighted_conditional (historyPMF bound) (Actor.nextRead depth bound)
    (Actor.nextRead depth bound actor) supported actor
  rw [next_posterior depth bound actor supported, PMF.pure_apply_self, mul_one, if_pos rfl] at weighted
  rw [whole_recorded, ← Actor.next_pmf]
  exact weighted.trans (historyPMF_apply bound actor)

theorem recorded_supported (depth bound : Nat) (actor : Fin (bound + 1)) :
    whole depth bound (recordedQuery bound actor) ∈
      (fieldPMF nativeStep (rawWords depth) (nativeStep CanonicalUnitArithmeticRoot.initialCurrent) bound).support := by
  change _ ≠ 0
  rw [recorded_mass]
  exact ENNReal.inv_ne_zero.mpr (by simp)

def query (depth bound : Nat) (actor : Fin (bound + 1)) :
    SourceOwnedObservationHistory.Space nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent bound →L[ℂ] ℂ :=
  (evalAtContinuous
    (fieldPMF nativeStep (rawWords depth) (nativeStep CanonicalUnitArithmeticRoot.initialCurrent) bound)
    (whole depth bound (recordedQuery bound actor)) (recorded_supported depth bound actor)).comp
      (IsometricRetainedTransfer.transfer
        (SourceOwnedObservationHistory.pullback nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent bound))

theorem query_read (depth bound : Nat) (actor : Fin (bound + 1))
    (value : SourceOwnedObservationHistory.Space nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent bound) :
    query depth bound actor value =
      decoder sourceOwner bound (fun index => value (Actor.originalRead depth bound index)) (recordedQuery bound actor) :=
  original_field_transfer_on_record depth bound value actor

theorem query_norm (depth bound : Nat) (actor : Fin (bound + 1)) :
    ‖query depth bound actor‖ = Real.sqrt ((bound + 1 : Nat) : ℝ) := by
  have actual := source_query_norm
    (fieldPMF nativeStep (rawWords depth) (nativeStep CanonicalUnitArithmeticRoot.initialCurrent) bound)
    (whole depth bound (recordedQuery bound actor)) (recorded_supported depth bound actor)
    (SourceOwnedObservationHistory.pullback nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent bound)
  change ‖query depth bound actor‖ = _ at actual
  rw [recorded_mass, ENNReal.toReal_inv, ENNReal.toReal_natCast, Real.sqrt_inv, one_div, inv_inv] at actual
  exact actual

end
end SourceGeneratedAtomicObservation.Recorded
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
