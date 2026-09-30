import H0mework.Fock.HistoryModel.RecordedWhole
import H0mework.Fock.PrimeFieldCalculation.CalculationConditional

/-! The recorded whole-word fibre generates the original time transfer from actual source births. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionWords.Fock.OriginalHilbert.Recorded

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceGeneratedActionObservationHistory SourceGeneratedRuntimeHistoryProbability
open SourcePrimeHistoryRecovery SourcePrimeCalculation SourceWeightedRecovery
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

local instance recordedConditionalFieldMeasurable (depth : Nat) :
    MeasurableSpace (Field nativeStep (rawWords depth)) := fieldBorel nativeStep (rawWords depth)

theorem next_conditional_recorded (depth bound : Nat) (actor : Fin (bound + 1))
    (supported : Actor.nextRead depth bound actor ∈
      (observed (historyPMF bound) (Actor.nextRead depth bound)).support) :
    SourceConditionalHistory.conditional (historyPMF bound) (Actor.nextRead depth bound)
        (Actor.nextRead depth bound actor) supported =
      FiniteRecurrence.Native.conditional (process := process) rawField
        (windowBound sourceOwner bound) runtimeSeed bound actor := by
  have sameFibre :
      {candidate | Actor.nextRead depth bound candidate = Actor.nextRead depth bound actor} =
        {candidate | observe sourceOwner bound candidate = observe sourceOwner bound actor} := by
    ext candidate
    change Actor.nextRead depth bound candidate = Actor.nextRead depth bound actor ↔
      observe sourceOwner bound candidate = observe sourceOwner bound actor
    have generated := (whole_recorded_fibre depth bound candidate actor).symm
    simpa only [recorded_is_query] using generated
  unfold FiniteRecurrence.Native.conditional SourceConditionalHistory.conditional
  congr 1

theorem original_transfer_from_birth (depth bound : Nat) (task : Fin (bound + 1) → ℂ)
    (actor : Fin (bound + 1)) :
    IsometricRetainedTransfer.transfer
        (SourceOwnedObservationHistory.pullback nativeStep (rawWords depth)
          CanonicalUnitArithmeticRoot.initialCurrent bound)
        (Actor.currentTransfer depth bound (taskValue (historyPMF bound) task))
        (Actor.nextRead depth bound actor) = sourceAnswer bound task actor := by
  have supported : Actor.nextRead depth bound actor ∈
      (observed (historyPMF bound) (Actor.nextRead depth bound)).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨actor, by simp [historyPMF], rfl⟩
  rw [Actor.complete_conditional_formula depth bound task _ supported]
  unfold sourceAnswer
  apply Finset.sum_congr rfl
  intro candidate _
  rw [next_conditional_recorded, Complex.real_smul, conditional_weight_is_birth]

theorem original_field_transfer_from_birth (depth bound : Nat)
    (value : SourceOwnedObservationHistory.Space nativeStep (rawWords depth)
      CanonicalUnitArithmeticRoot.initialCurrent bound) (actor : Fin (bound + 1)) :
    IsometricRetainedTransfer.transfer
        (SourceOwnedObservationHistory.pullback nativeStep (rawWords depth)
          CanonicalUnitArithmeticRoot.initialCurrent bound) value (Actor.nextRead depth bound actor) =
      sourceAnswer bound (fun index => value (Actor.originalRead depth bound index)) actor := by
  have supported : Actor.nextRead depth bound actor ∈
      (observed (historyPMF bound) (Actor.nextRead depth bound)).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨actor, by simp [historyPMF], rfl⟩
  rw [Actor.original_transfer_formula depth bound value _ supported]
  unfold sourceAnswer
  apply Finset.sum_congr rfl
  intro candidate _
  rw [next_conditional_recorded, Complex.real_smul, conditional_weight_is_birth]

end
end SourceGeneratedActionWords.Fock.OriginalHilbert.Recorded
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
