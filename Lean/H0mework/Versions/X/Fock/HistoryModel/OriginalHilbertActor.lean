import H0mework.Versions.X.Fock.HistoryModel.OriginalHilbertTime

/-! The complete original actor history feeds the existing native time pullback. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionWords.Fock.OriginalHilbert.Actor

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed MeasureTheory
open SourceGeneratedRuntimeHistoryProbability
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

local instance actorFieldUniform (depth : Nat) : UniformSpace (Field nativeStep (rawWords depth)) := fieldUniform nativeStep (rawWords depth)
local instance actorFieldMeasurable (depth : Nat) : MeasurableSpace (Field nativeStep (rawWords depth)) := fieldBorel nativeStep (rawWords depth)
local instance actorFieldBorel (depth : Nat) : BorelSpace (Field nativeStep (rawWords depth)) := ⟨rfl⟩

def originalRead (depth bound : Nat) (index : Fin (bound + 1)) : Field nativeStep (rawWords depth) :=
  originalField depth (Dynamic.Hilbert.read depth bound index)

theorem originalRead_actual (depth bound : Nat) (index : Fin (bound + 1)) :
    originalRead depth bound index = fieldPoint nativeStep (rawWords depth)
      ((runtimeAt index.val).current.visit.current : Current) :=
  original_point depth _

theorem current_pmf (depth bound : Nat) :
    SourceWeightedRecovery.observed (historyPMF bound) (originalRead depth bound) =
      fieldPMF nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent bound := by
  calc
    _ = (Dynamic.Hilbert.law depth bound).map (originalField depth) :=
      (PMF.map_comp (Dynamic.Hilbert.read depth bound) (historyPMF bound) (originalField depth)).symm
    _ = (wordLaw depth CanonicalUnitArithmeticRoot.initialCurrent bound).map (originalField depth) :=
      congrArg (fun law => law.map (originalField depth)) (wordLaw_initial depth bound).symm
    _ = _ := original_pmf depth CanonicalUnitArithmeticRoot.initialCurrent bound

theorem current_preserving (depth bound : Nat) :
    MeasurePreserving (originalRead depth bound) (historyPMF bound).toMeasure
      (empirical nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent bound).toMeasure :=
  ⟨measurable_of_finite _, (PMF.toMeasure_map _ _ (measurable_of_finite _)).trans
    (congrArg PMF.toMeasure (current_pmf depth bound))⟩

def currentPullback (depth bound : Nat) :
    SourceOwnedObservationHistory.Space nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent bound →ₗᵢ[ℂ]
      SourceWeightedRecovery.Space (historyPMF bound) :=
  Lp.compMeasurePreservingₗᵢ ℂ (originalRead depth bound) (current_preserving depth bound)

theorem currentPullback_at (depth bound : Nat)
    (value : SourceOwnedObservationHistory.Space nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent bound)
    (index : Fin (bound + 1)) :
    currentPullback depth bound value index = value (originalRead depth bound index) :=
  SourceWeightedRecovery.ae_at_support (historyPMF bound) index (by simp [historyPMF])
    (Lp.coeFn_compMeasurePreserving value (current_preserving depth bound))

abbrev currentTransfer (depth bound : Nat) := IsometricRetainedTransfer.transfer (currentPullback depth bound)

def nextRead (depth bound : Nat) : Fin (bound + 1) → Field nativeStep (rawWords depth) :=
  fieldAction nativeStep (rawWords depth) ∘ originalRead depth bound

theorem next_pmf (depth bound : Nat) :
    SourceWeightedRecovery.observed (historyPMF bound) (nextRead depth bound) =
      fieldPMF nativeStep (rawWords depth) (nativeStep CanonicalUnitArithmeticRoot.initialCurrent) bound := by
  calc
    _ = (SourceWeightedRecovery.observed (historyPMF bound) (originalRead depth bound)).map
        (fieldAction nativeStep (rawWords depth)) :=
      (PMF.map_comp (originalRead depth bound) (historyPMF bound) (fieldAction nativeStep (rawWords depth))).symm
    _ = (fieldPMF nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent bound).map
        (fieldAction nativeStep (rawWords depth)) :=
      congrArg (fun law => law.map (fieldAction nativeStep (rawWords depth))) (current_pmf depth bound)
    _ = _ := fieldPMF_action nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent bound

theorem next_preserving (depth bound : Nat) :
    MeasurePreserving (nextRead depth bound) (historyPMF bound).toMeasure
      (empirical nativeStep (rawWords depth) (nativeStep CanonicalUnitArithmeticRoot.initialCurrent) bound).toMeasure :=
  (SourceOwnedObservationHistory.source_measurePreserving nativeStep (rawWords depth)
    CanonicalUnitArithmeticRoot.initialCurrent bound).comp (current_preserving depth bound)

abbrev nextPullback (depth bound : Nat) := (currentPullback depth bound).comp
  (SourceOwnedObservationHistory.pullback nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent bound)

theorem nextPullback_is_source_map (depth bound : Nat) :
    nextPullback depth bound = Lp.compMeasurePreservingₗᵢ ℂ (nextRead depth bound) (next_preserving depth bound) := by
  apply LinearIsometry.ext
  intro value
  exact (Lp.compMeasurePreserving_comp_apply value
    (SourceOwnedObservationHistory.source_measurePreserving nativeStep (rawWords depth)
      CanonicalUnitArithmeticRoot.initialCurrent bound) (current_preserving depth bound)).symm

theorem nextPullback_at (depth bound : Nat)
    (value : SourceOwnedObservationHistory.Space nativeStep (rawWords depth)
      (nativeStep CanonicalUnitArithmeticRoot.initialCurrent) bound) (index : Fin (bound + 1)) :
    nextPullback depth bound value index = value (nextRead depth bound index) := by
  rw [nextPullback_is_source_map]
  exact SourceWeightedRecovery.ae_at_support (historyPMF bound) index (by simp [historyPMF])
    (Lp.coeFn_compMeasurePreserving value (next_preserving depth bound))

end
end SourceGeneratedActionWords.Fock.OriginalHilbert.Actor
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
