import H0mework.Versions.X.Fock.HistoryModel.OriginalHilbertInverse

/-! The already generated old-word restriction is the same source map inside the original native fields. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionWords.Fock.OriginalHilbert

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed MeasureTheory

noncomputable section

local instance dictionaryFieldMeasurable (depth : Nat) : MeasurableSpace (Field nativeStep (rawWords depth)) :=
  fieldBorel nativeStep (rawWords depth)
local instance dictionaryWordsMeasurable (depth : Nat) : MeasurableSpace (Complete.Carrier depth) := Dynamic.Hilbert.measurable depth

def dictionary (depth : Nat) : Field nativeStep (rawWords (depth + 1)) →ₗ[ℤ] Field nativeStep (rawWords depth) :=
  (originalField depth).toLinearMap.comp ((Dynamic.previous depth).comp (originalField (depth + 1)).symm.toLinearMap)

theorem dictionary_original (depth : Nat) (value : Complete.Carrier (depth + 1)) :
    dictionary depth (originalField (depth + 1) value) = originalField depth (Dynamic.previous depth value) := by
  change originalField depth (Dynamic.previous depth ((originalField (depth + 1)).symm (originalField (depth + 1) value))) = _
  rw [LinearEquiv.symm_apply_apply]

theorem dictionary_point (depth : Nat) (current : Current) :
    dictionary depth (fieldPoint nativeStep (rawWords (depth + 1)) current) = fieldPoint nativeStep (rawWords depth) current := by
  rw [← original_point, dictionary_original, Dynamic.previous_point, original_point]

theorem dictionary_action (depth : Nat) (value : Field nativeStep (rawWords (depth + 1))) :
    dictionary depth (fieldAction nativeStep (rawWords (depth + 1)) value) =
      fieldAction nativeStep (rawWords depth) (dictionary depth value) := by
  obtain ⟨word, rfl⟩ := (originalField (depth + 1)).surjective value
  rw [← original_action]
  simp only [dictionary_original]
  exact (congrArg (originalField depth) (Dynamic.previous_action depth (.inl ()) word)).trans
    (original_action depth (Dynamic.previous depth word))

theorem dictionary_measurable (depth : Nat) : Measurable (dictionary depth) :=
  (original_measurable depth).comp ((Dynamic.Hilbert.previous_measurable depth).comp
    (originalMeasurableEquiv (depth + 1)).symm.measurable)

theorem dictionary_pmf (depth : Nat) (current : Current) (bound : Nat) :
    (fieldPMF nativeStep (rawWords (depth + 1)) current bound).map (dictionary depth) =
      fieldPMF nativeStep (rawWords depth) current bound := by
  rw [fieldPMF, PMF.map_comp]
  exact congrArg (fun reader : Current → Field nativeStep (rawWords depth) => (statePMF nativeStep current bound).map reader)
    (funext (dictionary_point depth))

theorem dictionary_preserving (depth : Nat) (current : Current) (bound : Nat) :
    MeasurePreserving (dictionary depth) (empirical nativeStep (rawWords (depth + 1)) current bound).toMeasure
      (empirical nativeStep (rawWords depth) current bound).toMeasure :=
  ⟨dictionary_measurable depth, (PMF.toMeasure_map _ _ (dictionary_measurable depth)).trans
    (congrArg PMF.toMeasure (dictionary_pmf depth current bound))⟩

def dictionaryPullback (depth : Nat) (current : Current) (bound : Nat) :
    SourceOwnedObservationHistory.Space nativeStep (rawWords depth) current bound →ₗᵢ[ℂ]
      SourceOwnedObservationHistory.Space nativeStep (rawWords (depth + 1)) current bound :=
  Lp.compMeasurePreservingₗᵢ ℂ (dictionary depth) (dictionary_preserving depth current bound)

end
end SourceGeneratedActionWords.Fock.OriginalHilbert
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
