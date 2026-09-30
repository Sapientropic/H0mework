import H0mework.Versions.X.Fock.HistoryModel.OriginalHilbertField
import H0mework.Versions.X.Fock.HistoryModel.DynamicHilbertMeasure

/-! The same observer identity sends the complete word law to the original empirical measure. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionWords.Fock.OriginalHilbert

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed MeasureTheory

noncomputable section

local instance (depth : Nat) : UniformSpace (Complete.Carrier depth) := Dynamic.Hilbert.uniform depth
local instance (depth : Nat) : MeasurableSpace (Complete.Carrier depth) := Dynamic.Hilbert.measurable depth
local instance (depth : Nat) : BorelSpace (Complete.Carrier depth) := ⟨rfl⟩
local instance (depth : Nat) : T2Space (Complete.Carrier depth) := Dynamic.Hilbert.field_t2 depth
local instance (depth : Nat) : UniformSpace (Field nativeStep (rawWords depth)) := fieldUniform nativeStep (rawWords depth)
local instance (depth : Nat) : MeasurableSpace (Field nativeStep (rawWords depth)) := fieldBorel nativeStep (rawWords depth)
local instance (depth : Nat) : BorelSpace (Field nativeStep (rawWords depth)) := ⟨rfl⟩

theorem original_measurable (depth : Nat) : Measurable (originalField depth) := by
  have same : @UniformContinuous (Complete.Carrier depth) (Field nativeStep (rawWords depth))
      (Dynamic.Hilbert.uniform depth) (fieldUniform nativeStep (rawWords depth)) (originalField depth) := original_uniform depth
  exact same.continuous.borel_measurable

def wordLaw (depth : Nat) (current : Current) (bound : Nat) : PMF (Complete.Carrier depth) :=
  (statePMF nativeStep current bound).map (Complete.point depth)

theorem wordLaw_initial (depth bound : Nat) :
    wordLaw depth CanonicalUnitArithmeticRoot.initialCurrent bound = Dynamic.Hilbert.law depth bound :=
  (Dynamic.Hilbert.original_law depth bound).symm

theorem original_pmf (depth : Nat) (current : Current) (bound : Nat) :
    (wordLaw depth current bound).map (originalField depth) = fieldPMF nativeStep (rawWords depth) current bound := by
  rw [wordLaw, PMF.map_comp]
  exact congrArg (fun reader : Current → Field nativeStep (rawWords depth) => (statePMF nativeStep current bound).map reader)
    (funext (original_point depth))

theorem original_preserving (depth : Nat) (current : Current) (bound : Nat) :
    MeasurePreserving (originalField depth) (wordLaw depth current bound).toMeasure
      (empirical nativeStep (rawWords depth) current bound).toMeasure :=
  ⟨original_measurable depth, (PMF.toMeasure_map _ _ (original_measurable depth)).trans
    (congrArg PMF.toMeasure (original_pmf depth current bound))⟩

def fieldPullback (depth : Nat) (current : Current) (bound : Nat) :
    SourceOwnedObservationHistory.Space nativeStep (rawWords depth) current bound →ₗᵢ[ℂ]
      SourceWeightedRecovery.Space (wordLaw depth current bound) :=
  Lp.compMeasurePreservingₗᵢ ℂ (originalField depth) (original_preserving depth current bound)

theorem fieldPullback_ae (depth : Nat) (current : Current) (bound : Nat)
    (value : SourceOwnedObservationHistory.Space nativeStep (rawWords depth) current bound) :
    fieldPullback depth current bound value =ᵐ[(wordLaw depth current bound).toMeasure]
      value ∘ originalField depth :=
  Lp.coeFn_compMeasurePreserving value (original_preserving depth current bound)

end
end SourceGeneratedActionWords.Fock.OriginalHilbert
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
