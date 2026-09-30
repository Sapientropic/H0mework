import H0mework.Fock.HistoryModel.OriginalHilbertMeasure

/-! The same observer identity has a measurable inverse, so its Hilbert pullback loses no information. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionWords.Fock.OriginalHilbert

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed MeasureTheory

noncomputable section

local instance (depth : Nat) : UniformSpace (Complete.Carrier depth) := Dynamic.Hilbert.uniform depth
local instance (depth : Nat) : MeasurableSpace (Complete.Carrier depth) := Dynamic.Hilbert.measurable depth
local instance (depth : Nat) : UniformSpace (Field nativeStep (rawWords depth)) := fieldUniform nativeStep (rawWords depth)
local instance (depth : Nat) : MeasurableSpace (Field nativeStep (rawWords depth)) := fieldBorel nativeStep (rawWords depth)

def originalMeasurableEquiv (depth : Nat) : Complete.Carrier depth ≃ᵐ Field nativeStep (rawWords depth) where
  toEquiv := (originalField depth).toEquiv
  measurable_toFun := original_measurable depth
  measurable_invFun := by
    have same : @UniformContinuous (Field nativeStep (rawWords depth)) (Complete.Carrier depth)
        (fieldUniform nativeStep (rawWords depth)) (Dynamic.Hilbert.uniform depth) (originalField depth).symm :=
      original_inverse_uniform depth
    exact same.continuous.borel_measurable

theorem inverse_preserving (depth : Nat) (current : Current) (bound : Nat) :
    MeasurePreserving (originalMeasurableEquiv depth).symm
      (empirical nativeStep (rawWords depth) current bound).toMeasure (wordLaw depth current bound).toMeasure :=
  MeasurePreserving.symm (originalMeasurableEquiv depth) (original_preserving depth current bound)

def inversePullback (depth : Nat) (current : Current) (bound : Nat) :
    SourceWeightedRecovery.Space (wordLaw depth current bound) →ₗᵢ[ℂ]
      SourceOwnedObservationHistory.Space nativeStep (rawWords depth) current bound :=
  Lp.compMeasurePreservingₗᵢ ℂ (originalMeasurableEquiv depth).symm (inverse_preserving depth current bound)

theorem fieldPullback_inverse (depth : Nat) (current : Current) (bound : Nat)
    (value : SourceWeightedRecovery.Space (wordLaw depth current bound)) :
    fieldPullback depth current bound (inversePullback depth current bound value) = value := by
  have forward : MeasurePreserving (originalMeasurableEquiv depth) (wordLaw depth current bound).toMeasure
      (empirical nativeStep (rawWords depth) current bound).toMeasure := original_preserving depth current bound
  have composed := Lp.compMeasurePreserving_comp_apply value (inverse_preserving depth current bound) forward
  have identity := (originalMeasurableEquiv depth).symm_comp_self
  simp only [identity, Lp.compMeasurePreserving_id_apply] at composed
  exact composed.symm

theorem fieldPullback_surjective (depth : Nat) (current : Current) (bound : Nat) :
    Function.Surjective (fieldPullback depth current bound) :=
  fun value => ⟨inversePullback depth current bound value, fieldPullback_inverse depth current bound value⟩

theorem fieldPullback_residual_zero (depth : Nat) (current : Current) (bound : Nat)
    (value : SourceWeightedRecovery.Space (wordLaw depth current bound)) :
    IsometricRetainedTransfer.residual (fieldPullback depth current bound) value = 0 :=
  (IsometricRetainedTransfer.residual_zero_iff (fieldPullback depth current bound) value).mpr
    (fieldPullback_surjective depth current bound value)

end
end SourceGeneratedActionWords.Fock.OriginalHilbert
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
