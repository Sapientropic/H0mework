import H0mework.Probability.Source.MomentFilter
import H0mework.Versions.X.Fock.HistoryConditional.InventoryError

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

namespace SourceConditionalInventory

open SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedScalarCofinalTopology.NativeProbability (Field)
open SourceObservationInvariantControls (parity)
open scoped Classical
noncomputable section

theorem supported_retained (bound depth : Nat) (value : Field parity)
    (supported : value ∈ ((historyPMF bound).map (observation bound depth)).support) :
    value ∈ ((historyPMF (bound + 1)).map (observation (bound + 1) depth)).support := by
  obtain ⟨i, _, same⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  apply (PMF.mem_support_map_iff _ _ _).mpr
  exact ⟨i.castSucc, by simp only [historyPMF, PMF.mem_support_uniformOfFintype], (observation_retained bound depth i).trans same⟩

def count (bound depth : Nat) (value : Field parity) : ℝ :=
  ((bound + 1 : Nat) : ℝ) * ((historyPMF bound).map (observation bound depth) value).toReal

def conditional (bound depth : Nat) (value : Field parity)
    (supported : value ∈ ((historyPMF bound).map (observation bound depth)).support) : PMF (Fin (bound + 1)) :=
  SourceConditionalHistory.conditional (historyPMF bound) (observation bound depth) value supported

theorem conditional_mean_append (bound depth : Nat) (value : Field parity)
    (supported : value ∈ ((historyPMF bound).map (observation bound depth)).support) :
    (count (bound + 1) depth value : ℂ) •
        SourceVectorMoment.mean (conditional (bound + 1) depth value (supported_retained bound depth value supported)) (values (bound + 1)) =
      (count bound depth value : ℂ) • SourceVectorMoment.mean (conditional bound depth value supported) (values bound) +
        (if observation (bound + 1) depth (Fin.last (bound + 1)) = value then born bound else 0) := by
  simp only [count, Complex.ofReal_mul, Complex.ofReal_natCast, mul_smul, conditional,
    SourceVectorMoment.filtered_mean]
  rw [mean_count, mean_count, Fin.sum_univ_castSucc]
  simp only [values_retained, observation_retained, born]
  rfl


theorem conditional_error_count (bound depth : Nat) (value : Field parity)
    (supported : value ∈ ((historyPMF bound).map (observation bound depth)).support)
    (guess : SourceJointClockGraph.Carrier) :
    count bound depth value * SourceVectorMoment.error (conditional bound depth value supported) (values bound) guess =
      ∑ i, if observation bound depth i = value then ‖values bound i - guess‖ ^ 2 else 0 := by
  rw [count, mul_assoc, conditional, SourceVectorMoment.filtered_error]
  exact sum_count bound _

theorem conditional_error_append (bound depth : Nat) (value : Field parity)
    (supported : value ∈ ((historyPMF bound).map (observation bound depth)).support)
    (guess : SourceJointClockGraph.Carrier) :
    count (bound + 1) depth value *
        SourceVectorMoment.error (conditional (bound + 1) depth value (supported_retained bound depth value supported)) (values (bound + 1)) guess =
      count bound depth value * SourceVectorMoment.error (conditional bound depth value supported) (values bound) guess +
        (if observation (bound + 1) depth (Fin.last (bound + 1)) = value then ‖born bound - guess‖ ^ 2 else 0) := by
  rw [conditional_error_count, conditional_error_count, Fin.sum_univ_castSucc]
  simp only [observation_retained, values_retained, born]
  rfl

theorem conditional_variance_append (bound depth : Nat) (value : Field parity)
    (supported : value ∈ ((historyPMF bound).map (observation bound depth)).support) :
    count (bound + 1) depth value *
        SourceVectorMoment.variance (conditional (bound + 1) depth value (supported_retained bound depth value supported)) (values (bound + 1)) +
      count (bound + 1) depth value *
        ‖SourceVectorMoment.mean (conditional (bound + 1) depth value (supported_retained bound depth value supported)) (values (bound + 1)) -
          SourceVectorMoment.mean (conditional bound depth value supported) (values bound)‖ ^ 2 =
      count bound depth value * SourceVectorMoment.variance (conditional bound depth value supported) (values bound) +
        (if observation (bound + 1) depth (Fin.last (bound + 1)) = value then
          ‖born bound - SourceVectorMoment.mean (conditional bound depth value supported) (values bound)‖ ^ 2 else 0) := by
  have paid := conditional_error_append bound depth value supported
    (SourceVectorMoment.mean (conditional bound depth value supported) (values bound))
  rw [SourceVectorMoment.error_decomposition (conditional (bound + 1) depth value _), mul_add] at paid
  exact paid

end
end SourceConditionalInventory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
