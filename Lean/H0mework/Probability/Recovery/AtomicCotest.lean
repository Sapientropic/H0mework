import H0mework.Probability.Recovery.Core

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedAtomicObservation

open SourceWeightedRecovery MeasureTheory
open scoped InnerProductSpace

noncomputable section

universe u

variable {A : Type u} [MeasurableSpace A] [MeasurableSingletonClass A]
variable (source : PMF A) (point : A)

def cotest : Space source :=
  indicatorConstLp 2 (measurableSet_singleton point) (measure_ne_top _ _) (1 : ℂ)

theorem cotest_pairing (value : Space source) :
    ⟪cotest source point, value⟫_ℂ = (source point).toReal • value point := by
  rw [cotest, L2.inner_indicatorConstLp_one, integral_singleton]
  rw [measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]

theorem cotest_norm : ‖cotest source point‖ = Real.sqrt (source point).toReal := by
  rw [cotest, norm_indicatorConstLp (by norm_num : (2 : ENNReal) ≠ 0)
    (by norm_num : (2 : ENNReal) ≠ ⊤)]
  rw [measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  norm_num [Real.sqrt_eq_rpow]

theorem cotest_at (supported : point ∈ source.support) : cotest source point point = 1 := by
  have actual := ae_at_support source point supported
    (@indicatorConstLp_coeFn A _ _ 2 source.toMeasure _ {point}
      (measurableSet_singleton point) (measure_ne_top _ _) (1 : ℂ))
  simpa only [cotest, Set.indicator_of_mem (Set.mem_singleton point)] using actual

omit [MeasurableSpace A] [MeasurableSingletonClass A] in
theorem mass_positive (supported : point ∈ source.support) : 0 < (source point).toReal :=
  ENNReal.toReal_pos supported (source.apply_ne_top point)

end
end SourceGeneratedAtomicObservation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
