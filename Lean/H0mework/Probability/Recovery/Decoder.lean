import H0mework.Probability.Recovery.Core

/-! Raw decoders are represented only on the finite actual output support, without a zero-mass conditional branch. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWeightedRecovery

open MeasureTheory
open scoped Classical

noncomputable section

universe u v

variable {Source : Type u} [Fintype Source] [MeasurableSpace Source] [MeasurableSingletonClass Source]
variable {Observed : Type v} [MeasurableSpace Observed] [MeasurableSingletonClass Observed]
variable (source : PMF Source) (observer : Source → Observed)

def atoms : Finset Observed := (Finset.univ.filter (fun point => point ∈ source.support)).image observer

omit [MeasurableSpace Source] [MeasurableSingletonClass Source]
    [MeasurableSpace Observed] [MeasurableSingletonClass Observed] in
theorem atoms_iff (atom : Observed) : atom ∈ atoms source observer ↔ atom ∈ (observed source observer).support := by
  simp only [atoms, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    PMF.mem_support_map_iff]

def atomTest (atom : Observed) : Space (observed source observer) :=
  indicatorConstLp 2 (measurableSet_singleton atom) (measure_ne_top _ _) (1 : ℂ)

omit [Fintype Source] [MeasurableSpace Source] [MeasurableSingletonClass Source] in
theorem atomTest_at (atom point : Observed) (supported : point ∈ (observed source observer).support) :
    atomTest source observer atom point = if point = atom then 1 else 0 := by
  have raw := @indicatorConstLp_coeFn Observed _ _ 2 (observed source observer).toMeasure _
    {atom} (measurableSet_singleton atom) (measure_ne_top _ _) (1 : ℂ)
  simpa only [atomTest, Set.indicator_apply, Set.mem_singleton_iff] using
    ae_at_support (observed source observer) point supported raw

def decoderValue (decoder : Observed → ℂ) : Space (observed source observer) :=
  ∑ atom ∈ atoms source observer, decoder atom • atomTest source observer atom

omit [MeasurableSpace Source] [MeasurableSingletonClass Source] in
theorem decoderValue_at (decoder : Observed → ℂ) (point : Observed)
    (supported : point ∈ (observed source observer).support) : decoderValue source observer decoder point = decoder point := by
  change evalAt (observed source observer) point supported (decoderValue source observer decoder) = _
  simp only [decoderValue, map_sum, map_smul, evalAt_apply, atomTest_at source observer _ point supported, smul_eq_mul]
  rw [Finset.sum_eq_single point]
  · simp
  · intro atom _ distinct
    simp only [if_neg (Ne.symm distinct), mul_zero]
  · intro absent
    exact (absent ((atoms_iff source observer point).mpr supported)).elim

end
end SourceWeightedRecovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
