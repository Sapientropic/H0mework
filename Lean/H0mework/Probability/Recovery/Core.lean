import H0mework.Realization.HilbertTransfer.Recovery
import H0mework.Probability.Source.Conditional
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-! A finite source PMF generates the existing L² pullback and its retained transfer, including zero source weights. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWeightedRecovery

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

universe u v

section Atomic
variable {A : Type u} [MeasurableSpace A] [MeasurableSingletonClass A]

abbrev Space (source : PMF A) := Lp ℂ 2 source.toMeasure

theorem ae_at_support (source : PMF A) (point : A) (supported : point ∈ source.support)
    {predicate : A → Prop} (proof : ∀ᵐ point ∂source.toMeasure, predicate point) : predicate point := by
  have positive : source.toMeasure {point} ≠ 0 := by
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    exact supported
  obtain ⟨found, member, holds⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae positive (ae_restrict_of_ae proof)
  exact Set.mem_singleton_iff.mp member ▸ holds

def evalAt (source : PMF A) (point : A) (supported : point ∈ source.support) : Space source →ₗ[ℂ] ℂ where
  toFun value := value point
  map_add' left right := ae_at_support source point supported (Lp.coeFn_add left right)
  map_smul' scalar value := ae_at_support source point supported (Lp.coeFn_smul scalar value)

theorem evalAt_apply (source : PMF A) (point : A) (supported : point ∈ source.support) (value : Space source) :
    evalAt source point supported value = value point := rfl
end Atomic

variable {Source : Type u} [Fintype Source] [MeasurableSpace Source] [MeasurableSingletonClass Source]
variable {Observed : Type v} [MeasurableSpace Observed] [MeasurableSingletonClass Observed]
variable (source : PMF Source) (observer : Source → Observed)

abbrev observed : PMF Observed := source.map observer

omit [MeasurableSingletonClass Observed] in
theorem source_preserving : MeasurePreserving observer source.toMeasure (observed source observer).toMeasure :=
  ⟨measurable_of_finite observer, PMF.toMeasure_map observer source (measurable_of_finite observer)⟩

def pullback : Space (observed source observer) →ₗᵢ[ℂ] Space source :=
  Lp.compMeasurePreservingₗᵢ ℂ observer (source_preserving source observer)

abbrev transfer : Space source →L[ℂ] Space (observed source observer) :=
  IsometricRetainedTransfer.transfer (pullback source observer)

abbrev residual : Space source →L[ℂ] Space source :=
  IsometricRetainedTransfer.residual (pullback source observer)

omit [Fintype Source] [MeasurableSpace Source] [MeasurableSingletonClass Source]
    [MeasurableSpace Observed] [MeasurableSingletonClass Observed] in
theorem observed_supported (point : Source) (supported : point ∈ source.support) :
    observer point ∈ (observed source observer).support :=
  (PMF.mem_support_map_iff observer source (observer point)).mpr ⟨point, supported, rfl⟩

omit [MeasurableSingletonClass Observed] in
theorem pullback_at (value : Space (observed source observer)) (point : Source) (supported : point ∈ source.support) :
    pullback source observer value point = value (observer point) :=
  ae_at_support source point supported (Lp.coeFn_compMeasurePreserving value (source_preserving source observer))

theorem task_memLp (task : Source → ℂ) : MemLp task 2 source.toMeasure := by
  apply MemLp.of_bound (measurable_of_finite task).aestronglyMeasurable (∑ point, ‖task point‖)
  apply Filter.Eventually.of_forall
  intro point
  exact Finset.single_le_sum (fun other _ => norm_nonneg (task other)) (Finset.mem_univ point)

def taskValue (task : Source → ℂ) : Space source := (task_memLp source task).toLp task

theorem taskValue_at (task : Source → ℂ) (point : Source) (supported : point ∈ source.support) :
    taskValue source task point = task point :=
  ae_at_support source point supported (task_memLp source task).coeFn_toLp

theorem inner_source_sum (left right : Space source) :
    ⟪left, right⟫_ℂ = ∑ point : Source, (source point).toReal • ⟪left point, right point⟫_ℂ := by
  rw [L2.inner_def, PMF.integral_eq_sum]

theorem norm_source_sq (value : Space source) :
    ‖value‖ ^ 2 = ∑ point : Source, (source point).toReal * ‖value point‖ ^ 2 := by
  have realPart := congrArg Complex.re (inner_source_sum source value value)
  calc
    _ = Complex.re ⟪value, value⟫_ℂ := norm_sq_eq_re_inner (𝕜 := ℂ) value
    _ = ∑ point : Source, (source point).toReal * Complex.re ⟪value point, value point⟫_ℂ := by
      simpa only [Complex.re_sum, Complex.smul_re, smul_eq_mul] using realPart
    _ = _ := by
      apply Finset.sum_congr rfl
      intro point _
      exact congrArg ((source point).toReal * ·) (norm_sq_eq_re_inner (𝕜 := ℂ) (value point)).symm

end
end SourceWeightedRecovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
