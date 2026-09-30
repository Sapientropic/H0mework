import H0mework.Probability.Recovery.RecoveryMap
import H0mework.Chemistry.LAlanineEntropy.FiniteGibbsPopulation

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalNext

open SourceWeightedRecovery MeasureTheory
open scoped Classical
noncomputable section

universe u v w
variable {Source : Type u} [Fintype Source] {Observed : Type v} {Next : Type w} [Fintype Next]
variable (source : PMF Source) (read : Source → Observed) (nextRead : Source → Next)

def conditionalNext (value : Observed) (supported : value ∈ (source.map read).support) : PMF Next :=
  (SourceConditionalHistory.conditional source read value supported).map nextRead

omit [Fintype Source] [Fintype Next] in
theorem conditionalNext_support (value : Observed) (supported : value ∈ (source.map read).support)
    (next : Next) : next ∈ (conditionalNext source read nextRead value supported).support ↔
      ∃ point, read point = value ∧ source point ≠ 0 ∧ nextRead point = next := by
  rw [conditionalNext, PMF.mem_support_map_iff]
  simp only [SourceConditionalHistory.conditional_support, Set.mem_inter_iff, Set.mem_ofPred_eq,
    PMF.mem_support_iff]
  aesop

omit [Fintype Source] [Fintype Next] in
theorem conditionalNext_recombines :
    (source.map read).bindOnSupport (conditionalNext source read nextRead) = source.map nextRead :=
  SourceConditionalHistory.recombine_map source read nextRead

def mean (decode : Next → ℂ) (value : Observed) (supported : value ∈ (source.map read).support) : ℂ :=
  ∑ next, (conditionalNext source read nextRead value supported next).toReal • decode next

def variance (decode : Next → ℂ) (value : Observed) (supported : value ∈ (source.map read).support) : ℝ :=
  ∑ next, (conditionalNext source read nextRead value supported next).toReal *
    ‖decode next - mean source read nextRead decode value supported‖ ^ 2

omit [Fintype Source] in
theorem variance_nonnegative (decode : Next → ℂ) (value : Observed)
    (supported : value ∈ (source.map read).support) :
    0 ≤ variance source read nextRead decode value supported :=
  Finset.sum_nonneg fun _ _ => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)

variable [MeasurableSpace Source] [MeasurableSingletonClass Source]
variable [MeasurableSpace Next] [MeasurableSingletonClass Next]

private theorem sum_map {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (p : PMF Source) (f : Source → Next) (value : Next → E) :
    (∑ next, (p.map f next).toReal • value next) = ∑ point, (p point).toReal • value (f point) := by
  rw [← PMF.integral_eq_sum (p.map f) value, ← PMF.integral_eq_sum p (fun point => value (f point)),
    ← PMF.toMeasure_map f p (measurable_of_finite f)]
  exact integral_map (measurable_of_finite f).aemeasurable (measurable_of_finite value).aestronglyMeasurable

theorem mean_is_conditional (decode : Next → ℂ) (value : Observed)
    (supported : value ∈ (source.map read).support) :
    mean source read nextRead decode value supported =
      conditionalMean source read (decode ∘ nextRead) value supported :=
  sum_map _ nextRead decode

theorem variance_is_conditional (decode : Next → ℂ) (value : Observed)
    (supported : value ∈ (source.map read).support) :
    variance source read nextRead decode value supported =
      ∑ point, (SourceConditionalHistory.conditional source read value supported point).toReal *
        ‖decode (nextRead point) - mean source read nextRead decode value supported‖ ^ 2 :=
  sum_map _ nextRead (fun next => ‖decode next - mean source read nextRead decode value supported‖ ^ 2)

variable [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

theorem optimal_is_mean (decode : Next → ℂ) (value : Observed)
    (supported : value ∈ (source.map read).support) :
    optimalDecoder source read (decode ∘ nextRead) value =
      mean source read nextRead decode value supported :=
  (optimal_is_conditional source read _ value supported).trans
    (mean_is_conditional source read nextRead decode value supported).symm

omit [MeasurableSingletonClass Observed] in
private theorem conditional_loss_swap (task : Source → ℂ) (positive : ∀ point, point ∈ source.support)
    (left right : Source) :
    (source left).toReal *
        (SourceConditionalHistory.conditional source read (read left)
          (observed_supported source read left (positive left)) right).toReal *
        ‖task right - optimalDecoder source read task (read left)‖ ^ 2 =
      (source right).toReal *
        (SourceConditionalHistory.conditional source read (read right)
          (observed_supported source read right (positive right)) left).toReal *
        ‖task right - optimalDecoder source read task (read right)‖ ^ 2 := by
  simp only [SourceConditionalHistory.conditional_apply]
  by_cases same : read right = read left
  · simp only [same, if_true, ENNReal.toReal_mul]
    ring
  · simp only [same, Ne.symm same, if_false, ENNReal.toReal_zero, mul_zero, zero_mul]

omit [MeasurableSingletonClass Observed] in
private theorem conditional_error_average (task : Source → ℂ) (positive : ∀ point, point ∈ source.support) :
    (∑ left, (source left).toReal *
      ∑ right, (SourceConditionalHistory.conditional source read (read left)
        (observed_supported source read left (positive left)) right).toReal *
          ‖task right - optimalDecoder source read task (read left)‖ ^ 2) =
      error source read task (optimalDecoder source read task) := by
  calc
    _ = ∑ left, ∑ right, (source right).toReal *
        (SourceConditionalHistory.conditional source read (read right)
          (observed_supported source read right (positive right)) left).toReal *
        ‖task right - optimalDecoder source read task (read right)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro left _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro right _
      exact (mul_assoc _ _ _).symm.trans (conditional_loss_swap source read task positive left right)
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul, ← Finset.mul_sum,
        SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Population.pmf_sum_toReal,
        mul_one, error]

theorem residual_variance (decode : Next → ℂ) (positive : ∀ point, point ∈ source.support) :
    ‖residual source read (taskValue source (decode ∘ nextRead))‖ ^ 2 =
      ∑ point, (source point).toReal * variance source read nextRead decode (read point)
        (observed_supported source read point (positive point)) := by
  simp only [variance_is_conditional, ← optimal_is_mean]
  exact (optimal_attains source read (decode ∘ nextRead)).symm.trans
    (conditional_error_average source read (decode ∘ nextRead) positive).symm

theorem error_variance (decode : Next → ℂ) (positive : ∀ point, point ∈ source.support)
    (decoder : Observed → ℂ) :
    error source read (decode ∘ nextRead) decoder =
      (∑ point, (source point).toReal * variance source read nextRead decode (read point)
        (observed_supported source read point (positive point))) +
      error source read (fun point => mean source read nextRead decode (read point)
        (observed_supported source read point (positive point))) decoder := by
  rw [residual_decomposition, residual_variance source read nextRead decode positive]
  simp_rw [optimal_is_mean source read nextRead decode _ (observed_supported source read _ (positive _))]

end
end SourceConditionalNext
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
