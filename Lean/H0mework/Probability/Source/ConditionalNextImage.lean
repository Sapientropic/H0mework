import H0mework.Probability.Source.ConditionalNextEntropy
import Mathlib.Data.Set.Finite.Range

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalNext.Image

open SourceWeightedRecovery
noncomputable section
universe u v w
variable {Source : Type u} {Observed : Type v} {Next : Type w}

abbrev Values (nextRead : Source → Next) := Set.range nextRead

@[instance_reducible] def valuesFintype [Fintype Source] (nextRead : Source → Next) : Fintype (Values nextRead) := by
  classical
  exact Set.fintypeRange nextRead

@[instance_reducible] def valuesMeasurable (nextRead : Source → Next) : MeasurableSpace (Values nextRead) := ⊤

theorem valuesSingleton (nextRead : Source → Next) : @MeasurableSingletonClass (Values nextRead) (valuesMeasurable nextRead) := by
  change @MeasurableSingletonClass (Values nextRead) ⊤
  infer_instance

attribute [local instance] valuesFintype valuesMeasurable valuesSingleton

def actual (nextRead : Source → Next) : Source → Values nextRead := Set.rangeFactorization nextRead

theorem actual_value (nextRead : Source → Next) (point : Source) : (actual nextRead point).val = nextRead point := rfl

theorem conditional_original (source : PMF Source) (read : Source → Observed) (nextRead : Source → Next)
    (value : Observed) (supported : value ∈ (source.map read).support) :
    (conditionalNext source read (actual nextRead) value supported).map Subtype.val =
      conditionalNext source read nextRead value supported := by
  rw [conditionalNext, conditionalNext, PMF.map_comp]
  rfl

variable [Fintype Source]

theorem entropy_zero_iff (source : PMF Source) (read : Source → Observed) (nextRead : Source → Next)
    (positive : ∀ point, point ∈ source.support) :
    conditionalEntropy source read (actual nextRead) positive = 0 ↔
      ∀ left right, read left = read right → nextRead left = nextRead right := by
  rw [SourceConditionalNext.conditionalEntropy_zero_iff]
  constructor
  · intro determined left right same
    exact congrArg Subtype.val (determined left right same)
  · intro determined left right same
    exact Subtype.ext (determined left right same)

variable [MeasurableSpace Source] [MeasurableSingletonClass Source]

theorem mean_original (source : PMF Source) (read : Source → Observed) (nextRead : Source → Next)
    (decode : Next → ℂ) (value : Observed) (supported : value ∈ (source.map read).support) :
    mean source read (actual nextRead) (fun item => decode item.val) value supported =
      conditionalMean source read (decode ∘ nextRead) value supported :=
  mean_is_conditional source read (actual nextRead) (fun item => decode item.val) value supported

variable [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

theorem residual_variance_original (source : PMF Source) (read : Source → Observed) (nextRead : Source → Next)
    (decode : Next → ℂ) (positive : ∀ point, point ∈ source.support) :
    ‖residual source read (taskValue source (decode ∘ nextRead))‖ ^ 2 =
      ∑ point, (source point).toReal * variance source read (actual nextRead) (fun item => decode item.val) (read point)
        (observed_supported source read point (positive point)) :=
  residual_variance source read (actual nextRead) (fun item => decode item.val) positive

theorem error_variance_original (source : PMF Source) (read : Source → Observed) (nextRead : Source → Next)
    (decode : Next → ℂ) (positive : ∀ point, point ∈ source.support) (decoder : Observed → ℂ) :
    error source read (decode ∘ nextRead) decoder =
      (∑ point, (source point).toReal * variance source read (actual nextRead) (fun item => decode item.val) (read point)
        (observed_supported source read point (positive point))) +
      error source read (fun point => mean source read (actual nextRead) (fun item => decode item.val) (read point)
        (observed_supported source read point (positive point))) decoder :=
  error_variance source read (actual nextRead) (fun item => decode item.val) positive decoder

end
end SourceConditionalNext.Image
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
