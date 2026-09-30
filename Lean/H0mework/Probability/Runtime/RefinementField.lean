import H0mework.Realization.HistoryTopology.Compactness
import H0mework.Realization.HistoryTopology.Density
import H0mework.Probability.Runtime.InvariantMoments
import Mathlib.Topology.DenseEmbedding

/-! A linear restriction of one raw native observation generates its complete-field refinement. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedObservationRefinement

open CategoryTheory SourceOperationNative SourceGeneratedActionObservationHistory
open SourceGeneratedScalarCofinalNaturality SourceGeneratedScalarCofinalTopology
open SourceGeneratedScalarCofinalTopology.NativeProbability MeasureTheory

noncomputable section

universe u

variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}
variable {B D : Type u} [AddCommGroup B] [AddCommGroup D]
variable (read : process.State → B) (restriction : B →ₗ[ℤ] D)

def restrictedRead : process.State → D := fun state => restriction (read state)

theorem observer_square : restriction.comp (observer process read) =
    observer process (restrictedRead read restriction) := by
  apply observer_unique
  intro state
  simp only [LinearMap.comp_apply, observer_statePoint, restrictedRead]

def prefixMap (bound : Nat) : PrefixCarrier B bound →ₗ[ℤ] PrefixCarrier D bound :=
  LinearMap.pi fun index => restriction.comp (LinearMap.proj index)

def morphism : Morphism (data (sourceAction process) (observer process read))
    (data (sourceAction process) (observer process (restrictedRead read restriction))) where
  generatorMap := LinearMap.id
  stageMap := prefixMap restriction
  transition_naturality _ := rfl
  evaluator_naturality bound := by
    apply LinearMap.ext
    intro word
    funext index
    exact LinearMap.congr_fun (observer_square read restriction)
      (((sourceAction process) ^ index.val) word)

def fieldMap : Field read →ₗ[ℤ] Field (restrictedRead read restriction) :=
  ((morphism read restriction).completionMorphism
    (compatible (sourceAction process) (observer process read))
    (compatible (sourceAction process) (observer process (restrictedRead read restriction)))).hom

theorem fieldMap_source (word : SourceOperationNative.Carrier process) :
    fieldMap read restriction (sourceMap (sourceAction process) (observer process read) word) =
      sourceMap (sourceAction process) (observer process (restrictedRead read restriction)) word :=
  ConcreteCategory.congr_hom ((morphism read restriction).completionMorphism_source_naturality
    (compatible (sourceAction process) (observer process read))
    (compatible (sourceAction process) (observer process (restrictedRead read restriction)))) word

theorem fieldMap_point (state : process.State) :
    fieldMap read restriction (fieldPoint read state) =
      fieldPoint (restrictedRead read restriction) state :=
  fieldMap_source read restriction (statePoint process state)

theorem fieldMap_uniformContinuous :
    @UniformContinuous _ _ (fieldUniform read) (fieldUniform (restrictedRead read restriction))
      (fieldMap read restriction) :=
  completionMorphism_uniformContinuous (morphism read restriction)
    (compatible (sourceAction process) (observer process read))
    (compatible (sourceAction process) (observer process (restrictedRead read restriction)))

theorem fieldMap_measurable :
    @Measurable _ _ (fieldBorel read) (fieldBorel (restrictedRead read restriction))
      (fieldMap read restriction) := by
  let : UniformSpace (Field read) := fieldUniform read
  let : UniformSpace (Field (restrictedRead read restriction)) := fieldUniform (restrictedRead read restriction)
  exact (fieldMap_uniformContinuous read restriction).continuous.borel_measurable

theorem fieldMap_action (value : Field read) :
    fieldMap read restriction (fieldAction read value) =
      fieldAction (restrictedRead read restriction) (fieldMap read restriction value) := by
  let : UniformSpace (Field read) := fieldUniform read
  let : UniformSpace (Field (restrictedRead read restriction)) := fieldUniform (restrictedRead read restriction)
  let : T2Space (Field (restrictedRead read restriction)) := field_t2 (restrictedRead read restriction)
  have sourceDense := completionMap_denseRange
    (data (sourceAction process) (observer process read))
    (compatible (sourceAction process) (observer process read))
  have before := (endomorphism_uniformContinuous (sourceAction process) (observer process read)).continuous
  have after := (endomorphism_uniformContinuous (sourceAction process)
    (observer process (restrictedRead read restriction))).continuous
  have mapContinuous := (fieldMap_uniformContinuous read restriction).continuous
  have equality := sourceDense.equalizer (mapContinuous.comp before) (after.comp mapContinuous) (by
    funext word
    change fieldMap read restriction (fieldAction read
        (sourceMap (sourceAction process) (observer process read) word)) =
      fieldAction (restrictedRead read restriction) (fieldMap read restriction
        (sourceMap (sourceAction process) (observer process read) word))
    rw [fieldMap_source]
    change fieldMap read restriction
        (endomorphism (sourceAction process) (observer process read)
          (sourceMap (sourceAction process) (observer process read) word)) = _
    rw [endomorphism_source, fieldMap_source]
    exact (endomorphism_source (sourceAction process)
      (observer process (restrictedRead read restriction)) word).symm)
  exact congrFun equality value

theorem fieldPMF_pushforward (runtime : LivingRuntimeState process) (bound : Nat) :
    (fieldPMF read runtime bound).map (fieldMap read restriction) =
      fieldPMF (restrictedRead read restriction) runtime bound := by
  rw [fieldPMF, PMF.map_comp]
  have square : (fieldMap read restriction ∘ fieldPoint read) =
      fieldPoint (restrictedRead read restriction) := funext (fieldMap_point read restriction)
  rw [square]
  rfl

theorem empirical_pushforward (runtime : LivingRuntimeState process) (bound : Nat) :
    letI : MeasurableSpace (Field read) := fieldBorel read
    letI : MeasurableSpace (Field (restrictedRead read restriction)) := fieldBorel (restrictedRead read restriction)
    (empirical read runtime bound).map (fieldMap_measurable read restriction).aemeasurable =
      empirical (restrictedRead read restriction) runtime bound := by
  let : MeasurableSpace (Field read) := fieldBorel read
  let : MeasurableSpace (Field (restrictedRead read restriction)) := fieldBorel (restrictedRead read restriction)
  apply ProbabilityMeasure.toMeasure_injective
  change (fieldPMF read runtime bound).toMeasure.map (fieldMap read restriction) =
    (fieldPMF (restrictedRead read restriction) runtime bound).toMeasure
  rw [PMF.toMeasure_map _ _ (fieldMap_measurable read restriction), fieldPMF_pushforward]

end
end SourceGeneratedObservationRefinement
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
