import H0mework.Probability.Source.ModelFamily
import H0mework.Realization.HistoryTopology.Density
import Mathlib.Topology.DenseEmbedding

/-! Reindexing one source observation inventory generates a restriction between its existing complete fields. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOwnedObservationHistory.FamilyField

open CategoryTheory SourceGeneratedActionObservationHistory SourceGeneratedScalarCofinalNaturality
open SourceGeneratedScalarCofinalTopology FamilyModel

noncomputable section

universe u

variable {State I J : Type u} {B : I → Type u} [∀ index, AddCommGroup (B index)]

def indexMap (reindex : J → I) : ((index : I) → B index) →ₗ[ℤ] ((index : J) → B (reindex index)) :=
  LinearMap.pi fun index => LinearMap.proj (reindex index)

def prefixMap (reindex : J → I) (bound : Nat) :
    PrefixCarrier ((index : I) → B index) bound →ₗ[ℤ]
      PrefixCarrier ((index : J) → B (reindex index)) bound :=
  LinearMap.pi fun index => (indexMap reindex).comp (LinearMap.proj index)

variable (step : State → State) (read : (index : I) → State → B index) (reindex : J → I)

def morphism : Morphism (data (sourceAction step) (observation (familyRead read)))
    (data (sourceAction step) (observation (familyRead (fun index => read (reindex index))))) where
  generatorMap := LinearMap.id
  stageMap := prefixMap reindex
  transition_naturality _ := rfl
  evaluator_naturality bound := by
    apply LinearMap.ext
    intro word
    funext index item
    change observation (familyRead read) ((sourceAction step ^ index.val) word) (reindex item) =
      observation (familyRead (fun index => read (reindex index))) ((sourceAction step ^ index.val) word) item
    rw [observation_family, observation_family]
    rfl

def fieldMap : Field step (familyRead read) →ₗ[ℤ]
    Field step (familyRead (fun index => read (reindex index))) :=
  ((morphism step read reindex).completionMorphism
    (compatible (sourceAction step) (observation (familyRead read)))
    (compatible (sourceAction step) (observation (familyRead (fun index => read (reindex index)))))).hom

theorem fieldMap_source (word : Carrier State) :
    fieldMap step read reindex (sourceMap (sourceAction step) (observation (familyRead read)) word) =
      sourceMap (sourceAction step) (observation (familyRead (fun index => read (reindex index)))) word :=
  ConcreteCategory.congr_hom ((morphism step read reindex).completionMorphism_source_naturality
    (compatible (sourceAction step) (observation (familyRead read)))
    (compatible (sourceAction step) (observation (familyRead (fun index => read (reindex index)))))) word

theorem fieldMap_point (state : State) :
    fieldMap step read reindex (fieldPoint step (familyRead read) state) =
      fieldPoint step (familyRead (fun index => read (reindex index))) state :=
  fieldMap_source step read reindex (sourcePoint state)

theorem fieldMap_uniformContinuous :
    @UniformContinuous _ _ (fieldUniform step (familyRead read))
      (fieldUniform step (familyRead (fun index => read (reindex index)))) (fieldMap step read reindex) :=
  completionMorphism_uniformContinuous (morphism step read reindex)
    (compatible (sourceAction step) (observation (familyRead read)))
    (compatible (sourceAction step) (observation (familyRead (fun index => read (reindex index)))))

theorem fieldMap_measurable :
    @Measurable _ _ (fieldBorel step (familyRead read))
      (fieldBorel step (familyRead (fun index => read (reindex index)))) (fieldMap step read reindex) := by
  let : UniformSpace (Field step (familyRead read)) := fieldUniform step (familyRead read)
  let : UniformSpace (Field step (familyRead (fun index => read (reindex index)))) :=
    fieldUniform step (familyRead (fun index => read (reindex index)))
  exact (fieldMap_uniformContinuous step read reindex).continuous.borel_measurable

theorem fieldMap_action (value : Field step (familyRead read)) :
    fieldMap step read reindex (fieldAction step (familyRead read) value) =
      fieldAction step (familyRead (fun index => read (reindex index))) (fieldMap step read reindex value) := by
  let : UniformSpace (Field step (familyRead read)) := fieldUniform step (familyRead read)
  let : UniformSpace (Field step (familyRead (fun index => read (reindex index)))) :=
    fieldUniform step (familyRead (fun index => read (reindex index)))
  let target := data (sourceAction step) (observation (familyRead (fun index => read (reindex index))))
  let laws := compatible (sourceAction step) (observation (familyRead (fun index => read (reindex index))))
  let : ∀ stage, UniformSpace (target.StageQuotient stage) := stageUniform target
  let : T2Space (Field step (familyRead (fun index => read (reindex index)))) :=
    (coordinates_isUniformEmbedding target laws).isEmbedding.t2Space
  have dense := completionMap_denseRange (data (sourceAction step) (observation (familyRead read)))
    (compatible (sourceAction step) (observation (familyRead read)))
  have before := (endomorphism_uniformContinuous (sourceAction step) (observation (familyRead read))).continuous
  have after := (endomorphism_uniformContinuous (sourceAction step)
    (observation (familyRead (fun index => read (reindex index))))).continuous
  have mapped := (fieldMap_uniformContinuous step read reindex).continuous
  have equality := dense.equalizer (mapped.comp before) (after.comp mapped) (by
    funext word
    change fieldMap step read reindex (fieldAction step (familyRead read)
        (sourceMap (sourceAction step) (observation (familyRead read)) word)) =
      fieldAction step (familyRead (fun index => read (reindex index))) (fieldMap step read reindex
        (sourceMap (sourceAction step) (observation (familyRead read)) word))
    rw [fieldMap_source]
    change fieldMap step read reindex (endomorphism (sourceAction step) (observation (familyRead read))
      (sourceMap (sourceAction step) (observation (familyRead read)) word)) = _
    rw [endomorphism_source, fieldMap_source]
    exact (endomorphism_source (sourceAction step)
      (observation (familyRead (fun index => read (reindex index)))) word).symm)
  exact congrFun equality value

end
end SourceOwnedObservationHistory.FamilyField
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
