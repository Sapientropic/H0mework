import H0mework.Versions.R2.Probability.FullSource.Read
import H0mework.Realization.HistoryTopology.Density
import Mathlib.Topology.DenseEmbedding

/-! Every raw observation is a generated restriction of the same complete native source field. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOwnedObservationHistory.FullProjection

open CategoryTheory SourceGeneratedActionObservationHistory SourceGeneratedScalarCofinalNaturality
open SourceGeneratedScalarCofinalTopology

noncomputable section

universe u

variable {State B : Type u} [AddCommGroup B]
variable (step : State → State) (read : State → B)

def prefixMap (bound : Nat) : PrefixCarrier (Carrier State) bound →ₗ[ℤ] PrefixCarrier B bound :=
  LinearMap.pi fun index => (observation read).comp (LinearMap.proj index)

def morphism : Morphism (data (sourceAction step) (observation (sourcePoint (State := State))))
    (data (sourceAction step) (observation read)) where
  generatorMap := LinearMap.id
  stageMap := prefixMap read
  transition_naturality _ := rfl
  evaluator_naturality bound := by
    apply LinearMap.ext
    intro word
    funext index
    change observation read (observation sourcePoint ((sourceAction step ^ index.val) word)) =
      observation read ((sourceAction step ^ index.val) word)
    rw [full_observation]
    rfl

def fieldMap : Field step (sourcePoint (State := State)) →ₗ[ℤ] Field step read :=
  ((morphism step read).completionMorphism
    (compatible (sourceAction step) (observation sourcePoint))
    (compatible (sourceAction step) (observation read))).hom

theorem fieldMap_source (word : Carrier State) :
    fieldMap step read (sourceMap (sourceAction step) (observation sourcePoint) word) =
      sourceMap (sourceAction step) (observation read) word :=
  ConcreteCategory.congr_hom ((morphism step read).completionMorphism_source_naturality
    (compatible (sourceAction step) (observation sourcePoint))
    (compatible (sourceAction step) (observation read))) word

theorem fieldMap_point (state : State) :
    fieldMap step read (fieldPoint step sourcePoint state) = fieldPoint step read state :=
  fieldMap_source step read (sourcePoint state)

theorem fieldMap_uniformContinuous :
    @UniformContinuous _ _ (fieldUniform step (sourcePoint (State := State))) (fieldUniform step read)
      (fieldMap step read) :=
  completionMorphism_uniformContinuous (morphism step read)
    (compatible (sourceAction step) (observation sourcePoint))
    (compatible (sourceAction step) (observation read))

theorem fieldMap_measurable :
    @Measurable _ _ (fieldBorel step (sourcePoint (State := State))) (fieldBorel step read)
      (fieldMap step read) := by
  let : UniformSpace (Field step (sourcePoint (State := State))) := fieldUniform step sourcePoint
  let : UniformSpace (Field step read) := fieldUniform step read
  exact (fieldMap_uniformContinuous step read).continuous.borel_measurable

theorem fieldMap_action (value : Field step (sourcePoint (State := State))) :
    fieldMap step read (fieldAction step sourcePoint value) =
      fieldAction step read (fieldMap step read value) := by
  let : UniformSpace (Field step (sourcePoint (State := State))) := fieldUniform step sourcePoint
  let : UniformSpace (Field step read) := fieldUniform step read
  let target := data (sourceAction step) (observation read)
  let laws := compatible (sourceAction step) (observation read)
  let : ∀ stage, UniformSpace (target.StageQuotient stage) := stageUniform target
  let : T2Space (Field step read) := (coordinates_isUniformEmbedding target laws).isEmbedding.t2Space
  have dense := completionMap_denseRange
    (data (sourceAction step) (observation (sourcePoint (State := State))))
    (compatible (sourceAction step) (observation sourcePoint))
  have before := (endomorphism_uniformContinuous (sourceAction step) (observation sourcePoint)).continuous
  have after := (endomorphism_uniformContinuous (sourceAction step) (observation read)).continuous
  have mapped := (fieldMap_uniformContinuous step read).continuous
  have equality := dense.equalizer (mapped.comp before) (after.comp mapped) (by
    funext word
    change fieldMap step read (fieldAction step sourcePoint
        (sourceMap (sourceAction step) (observation sourcePoint) word)) =
      fieldAction step read (fieldMap step read
        (sourceMap (sourceAction step) (observation sourcePoint) word))
    rw [fieldMap_source]
    change fieldMap step read (endomorphism (sourceAction step) (observation sourcePoint)
      (sourceMap (sourceAction step) (observation sourcePoint) word)) = _
    rw [endomorphism_source, fieldMap_source]
    exact (endomorphism_source (sourceAction step) (observation read) word).symm)
  exact congrFun equality value

theorem fieldMap_source_fibre_iff (left right : Carrier State) :
    fieldMap step read (sourceMap (sourceAction step) (observation sourcePoint) left) =
      fieldMap step read (sourceMap (sourceAction step) (observation sourcePoint) right) ↔
      ∀ stage, observation read ((sourceAction step ^ stage) left) =
        observation read ((sourceAction step ^ stage) right) := by
  rw [fieldMap_source, fieldMap_source]
  exact source_fibre_iff (sourceAction step) (observation read) left right

private theorem action_power_point (state : State) (stage : Nat) :
    (sourceAction step ^ stage) (sourcePoint state) = sourcePoint (step^[stage] state) := by
  induction stage with
  | zero => rfl
  | succ stage previous =>
      rw [pow_succ', Function.iterate_succ_apply']
      exact (congrArg (sourceAction step) previous).trans (sourceAction_point step (step^[stage] state))

theorem native_fibre_iff (left right : State) :
    fieldMap step read (fieldPoint step sourcePoint left) =
      fieldMap step read (fieldPoint step sourcePoint right) ↔
      ∀ stage, read (step^[stage] left) = read (step^[stage] right) := by
  change fieldMap step read (sourceMap _ _ (sourcePoint left)) =
    fieldMap step read (sourceMap _ _ (sourcePoint right)) ↔ _
  rw [fieldMap_source_fibre_iff]
  simp only [action_power_point, observation_point]

end
end SourceOwnedObservationHistory.FullProjection
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
