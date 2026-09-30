import H0mework.Realization.HistoryTopology.Carrier
import H0mework.Realization.ScalarCofinal.Tail

/-! Existing naturality squares generate continuity on the complete observation carriers. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedScalarCofinalTopology

open CategoryTheory SourceGeneratedScalarCofinalKernelCompletion
open SourceGeneratedScalarCofinalNaturality

noncomputable section

universe r u

variable {R : Type r} [CommRing R]
variable {Generator₁ Generator₂ : Type u}
variable [AddCommGroup Generator₁] [Module R Generator₁]
variable [AddCommGroup Generator₂] [Module R Generator₂]
variable {Carrier₁ Carrier₂ : Nat → Type u}
variable [∀ stage, AddCommGroup (Carrier₁ stage)] [∀ stage, Module R (Carrier₁ stage)]
variable [∀ stage, AddCommGroup (Carrier₂ stage)] [∀ stage, Module R (Carrier₂ stage)]
variable (data₁ : Data (R := R) (Generator := Generator₁) (Carrier := Carrier₁))

theorem restriction_uniformContinuous (compatible : data₁.Compatible) (stage : Nat) :
    @UniformContinuous _ _ (observationUniform data₁ compatible) (stageUniform data₁ stage)
      (data₁.restriction compatible stage) := by
  let : ∀ stage, UniformSpace (data₁.StageQuotient stage) := stageUniform data₁
  let : UniformSpace (data₁.Completion compatible) := observationUniform data₁ compatible
  exact (Pi.uniformContinuous_proj _ stage).comp
    (coordinates_isUniformEmbedding data₁ compatible).uniformContinuous

variable {data₁} {data₂ : Data (R := R) (Generator := Generator₂) (Carrier := Carrier₂)}

theorem completionMorphism_uniformContinuous (morphism : Morphism data₁ data₂)
    (compatible₁ : data₁.Compatible) (compatible₂ : data₂.Compatible) :
    @UniformContinuous _ _ (observationUniform data₁ compatible₁)
      (observationUniform data₂ compatible₂)
      (morphism.completionMorphism compatible₁ compatible₂) := by
  let : ∀ stage, UniformSpace (data₁.StageQuotient stage) := stageUniform data₁
  let : ∀ stage, UniformSpace (data₂.StageQuotient stage) := stageUniform data₂
  let : UniformSpace (data₁.Completion compatible₁) := observationUniform data₁ compatible₁
  let : UniformSpace (data₂.Completion compatible₂) := observationUniform data₂ compatible₂
  apply (coordinates_isUniformEmbedding data₂ compatible₂).isUniformInducing.uniformContinuous_iff.mpr
  apply uniformContinuous_pi.mpr
  intro stage
  have square : (fun value : data₁.Completion compatible₁ =>
      coordinates data₂ compatible₂ (morphism.completionMorphism compatible₁ compatible₂ value) stage) =
      fun value => morphism.stageQuotientMap stage (data₁.restriction compatible₁ stage value) := by
    funext value
    exact ConcreteCategory.congr_hom
      (morphism.completionMorphism_restriction compatible₁ compatible₂ stage) value
  change UniformContinuous (fun value =>
    coordinates data₂ compatible₂ (morphism.completionMorphism compatible₁ compatible₂ value) stage)
  rw [square]
  exact (DiscreteUniformity.uniformContinuous (data₁.StageQuotient stage)
    (morphism.stageQuotientMap stage)).comp
    (restriction_uniformContinuous data₁ compatible₁ stage)

theorem tail_uniformContinuous (data : Data (R := R) (Generator := Generator₁) (Carrier := Carrier₁))
    (compatible : data.Compatible) :
    @UniformContinuous _ _ (observationUniform data compatible)
      (observationUniform (SourceGeneratedScalarCofinalTail.tail data)
        (SourceGeneratedScalarCofinalTail.compatible data compatible))
      (SourceGeneratedScalarCofinalTail.completionMap data compatible) := by
  let : ∀ stage, UniformSpace (data.StageQuotient stage) := stageUniform data
  let : ∀ stage, UniformSpace ((SourceGeneratedScalarCofinalTail.tail data).StageQuotient stage) :=
    stageUniform (SourceGeneratedScalarCofinalTail.tail data)
  let : UniformSpace (data.Completion compatible) := observationUniform data compatible
  let : UniformSpace ((SourceGeneratedScalarCofinalTail.tail data).Completion
      (SourceGeneratedScalarCofinalTail.compatible data compatible)) :=
    observationUniform (SourceGeneratedScalarCofinalTail.tail data)
      (SourceGeneratedScalarCofinalTail.compatible data compatible)
  apply (coordinates_isUniformEmbedding (SourceGeneratedScalarCofinalTail.tail data)
    (SourceGeneratedScalarCofinalTail.compatible data compatible)).isUniformInducing.uniformContinuous_iff.mpr
  apply uniformContinuous_pi.mpr
  intro stage
  have square : (fun value : data.Completion compatible =>
      coordinates (SourceGeneratedScalarCofinalTail.tail data)
        (SourceGeneratedScalarCofinalTail.compatible data compatible)
        (SourceGeneratedScalarCofinalTail.completionMap data compatible value) stage) =
      fun value => data.restriction compatible (stage + 1) value := by
    funext value
    exact ConcreteCategory.congr_hom
      (SourceGeneratedScalarCofinalTail.completionMap_restriction data compatible stage) value
  change UniformContinuous (fun value =>
    coordinates (SourceGeneratedScalarCofinalTail.tail data)
      (SourceGeneratedScalarCofinalTail.compatible data compatible)
      (SourceGeneratedScalarCofinalTail.completionMap data compatible value) stage)
  rw [square]
  exact restriction_uniformContinuous data compatible (stage + 1)

end
end SourceGeneratedScalarCofinalTopology
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
