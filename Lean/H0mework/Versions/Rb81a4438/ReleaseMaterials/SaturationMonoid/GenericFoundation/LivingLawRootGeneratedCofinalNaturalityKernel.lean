import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.LivingLawRootGeneratedUniversalCofinalPerfectificationKernel
import H0mework.Realization.Perfectification.IntegralPair

/-!
# Natural transport of source-generated cofinal perfectifications

Two actual evaluator towers may be related by a generator map and compatible
stage maps.  This file derives the quotient-tower map, the map on categorical
cofinal completions, and the induced map on the canonical perfectifications.
The source/root equality and all commuting squares are explicit fields of the
transport, while no finite, free, projective, or determinant datum is added.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CofinalNaturality

open CategoryTheory
open CategoryTheory.Limits
open CofinalKernelCompletion
open CofinalKernelCompletion.RootGeneratedCofinalKernelCompletionAt
open UniversalCofinalPerfectification
open SourceGeneratedPerfectification
open SourceGeneratedCanonicalPerfectPair

noncomputable section

universe u w₁ w₂ w₃ d

variable {Root₁ : Type w₁} {Root₂ : Type w₂} {Root₃ : Type w₃}
variable {Generator₁ Generator₂ : Type u}
variable [AddCommGroup Generator₁] [AddCommGroup Generator₂]
variable {Carrier₁ Carrier₂ : Nat → Type u}
variable [∀ stage, AddCommGroup (Carrier₁ stage)]
variable [∀ stage, AddCommGroup (Carrier₂ stage)]
variable {Dual₁ : Type d} {Dual₂ : Type d}
variable [AddCommGroup Dual₁] [AddCommGroup Dual₂]
variable {occurrence₁ : RootedAccountedUnfolding
  (Root₁ × AdditiveCofinalEvaluatorData Generator₁ Carrier₁)}
variable {occurrence₂ : RootedAccountedUnfolding
  (Root₂ × AdditiveCofinalEvaluatorData Generator₂ Carrier₂)}
variable {face₁ : RootGeneratedCofinalKernelCompletionAt occurrence₁}
variable {face₂ : RootGeneratedCofinalKernelCompletionAt occurrence₂}
variable {calculation₁ : GeneratedCompatibilityCalculationAt face₁}
variable {calculation₂ : GeneratedCompatibilityCalculationAt face₂}

structure CofinalMorphism
    (face₁ : RootGeneratedCofinalKernelCompletionAt occurrence₁)
    (face₂ : RootGeneratedCofinalKernelCompletionAt occurrence₂)
    (calculation₁ : GeneratedCompatibilityCalculationAt face₁)
    (calculation₂ : GeneratedCompatibilityCalculationAt face₂) where
  generatorMap : Generator₁ →+ Generator₂
  stageMap : ∀ stage, Carrier₁ stage →+ Carrier₂ stage
  transition_naturality : ∀ stage,
    (stageMap stage).comp (face₁.transition stage) =
      (face₂.transition stage).comp (stageMap (stage + 1))
  evaluator_naturality : ∀ stage,
    (stageMap stage).comp (face₁.evaluator stage) =
      (face₂.evaluator stage).comp generatorMap
  rootMap : Root₁ → Root₂
  root_naturality : face₂.root = face₁.root.map rootMap

namespace CofinalMorphism

def id
    (face : RootGeneratedCofinalKernelCompletionAt occurrence₁)
    (calculation : GeneratedCompatibilityCalculationAt face) :
    CofinalMorphism face face calculation calculation where
  generatorMap := AddMonoidHom.id _
  stageMap := fun _ => AddMonoidHom.id _
  transition_naturality := by
    intro stage
    simp
  evaluator_naturality := by
    intro stage
    simp
  rootMap := _root_.id
  root_naturality := by
    simpa using (RootedAccountedUnfolding.map_id face.root).symm

def comp
    {Generator₃ : Type u}
    [AddCommGroup Generator₃]
    {Carrier₃ : Nat → Type u}
    [∀ stage, AddCommGroup (Carrier₃ stage)]
    {occurrence₃ : RootedAccountedUnfolding
      (Root₃ × AdditiveCofinalEvaluatorData Generator₃ Carrier₃)}
    {face₃ : RootGeneratedCofinalKernelCompletionAt occurrence₃}
    {calculation₃ : GeneratedCompatibilityCalculationAt face₃}
    (left : CofinalMorphism face₁ face₂ calculation₁ calculation₂)
    (right : CofinalMorphism face₂ face₃ calculation₂ calculation₃) :
    CofinalMorphism face₁ face₃ calculation₁ calculation₃ where
  generatorMap := right.generatorMap.comp left.generatorMap
  stageMap := fun stage => (right.stageMap stage).comp (left.stageMap stage)
  transition_naturality := by
    intro stage
    apply AddMonoidHom.ext
    intro value
    have leftLaw := DFunLike.congr_fun
      (left.transition_naturality stage) value
    have rightLaw := DFunLike.congr_fun
      (right.transition_naturality stage)
        (left.stageMap (stage + 1) value)
    simpa [AddMonoidHom.comp_apply] using
      (congrArg (right.stageMap stage) leftLaw).trans rightLaw
  evaluator_naturality := by
    intro stage
    apply AddMonoidHom.ext
    intro value
    have leftLaw := DFunLike.congr_fun
      (left.evaluator_naturality stage) value
    have rightLaw := DFunLike.congr_fun
      (right.evaluator_naturality stage)
        (left.generatorMap value)
    simpa [AddMonoidHom.comp_apply] using
      (congrArg (right.stageMap stage) leftLaw).trans rightLaw
  rootMap := right.rootMap ∘ left.rootMap
  root_naturality := by
    calc
      face₃.root = face₂.root.map right.rootMap := right.root_naturality
      _ = (face₁.root.map left.rootMap).map right.rootMap := by
        rw [left.root_naturality]
      _ = face₁.root.map (right.rootMap ∘ left.rootMap) := by
        exact RootedAccountedUnfolding.map_map right.rootMap left.rootMap face₁.root

def quotientMap
    (m : CofinalMorphism face₁ face₂ calculation₁ calculation₂) (stage : Nat) :
    face₁.StageQuotient stage →+ face₂.StageQuotient stage :=
  QuotientAddGroup.map
    (face₁.stageKernel stage) (face₂.stageKernel stage) m.generatorMap (by
      intro value value_mem
      change value ∈ (face₁.evaluator stage).ker at value_mem
      change m.generatorMap value ∈ (face₂.evaluator stage).ker
      rw [AddMonoidHom.mem_ker] at value_mem ⊢
      have naturality := DFunLike.congr_fun
        (m.evaluator_naturality stage) value
      change (m.stageMap stage) ((face₁.evaluator stage) value) =
        (face₂.evaluator stage) (m.generatorMap value) at naturality
      rw [value_mem, map_zero] at naturality
      exact naturality.symm)

theorem quotientMap_id
    (face : RootGeneratedCofinalKernelCompletionAt occurrence₁)
    (calculation : GeneratedCompatibilityCalculationAt face)
    (stage : Nat) :
    CofinalMorphism.quotientMap (CofinalMorphism.id face calculation) stage =
      AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro quotient
  induction quotient using QuotientAddGroup.induction_on with
  | H value =>
      rfl

theorem quotientMap_comp
    {Generator₃ : Type u}
    [AddCommGroup Generator₃]
    {Carrier₃ : Nat → Type u}
    [∀ stage, AddCommGroup (Carrier₃ stage)]
    {occurrence₃ : RootedAccountedUnfolding
      (Root₃ × AdditiveCofinalEvaluatorData Generator₃ Carrier₃)}
    {face₃ : RootGeneratedCofinalKernelCompletionAt occurrence₃}
    {calculation₃ : GeneratedCompatibilityCalculationAt face₃}
    (left : CofinalMorphism face₁ face₂ calculation₁ calculation₂)
    (right : CofinalMorphism face₂ face₃ calculation₂ calculation₃)
    (stage : Nat) :
    CofinalMorphism.quotientMap (CofinalMorphism.comp left right) stage =
      (CofinalMorphism.quotientMap right stage).comp
        (CofinalMorphism.quotientMap left stage) := by
  apply AddMonoidHom.ext
  intro quotient
  induction quotient using QuotientAddGroup.induction_on with
  | H value =>
      rfl

theorem quotientMap_mk
    (m : CofinalMorphism face₁ face₂ calculation₁ calculation₂)
    (stage : Nat) (value : Generator₁) :
    m.quotientMap stage
        (face₁.quotientMap stage value) =
      face₂.quotientMap stage (m.generatorMap value) :=
  rfl

theorem quotientMap_transition
    (m : CofinalMorphism face₁ face₂ calculation₁ calculation₂)
    (stage : Nat) :
    (m.quotientMap stage).comp
        (face₁.quotientTransition calculation₁ stage) =
      (face₂.quotientTransition calculation₂ stage).comp
        (m.quotientMap (stage + 1)) := by
  apply AddMonoidHom.ext
  intro quotient
  induction quotient using QuotientAddGroup.induction_on with
  | H value =>
      rfl

noncomputable def quotientNaturalTransformation
    (m : CofinalMorphism face₁ face₂ calculation₁ calculation₂) :
    face₁.quotientTower calculation₁ ⟶ face₂.quotientTower calculation₂ :=
  NatTrans.ofOpSequence
    (fun stage => AddCommGrpCat.ofHom (m.quotientMap stage))
    (fun stage => by
      simp only [RootGeneratedCofinalKernelCompletionAt.quotientTower,
        Functor.ofOpSequence_map_homOfLE_succ]
      apply AddCommGrpCat.ext
      intro quotient
      change m.quotientMap stage
          (face₁.quotientTransition calculation₁ stage quotient) =
        face₂.quotientTransition calculation₂ stage
          (m.quotientMap (stage + 1) quotient)
      exact DFunLike.congr_fun
        (m.quotientMap_transition stage) quotient
        )

noncomputable def completionMap
    (m : CofinalMorphism face₁ face₂ calculation₁ calculation₂) :
    face₁.completion calculation₁ ⟶ face₂.completion calculation₂ :=
  limMap m.quotientNaturalTransformation

theorem completionMap_restriction
    (m : CofinalMorphism face₁ face₂ calculation₁ calculation₂)
    (stage : Nat) :
    m.completionMap ≫
        face₂.restriction calculation₂ stage =
      face₁.restriction calculation₁ stage ≫
        AddCommGrpCat.ofHom (m.quotientMap stage) := by
  exact limMap_π m.quotientNaturalTransformation
    (Opposite.op stage)

theorem completionMap_source_naturality
    (m : CofinalMorphism face₁ face₂ calculation₁ calculation₂) :
    face₁.completionMap calculation₁ ≫ m.completionMap =
      AddCommGrpCat.ofHom m.generatorMap ≫ face₂.completionMap calculation₂ := by
  apply (limit.isLimit (face₂.quotientTower calculation₂)).hom_ext
  intro index
  rcases index with ⟨stage⟩
  change (face₁.completionMap calculation₁ ≫ m.completionMap) ≫
      face₂.restriction calculation₂ stage =
    (AddCommGrpCat.ofHom m.generatorMap ≫ face₂.completionMap calculation₂) ≫
      face₂.restriction calculation₂ stage
  calc
    (face₁.completionMap calculation₁ ≫ m.completionMap) ≫
          face₂.restriction calculation₂ stage =
        face₁.completionMap calculation₁ ≫
          (m.completionMap ≫ face₂.restriction calculation₂ stage) := by
            rw [Category.assoc]
    _ = face₁.completionMap calculation₁ ≫
          (face₁.restriction calculation₁ stage ≫
            AddCommGrpCat.ofHom (m.quotientMap stage)) := by
            rw [m.completionMap_restriction]
    _ = (face₁.completionMap calculation₁ ≫
          face₁.restriction calculation₁ stage) ≫
            AddCommGrpCat.ofHom (m.quotientMap stage) := by
            rw [Category.assoc]
    _ = AddCommGrpCat.ofHom (face₁.quotientMap stage) ≫
          AddCommGrpCat.ofHom (m.quotientMap stage) := by
            rw [face₁.completionMap_restriction]
    _ = AddCommGrpCat.ofHom m.generatorMap ≫
          AddCommGrpCat.ofHom (face₂.quotientMap stage) := by
            apply AddCommGrpCat.ext
            intro generator
            change m.quotientMap stage (face₁.quotientMap stage generator) =
              face₂.quotientMap stage (m.generatorMap generator)
            exact m.quotientMap_mk stage generator
    _ = (AddCommGrpCat.ofHom m.generatorMap ≫
          face₂.completionMap calculation₂) ≫
            face₂.restriction calculation₂ stage := by
            rw [Category.assoc, face₂.completionMap_restriction]

theorem completionMap_id
    (face : RootGeneratedCofinalKernelCompletionAt occurrence₁)
    (calculation : GeneratedCompatibilityCalculationAt face) :
    (CofinalMorphism.id face calculation).completionMap =
      𝟙 (face.completion calculation) := by
  apply (limit.isLimit (face.quotientTower calculation)).hom_ext
  intro index
  rcases index with ⟨stage⟩
  change (CofinalMorphism.id face calculation).completionMap ≫
      face.restriction calculation stage =
    (𝟙 (face.completion calculation)) ≫ face.restriction calculation stage
  rw [CofinalMorphism.completionMap_restriction,
    CofinalMorphism.quotientMap_id]
  simp

theorem completionMap_comp
    {Generator₃ : Type u}
    [AddCommGroup Generator₃]
    {Carrier₃ : Nat → Type u}
    [∀ stage, AddCommGroup (Carrier₃ stage)]
    {occurrence₃ : RootedAccountedUnfolding
      (Root₃ × AdditiveCofinalEvaluatorData Generator₃ Carrier₃)}
    {face₃ : RootGeneratedCofinalKernelCompletionAt occurrence₃}
    {calculation₃ : GeneratedCompatibilityCalculationAt face₃}
    (left : CofinalMorphism face₁ face₂ calculation₁ calculation₂)
    (right : CofinalMorphism face₂ face₃ calculation₂ calculation₃) :
    (CofinalMorphism.comp left right).completionMap =
      left.completionMap ≫ right.completionMap := by
  apply (limit.isLimit (face₃.quotientTower calculation₃)).hom_ext
  intro index
  rcases index with ⟨stage⟩
  change (CofinalMorphism.comp left right).completionMap ≫
      face₃.restriction calculation₃ stage =
    (left.completionMap ≫ right.completionMap) ≫
      face₃.restriction calculation₃ stage
  calc
    (CofinalMorphism.comp left right).completionMap ≫
          face₃.restriction calculation₃ stage =
        face₁.restriction calculation₁ stage ≫
          AddCommGrpCat.ofHom
            (CofinalMorphism.quotientMap (CofinalMorphism.comp left right) stage) := by
            exact CofinalMorphism.completionMap_restriction
              (CofinalMorphism.comp left right) stage
    _ = face₁.restriction calculation₁ stage ≫
          (AddCommGrpCat.ofHom (left.quotientMap stage) ≫
            AddCommGrpCat.ofHom (right.quotientMap stage)) := by
            rw [CofinalMorphism.quotientMap_comp]
            apply congrArg (fun arrow =>
              face₁.restriction calculation₁ stage ≫ arrow)
            apply AddCommGrpCat.ext
            intro value
            rfl
    _ = (left.completionMap ≫ right.completionMap) ≫
          face₃.restriction calculation₃ stage := by
            calc
              face₁.restriction calculation₁ stage ≫
                    (AddCommGrpCat.ofHom (left.quotientMap stage) ≫
                      AddCommGrpCat.ofHom (right.quotientMap stage)) =
                  (face₁.restriction calculation₁ stage ≫
                    AddCommGrpCat.ofHom (left.quotientMap stage)) ≫
                      AddCommGrpCat.ofHom (right.quotientMap stage) := by
                        rw [Category.assoc]
              _ = (left.completionMap ≫
                    face₂.restriction calculation₂ stage) ≫
                      AddCommGrpCat.ofHom (right.quotientMap stage) := by
                        rw [left.completionMap_restriction]
              _ = (left.completionMap ≫ right.completionMap) ≫
                    face₃.restriction calculation₃ stage := by
                        calc
                          (left.completionMap ≫
                              face₂.restriction calculation₂ stage) ≫
                              AddCommGrpCat.ofHom (right.quotientMap stage) =
                            left.completionMap ≫
                              (face₂.restriction calculation₂ stage ≫
                                AddCommGrpCat.ofHom (right.quotientMap stage)) := by
                                  rw [Category.assoc]
                          _ = left.completionMap ≫
                              (right.completionMap ≫
                                face₃.restriction calculation₃ stage) := by
                                  rw [right.completionMap_restriction]
                          _ = (left.completionMap ≫ right.completionMap) ≫
                              face₃.restriction calculation₃ stage := by
                                  rw [Category.assoc]
def completionLinearMap
    (m : CofinalMorphism face₁ face₂ calculation₁ calculation₂) :
    face₁.completion calculation₁ →ₗ[ℤ] face₂.completion calculation₂ :=
  m.completionMap.hom.toIntLinearMap

end CofinalMorphism

/-! ## Dual evaluation and perfectification transport -/

structure PerfectificationMorphism
    (Dual₁ : Type d) [AddCommGroup Dual₁]
    (Dual₂ : Type d) [AddCommGroup Dual₂]
    (m : CofinalMorphism face₁ face₂ calculation₁ calculation₂)
    (evaluation₁ : face₁.completion calculation₁ →ₗ[ℤ]
      Module.Dual ℤ Dual₁)
    (evaluation₂ : face₂.completion calculation₂ →ₗ[ℤ]
      Module.Dual ℤ Dual₂) where
  dualMap : Dual₂ →ₗ[ℤ] Dual₁
  evaluation_naturality :
    (SourceGeneratedPerfectification.inducedDualTarget dualMap).comp evaluation₁ =
      evaluation₂.comp m.completionLinearMap

def inducedPerfectificationMap
    (m : CofinalMorphism face₁ face₂ calculation₁ calculation₂)
    (evaluation₁ : face₁.completion calculation₁ →ₗ[ℤ]
      Module.Dual ℤ Dual₁)
    (evaluation₂ : face₂.completion calculation₂ →ₗ[ℤ]
      Module.Dual ℤ Dual₂)
    (transport : PerfectificationMorphism Dual₁ Dual₂ m evaluation₁ evaluation₂) :
    PerfectificationCarrier evaluation₁ →ₗ[ℤ]
      PerfectificationCarrier evaluation₂ :=
  SourceGeneratedPerfectification.inducedPerfectificationMap
    evaluation₁ evaluation₂
    m.completionLinearMap
    transport.dualMap transport.evaluation_naturality

theorem inducedPerfectificationMap_comp_canonical
    (m : CofinalMorphism face₁ face₂ calculation₁ calculation₂)
    (evaluation₁ : face₁.completion calculation₁ →ₗ[ℤ]
      Module.Dual ℤ Dual₁)
    (evaluation₂ : face₂.completion calculation₂ →ₗ[ℤ]
      Module.Dual ℤ Dual₂)
    (transport : PerfectificationMorphism Dual₁ Dual₂ m evaluation₁ evaluation₂) :
    (inducedPerfectificationMap m evaluation₁ evaluation₂ transport).comp
        (SourceGeneratedPerfectification.canonicalMap evaluation₁) =
      (SourceGeneratedPerfectification.canonicalMap evaluation₂).comp
        m.completionLinearMap :=
  SourceGeneratedPerfectification.inducedPerfectificationMap_comp
    evaluation₁ evaluation₂ m.completionLinearMap
    transport.dualMap transport.evaluation_naturality

theorem dualEmbedding_naturality
    (m : CofinalMorphism face₁ face₂ calculation₁ calculation₂)
    (evaluation₁ : face₁.completion calculation₁ →ₗ[ℤ]
      Module.Dual ℤ Dual₁)
    (evaluation₂ : face₂.completion calculation₂ →ₗ[ℤ]
      Module.Dual ℤ Dual₂)
    (transport : PerfectificationMorphism Dual₁ Dual₂ m evaluation₁ evaluation₂) :
    (SourceGeneratedPerfectification.dualEmbedding evaluation₂).comp
      (inducedPerfectificationMap m evaluation₁ evaluation₂ transport) =
      (SourceGeneratedPerfectification.inducedDualTarget transport.dualMap).comp
        (SourceGeneratedPerfectification.dualEmbedding evaluation₁) :=
  SourceGeneratedPerfectification.dualEmbedding_naturality
    evaluation₁ evaluation₂ m.completionLinearMap
    transport.dualMap transport.evaluation_naturality

/-! The same source map also transports the generated dual-image faces.  The
image subtype is not replaced by the full ambient dual. -/

def inducedCanonicalPerfectPairDualMap
    (m : CofinalMorphism face₁ face₂ calculation₁ calculation₂)
    (evaluation₁ : face₁.completion calculation₁ →ₗ[ℤ]
      Module.Dual ℤ Dual₁)
    (evaluation₂ : face₂.completion calculation₂ →ₗ[ℤ]
      Module.Dual ℤ Dual₂)
    (transport : PerfectificationMorphism Dual₁ Dual₂ m evaluation₁ evaluation₂) :
    SourceGeneratedCanonicalPerfectPair.GeneratedDual evaluation₁ →ₗ[ℤ]
      SourceGeneratedCanonicalPerfectPair.GeneratedDual evaluation₂ :=
  SourceGeneratedCanonicalPerfectPair.inducedDualImageMap
    evaluation₁ evaluation₂ m.completionLinearMap transport.dualMap
    transport.evaluation_naturality

theorem canonicalPerfectPair_map_naturality
    (m : CofinalMorphism face₁ face₂ calculation₁ calculation₂)
    (evaluation₁ : face₁.completion calculation₁ →ₗ[ℤ]
      Module.Dual ℤ Dual₁)
    (evaluation₂ : face₂.completion calculation₂ →ₗ[ℤ]
      Module.Dual ℤ Dual₂)
    (transport : PerfectificationMorphism Dual₁ Dual₂ m evaluation₁ evaluation₂) :
    (inducedCanonicalPerfectPairDualMap m evaluation₁ evaluation₂ transport).comp
        (SourceGeneratedCanonicalPerfectPair.generatedDualMap evaluation₁) =
      (SourceGeneratedCanonicalPerfectPair.generatedDualMap evaluation₂).comp
        (inducedPerfectificationMap m evaluation₁ evaluation₂ transport) :=
  SourceGeneratedCanonicalPerfectPair.generatedDualMap_naturality
    evaluation₁ evaluation₂ m.completionLinearMap transport.dualMap
    transport.evaluation_naturality

theorem canonicalPerfectPair_inclusion_naturality
    (m : CofinalMorphism face₁ face₂ calculation₁ calculation₂)
    (evaluation₁ : face₁.completion calculation₁ →ₗ[ℤ]
      Module.Dual ℤ Dual₁)
    (evaluation₂ : face₂.completion calculation₂ →ₗ[ℤ]
      Module.Dual ℤ Dual₂)
    (transport : PerfectificationMorphism Dual₁ Dual₂ m evaluation₁ evaluation₂) :
    (SourceGeneratedCanonicalPerfectPair.dualInclusion evaluation₂).comp
        (inducedCanonicalPerfectPairDualMap m evaluation₁ evaluation₂ transport) =
      (SourceGeneratedPerfectification.inducedDualTarget transport.dualMap).comp
        (SourceGeneratedCanonicalPerfectPair.dualInclusion evaluation₁) :=
  SourceGeneratedCanonicalPerfectPair.inducedDualImageMap_naturality
    evaluation₁ evaluation₂ m.completionLinearMap transport.dualMap
    transport.evaluation_naturality

theorem canonicalPerfectPair_coevaluation_naturality
    (m : CofinalMorphism face₁ face₂ calculation₁ calculation₂)
    (evaluation₁ : face₁.completion calculation₁ →ₗ[ℤ]
      Module.Dual ℤ Dual₁)
    (evaluation₂ : face₂.completion calculation₂ →ₗ[ℤ]
      Module.Dual ℤ Dual₂)
    (transport : PerfectificationMorphism Dual₁ Dual₂ m evaluation₁ evaluation₂) :
    (inducedPerfectificationMap m evaluation₁ evaluation₂ transport).comp
        (SourceGeneratedCanonicalPerfectPair.coevaluation evaluation₁) =
      (SourceGeneratedCanonicalPerfectPair.coevaluation evaluation₂).comp
        (inducedCanonicalPerfectPairDualMap m evaluation₁ evaluation₂ transport) :=
  SourceGeneratedCanonicalPerfectPair.coevaluation_naturality
    evaluation₁ evaluation₂ m.completionLinearMap transport.dualMap
    transport.evaluation_naturality

end
end CofinalNaturality
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
