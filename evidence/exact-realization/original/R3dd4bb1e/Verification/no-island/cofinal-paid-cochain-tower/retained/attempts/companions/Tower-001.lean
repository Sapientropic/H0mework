import SaturationMonoid.GenericFoundation.Cofinal.Topology.Functor
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.Homotopy

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u v
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedPrimePowerCompletion

open CategoryTheory CategoryTheory.Limits

variable {I : Type v} (shape : ComplexShape I) (p : Nat.Primes)
variable (source : HomologicalComplex AddCommGrpCat.{u} shape)

local notation "Cochains" => HomologicalComplex (ModuleCat.{u} ℤ) shape

/-- Every original stage restriction is a map of the degreewise residual complexes. -/
def cochainStageTower : ℕᵒᵖ ⥤ Cochains :=
  Functor.ofOpSequence (X := fun j => ((stageFunctor p j).mapHomologicalComplex shape).obj source)
    (fun j => ((stageFunctorTransition p j).mapHomologicalComplex shape).app source)

/-- The existing coherent module limits form the cone of the actual stage complexes. -/
def cochainCompletionCone : Cone (cochainStageTower shape p source) :=
  Cone.mk (((completionFunctor p).mapHomologicalComplex shape).obj source)
    (NatTrans.ofOpSequence (fun j => ((completionFunctorRestriction p j).mapHomologicalComplex shape).app source)
      (by
        intro j
        rw [Functor.const_obj_map, Category.id_comp]
        rw [cochainStageTower, Functor.ofOpSequence_map_homOfLE_succ]
        have step := congrArg
          (fun (maps : completionFunctor p ⟶ stageFunctor p j) => (maps.mapHomologicalComplex shape).app source)
          (completion_functor_restriction_step p j)
        rw [NatTrans.mapHomologicalComplex_comp, NatTrans.comp_app] at step
        exact step.symm))

private def evaluationTowerIso (degree : I) :
    cochainStageTower shape p source ⋙ HomologicalComplex.eval (ModuleCat.{u} ℤ) shape degree ≅
      tower (L := source.X degree) p := by
  let evaluated := cochainStageTower shape p source ⋙ HomologicalComplex.eval (ModuleCat.{u} ℤ) shape degree
  let original := tower (L := source.X degree) p
  let same : evaluated ⟶ original := NatTrans.ofOpSequence (fun _ => 𝟙 _)
    (by
      intro j
      rw [Category.comp_id, Category.id_comp]
      change ((cochainStageTower shape p source).map (homOfLE (Nat.le_add_right j 1)).op).f degree =
        original.map (homOfLE (Nat.le_add_right j 1)).op
      rw [cochainStageTower, Functor.ofOpSequence_map_homOfLE_succ]
      exact (Functor.ofOpSequence_map_homOfLE_succ _ j).symm)
  have : IsIso same := (NatTrans.isIso_iff_isIso_app same).2 (by
    intro j
    change IsIso (𝟙 (evaluated.obj j))
    infer_instance)
  exact asIso same

/-- The assembled cochain cone is the limit of the original stage tower. -/
def cochainCompletionIsLimit : IsLimit (cochainCompletionCone shape p source) := by
  apply HomologicalComplex.isLimitOfEval
  intro degree
  let evaluated := (HomologicalComplex.eval (ModuleCat.{u} ℤ) shape degree).mapCone (cochainCompletionCone shape p source)
  let compared := evaluationTowerIso shape p source degree
  apply (IsLimit.postcomposeHomEquiv compared evaluated).toFun
  refine IsLimit.ofIsoLimit (limit.isLimit (tower (L := source.X degree) p)) (Cone.ext (Iso.refl _) ?_)
  rintro ⟨j⟩
  change restriction (L := source.X degree) p j = 𝟙 _ ≫ (restriction (L := source.X degree) p j ≫ 𝟙 _)
  rw [Category.id_comp, Category.comp_id]

end SourceGeneratedPrimePowerCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
