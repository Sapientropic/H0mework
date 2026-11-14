import H0mework.Versions.R18f91d79.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.Functor
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

/-- Every original stage restriction is a map of the degreewise residual complexes. -/
def cochainStageTower : ℕᵒᵖ ⥤ HomologicalComplex (ModuleCat.{u} ℤ) shape :=
  Functor.ofOpSequence (X := fun j => ((stageFunctor p j).mapHomologicalComplex shape).obj source)
    (fun j => ((stageFunctorTransition p j).mapHomologicalComplex shape).app source)

/-- The existing coherent module limits form the cone of the actual stage complexes. -/
def cochainCompletionCone : Cone (cochainStageTower shape p source) :=
  Cone.mk (((completionFunctor p).mapHomologicalComplex shape).obj source)
    (NatTrans.ofOpSequence (fun j => ((completionFunctorRestriction p j).mapHomologicalComplex shape).app source)
      (by
        intro j
        let upper := ((completionFunctorRestriction p (j+1)).mapHomologicalComplex shape).app source
        let lower := ((completionFunctorRestriction p j).mapHomologicalComplex shape).app source
        let edge := (homOfLE (Nat.le_add_right j 1)).op
        have written : (cochainStageTower shape p source).map edge =
            ((stageFunctorTransition p j).mapHomologicalComplex shape).app source :=
          Functor.ofOpSequence_map_homOfLE_succ _ j
        have step := congrArg
          (fun (maps : completionFunctor p ⟶ stageFunctor p j) => (maps.mapHomologicalComplex shape).app source)
          (completion_functor_restriction_step p j)
        rw [NatTrans.mapHomologicalComplex_comp, NatTrans.comp_app] at step
        change 𝟙 _ ≫ lower = upper ≫ (cochainStageTower shape p source).map edge
        exact (Category.id_comp lower).trans (step.symm.trans (congrArg (fun map => upper ≫ map) written.symm))))

private def evaluationTowerIso (degree : I) :
    cochainStageTower shape p source ⋙ HomologicalComplex.eval (ModuleCat.{u} ℤ) shape degree ≅
      tower (L := source.X degree) p := by
  let evaluated := cochainStageTower shape p source ⋙ HomologicalComplex.eval (ModuleCat.{u} ℤ) shape degree
  let original := tower (L := source.X degree) p
  let same : evaluated ⟶ original := NatTrans.ofOpSequence (fun _ => 𝟙 _)
    (by
      intro j
      let edge := (homOfLE (Nat.le_add_right j 1)).op
      have written : (cochainStageTower shape p source).map edge =
          ((stageFunctorTransition p j).mapHomologicalComplex shape).app source :=
        Functor.ofOpSequence_map_homOfLE_succ _ j
      have moduleEdge : original.map edge = ModuleCat.ofHom (transition (L := source.X degree) p j) :=
        Functor.ofOpSequence_map_homOfLE_succ _ j
      have sameEdge : evaluated.map edge = original.map edge :=
        (congrArg (fun map => map.f degree) written).trans moduleEdge.symm
      exact (Category.comp_id (evaluated.map edge)).trans (sameEdge.trans (Category.id_comp (original.map edge)).symm))
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

variable {source} {target : HomologicalComplex AddCommGrpCat.{u} shape}

/-- An actual cochain action generates the maps of all stages in the original restriction tower. -/
def cochainStageTowerMap (f : source ⟶ target) : cochainStageTower shape p source ⟶ cochainStageTower shape p target :=
  NatTrans.ofOpSequence (fun j => ((stageFunctor p j).mapHomologicalComplex shape).map f) (by
    intro j
    let step := (stageFunctorTransition p j).mapHomologicalComplex shape
    let upper := ((stageFunctor p (j+1)).mapHomologicalComplex shape).map f
    let lower := ((stageFunctor p j).mapHomologicalComplex shape).map f
    let edge := (homOfLE (Nat.le_add_right j 1)).op
    have writtenSource : (cochainStageTower shape p source).map edge = step.app source :=
      Functor.ofOpSequence_map_homOfLE_succ _ j
    have writtenTarget : (cochainStageTower shape p target).map edge = step.app target :=
      Functor.ofOpSequence_map_homOfLE_succ _ j
    exact (congrArg (fun written => written ≫ lower) writtenSource).trans
      ((step.naturality f).symm.trans (congrArg (fun written => upper ≫ written) writtenTarget.symm)))

theorem cochain_completion_map_restriction (f : source ⟶ target) (j : Nat) :
    ((completionFunctor p).mapHomologicalComplex shape).map f ≫
        (cochainCompletionCone shape p target).π.app (Opposite.op j) =
      (cochainCompletionCone shape p source).π.app (Opposite.op j) ≫ (cochainStageTowerMap shape p f).app (Opposite.op j) :=
  ((completionFunctorRestriction p j).mapHomologicalComplex shape).naturality f

/-- The coherent action is the limit lift of the actual stage actions. -/
theorem cochain_completion_map_from_tower (f : source ⟶ target) :
    ((completionFunctor p).mapHomologicalComplex shape).map f =
      (cochainCompletionIsLimit shape p target).lift
        ((Cone.postcompose (cochainStageTowerMap shape p f)).obj (cochainCompletionCone shape p source)) := by
  let completed := cochainCompletionIsLimit shape p target
  let image := (Cone.postcompose (cochainStageTowerMap shape p f)).obj (cochainCompletionCone shape p source)
  apply completed.hom_ext
  rintro ⟨j⟩
  exact (cochain_completion_map_restriction shape p f j).trans (completed.fac image (Opposite.op j)).symm

end SourceGeneratedPrimePowerCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
