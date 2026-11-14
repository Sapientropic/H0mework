import H0mework.Versions.R58dfec4d.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.FiniteModulus.Factorial.Observation.Completion
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.Homotopy

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u v
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CofinalAllPrimeTopology

open CategoryTheory CategoryTheory.Limits
open private factorial_step from H0mework.Versions.R1f4eaffd.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.FiniteModulus.Factorial

variable {I : Type v} (shape : ComplexShape I)
variable (source : HomologicalComplex AddCommGrpCat.{u} shape)

/-- Each whole composite quotient gives the actual cochain stage of the factorial tower. -/
def factorialCochainTower : ℕᵒᵖ ⥤ HomologicalComplex (ModuleCat.{u} ℤ) shape :=
  Functor.ofOpSequence (X := fun stage => ((factorialStageFunctor stage).mapHomologicalComplex shape).obj source)
    (fun stage => ((factorialStageTransition stage).mapHomologicalComplex shape).app source)

def factorialCochainCone : Cone (factorialCochainTower shape source) :=
  Cone.mk ((factorialCompletionFunctor.mapHomologicalComplex shape).obj source)
    (NatTrans.ofOpSequence (fun stage => ((factorialFunctorRestriction stage).mapHomologicalComplex shape).app source) (by
      intro stage
      let lower := ((factorialFunctorRestriction stage).mapHomologicalComplex shape).app source
      let upper := ((factorialFunctorRestriction (stage+1)).mapHomologicalComplex shape).app source
      let step := ((factorialStageTransition stage).mapHomologicalComplex shape).app source
      let edge := (homOfLE (Nat.le_add_right stage 1)).op
      have written : (factorialCochainTower shape source).map edge = step :=
        Functor.ofOpSequence_map_homOfLE_succ _ stage
      have paid := congrArg
        (fun (restriction : factorialCompletionFunctor ⟶ factorialStageFunctor stage) =>
          (restriction.mapHomologicalComplex shape).app source) (factorial_functor_restriction_step stage)
      rw [NatTrans.mapHomologicalComplex_comp, NatTrans.comp_app] at paid
      change 𝟙 _ ≫ lower = upper ≫ (factorialCochainTower shape source).map edge
      exact (Category.id_comp lower).trans (paid.symm.trans (congrArg (fun arrow => upper ≫ arrow) written.symm))))

private def factorialEvaluationIso (degree : I) :
    factorialCochainTower shape source ⋙ HomologicalComplex.eval (ModuleCat.{u} ℤ) shape degree ≅
      factorialTower (L := source.X degree) := by
  let evaluated := factorialCochainTower shape source ⋙ HomologicalComplex.eval (ModuleCat.{u} ℤ) shape degree
  let actual := factorialTower (L := source.X degree)
  let compare : evaluated ⟶ actual := NatTrans.ofOpSequence (fun _ => 𝟙 _) (by
    intro stage
    let edge := (homOfLE (Nat.le_add_right stage 1)).op
    have written : (factorialCochainTower shape source).map edge =
        ((factorialStageTransition stage).mapHomologicalComplex shape).app source :=
      Functor.ofOpSequence_map_homOfLE_succ _ stage
    have component : evaluated.map edge = actual.map edge :=
      (congrArg (fun map => map.f degree) written).trans (factorial_step (L := source.X degree) stage).symm
    exact (Category.comp_id (evaluated.map edge)).trans (component.trans (Category.id_comp (actual.map edge)).symm))
  have : IsIso compare := (NatTrans.isIso_iff_isIso_app compare).2 (by
    intro stage
    change IsIso (𝟙 (evaluated.obj stage))
    infer_instance)
  exact asIso compare

/-- The cochain cone uses the original factorial limits degree by degree. -/
def factorialCochainIsLimit : IsLimit (factorialCochainCone shape source) := by
  apply HomologicalComplex.isLimitOfEval
  intro degree
  let evaluated := (HomologicalComplex.eval (ModuleCat.{u} ℤ) shape degree).mapCone (factorialCochainCone shape source)
  let compared := factorialEvaluationIso shape source degree
  apply (IsLimit.postcomposeHomEquiv compared evaluated).toFun
  refine IsLimit.ofIsoLimit (limit.isLimit (factorialTower (L := source.X degree))) (Cone.ext (Iso.refl _) ?_)
  rintro ⟨stage⟩
  let projection := factorialRestriction (L := source.X degree) stage
  change projection = 𝟙 _ ≫ (projection ≫ 𝟙 _)
  rw [Category.id_comp, Category.comp_id]

variable {source} {target : HomologicalComplex AddCommGrpCat.{u} shape}

/-- An actual cochain action supplies the whole factorial tower transformation. -/
def factorialCochainTowerMap (action : source ⟶ target) :
    factorialCochainTower shape source ⟶ factorialCochainTower shape target :=
  NatTrans.ofOpSequence (fun stage => ((factorialStageFunctor stage).mapHomologicalComplex shape).map action) (by
    intro stage
    let step := (factorialStageTransition stage).mapHomologicalComplex shape
    let upper := ((factorialStageFunctor (stage+1)).mapHomologicalComplex shape).map action
    let lower := ((factorialStageFunctor stage).mapHomologicalComplex shape).map action
    let edge := (homOfLE (Nat.le_add_right stage 1)).op
    have before : (factorialCochainTower shape source).map edge = step.app source :=
      Functor.ofOpSequence_map_homOfLE_succ _ stage
    have after : (factorialCochainTower shape target).map edge = step.app target :=
      Functor.ofOpSequence_map_homOfLE_succ _ stage
    exact (congrArg (fun arrow => arrow ≫ lower) before).trans
      ((step.naturality action).symm.trans (congrArg (fun arrow => upper ≫ arrow) after.symm)))

theorem factorial_cochain_map_restriction (action : source ⟶ target) (stage : Nat) :
    (factorialCompletionFunctor.mapHomologicalComplex shape).map action ≫
        (factorialCochainCone shape target).π.app (Opposite.op stage) =
      (factorialCochainCone shape source).π.app (Opposite.op stage) ≫
        (factorialCochainTowerMap shape action).app (Opposite.op stage) :=
  ((factorialFunctorRestriction stage).mapHomologicalComplex shape).naturality action

end CofinalAllPrimeTopology
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
