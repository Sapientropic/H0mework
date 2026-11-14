import SaturationMonoid.GenericFoundation.Cofinal.Topology.Operations.Closure.Continuation.Cochain.Cohomology

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationCompletion

open CategoryTheory CategoryTheory.Limits CofinalHistorySettlement CofinalHistoryTransition
open SourceOperationEffects SourceOperationExecution SourceOperationPaidRelations

open private observedCofork observedCoforkIsColimit observed_next_zero observedHomologyData from
  SaturationMonoid.GenericFoundation.Cofinal.Topology.Operations.Closure.Continuation.Cochain.Cohomology

variable {S Root NextRoot : Type u} {V X : S → Type u} [∀ s, AddCommGroup (V s)]
variable {s : S} {old : Env V X} {before middle after : Expr V X s}
variable (root : RootedAccountedUnfolding Root) (prior : Trace old before middle)
variable (nextRoot : RootedAccountedUnfolding NextRoot) (next : Trace old before after)
variable {F G : AddCommGrpCat.{u} ⥤ ModuleCat.{u} ℤ} [F.Additive] [G.Additive]

local notation "sourceComplex" => observedPaidComplex root prior F
local notation "targetComplex" => observedPaidComplex nextRoot next G
local notation "sourceCofork" => observedCofork root prior F
local notation "targetCofork" => observedCofork nextRoot next G
local notation "sourceIso" => paidObservedCohomologyIso root prior F
local notation "targetIso" => paidObservedCohomologyIso nextRoot next G

private theorem paid_cohomology_map_of_projection
    (f : sourceComplex ⟶ targetComplex) (read : (sourceCofork).pt ⟶ (targetCofork).pt)
    (square : f.f 1 ≫ (targetCofork).π = (sourceCofork).π ≫ read) :
    HomologicalComplex.homologyMap f 1 ≫ (targetIso).hom = (sourceIso).hom ≫ read := by
  let shape := ComplexShape.up ℕ
  let choose := HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} ℤ) shape 0 1 2
  let compare := HomologicalComplex.natIsoSc' (ModuleCat.{u} ℤ) shape 0 1 2
    (CochainComplex.prev_nat_succ 0) (CochainComplex.next ℕ 1)
  let mapData := ShortComplex.HomologyMapData.ofIsColimitCokernelCofork (choose.map f)
    (observed_next_zero root prior F) sourceCofork (observedCoforkIsColimit root prior F)
    (observed_next_zero nextRoot next G) targetCofork (observedCoforkIsColimit nextRoot next G) read square
  let sourceCoordinate : (sourceComplex.sc' 0 1 2).homology ⟶ (sourceCofork).pt :=
    (observedHomologyData root prior F).left.homologyIso.hom
  let targetCoordinate : (targetComplex.sc' 0 1 2).homology ⟶ (targetCofork).pt :=
    (observedHomologyData nextRoot next G).left.homologyIso.hom
  let fromSource := ShortComplex.homologyMap (compare.hom.app sourceComplex)
  let fromTarget := ShortComplex.homologyMap (compare.hom.app targetComplex)
  let raw := HomologicalComplex.homologyMap f 1
  let finite := ShortComplex.homologyMap (choose.map f)
  have reported : finite ≫ targetCoordinate = sourceCoordinate ≫ read := mapData.left.homologyMap_comm
  have before := congrArg (fun map => ShortComplex.homologyMap map) (compare.hom.naturality f)
  rw [ShortComplex.homologyMap_comp, ShortComplex.homologyMap_comp] at before
  have step : raw ≫ fromTarget = fromSource ≫ finite := before
  change raw ≫ (fromTarget ≫ targetCoordinate) = (fromSource ≫ sourceCoordinate) ≫ read
  calc
    _ = (raw ≫ fromTarget) ≫ targetCoordinate := (Category.assoc _ _ _).symm
    _ = (fromSource ≫ finite) ≫ targetCoordinate := congrArg (fun map => map ≫ targetCoordinate) step
    _ = fromSource ≫ (finite ≫ targetCoordinate) := Category.assoc _ _ _
    _ = fromSource ≫ (sourceCoordinate ≫ read) := congrArg (fun map => fromSource ≫ map) reported
    _ = _ := (Category.assoc _ _ _).symm

/-- The original quotient identifies the cohomology action of each actual topology comparison. -/
theorem paid_cohomology_restriction (comparison : F ⟶ G) :
    let complexMap := (comparison.mapHomologicalComplex (ComplexShape.up ℕ)).app (paidGroupComplex root prior)
    HomologicalComplex.homologyMap complexMap 1 ≫ (paidObservedCohomologyIso root prior G).hom =
      (paidObservedCohomologyIso root prior F).hom ≫
        comparison.app (AddCommGrpCat.of (prefixHistory root (exposure prior)).CompletionCarrier) := by
  let quotient := (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat).map
    (ModuleCat.ofHom (prefixHistory root (exposure prior)).completionProjection)
  exact paid_cohomology_map_of_projection root prior root prior _ _ (comparison.naturality quotient).symm

/-- The actual cochain continuation acts on cohomology through the existing original quotient transition. -/
theorem paid_cohomology_continuation (paid : words prior <+: words next) :
    let observed := continuationCochainThrough root prior nextRoot next paid F
    let source := prefixHistory root (exposure prior)
    let target := prefixHistory nextRoot (exposure next)
    let original := (continuationTransition root nextRoot paid).completionMap source target
    let mapped := F.map ((forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat).map (ModuleCat.ofHom original))
    HomologicalComplex.homologyMap observed.hom 1 ≫ (paidObservedCohomologyIso nextRoot next F).hom =
      (paidObservedCohomologyIso root prior F).hom ≫ mapped := by
  let source := prefixHistory root (exposure prior)
  let target := prefixHistory nextRoot (exposure next)
  let transition := continuationTransition root nextRoot paid
  let observe := forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat ⋙ F
  have original := transition.completionMap_comp_projection source target
  have square : ModuleCat.ofHom (transition.generatorMap source target) ≫ ModuleCat.ofHom target.completionProjection =
      ModuleCat.ofHom source.completionProjection ≫ ModuleCat.ofHom (transition.completionMap source target) :=
    ModuleCat.hom_ext original.symm
  have mapped := congrArg (fun action => observe.map action) square
  rw [Functor.map_comp, Functor.map_comp] at mapped
  exact paid_cohomology_map_of_projection root prior nextRoot next _ _ mapped

end SourceOperationCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
