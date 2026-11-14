import H0mework.Versions.R18f91d79.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.Cochain.Tower
import H0mework.Versions.R18f91d79.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.Operations.Closure.Continuation.Cochain

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationCompletion

open CategoryTheory CategoryTheory.Limits
open SourceGeneratedPrimePowerCompletion
open SourceOperationEffects SourceOperationExecution SourceOperationPaidRelations CofinalRelationGeneratedComplex

variable {S Root NextRoot : Type u} {V X : S → Type u} [∀ s, AddCommGroup (V s)]
variable {s : S} {old : Env V X} {before middle after : Expr V X s}
variable (root : RootedAccountedUnfolding Root) (prior : Trace old before middle)
variable (nextRoot : RootedAccountedUnfolding NextRoot) (next : Trace old before after)
variable (paid : words prior <+: words next)

abbrev paidGroupComplex : CochainComplex AddCommGrpCat.{u} ℕ :=
  ((forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (natComplex (prefixHistory root (exposure prior)))

private def groupContinuation : HomotopyEquiv (paidGroupComplex root prior) (paidGroupComplex nextRoot next) :=
  (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat).mapHomotopyEquiv
    (continuationCochainHomotopyEquiv root prior nextRoot next paid)

private def groupContraction : (paidGroupComplex nextRoot next).X 1 ⟶ (paidGroupComplex nextRoot next).X 0 :=
  (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat).map
    (ModuleCat.ofHom (continuationHomotopyMap root prior nextRoot next))

/-- Apply the actual cochain continuation and both of its homotopies in an additive observation. -/
def continuationCochainThrough (observe : AddCommGrpCat.{u} ⥤ ModuleCat.{u} ℤ) [observe.Additive] :=
  observe.mapHomotopyEquiv (groupContinuation root prior nextRoot next paid)

/-- A restriction reads the original forward map, inverse map and contracting component. -/
theorem continuation_cochain_naturality {F G : AddCommGrpCat.{u} ⥤ ModuleCat.{u} ℤ}
    [F.Additive] [G.Additive] (restriction : F ⟶ G) :
    let source := paidGroupComplex root prior
    let target := paidGroupComplex nextRoot next
    let compare := restriction.mapHomologicalComplex (ComplexShape.up ℕ)
    let left :=  continuationCochainThrough root prior nextRoot next paid F
    let right :=  continuationCochainThrough root prior nextRoot next paid G
    let contract := groupContraction root prior nextRoot next
    left.hom ≫ compare.app target = compare.app source ≫ right.hom ∧
      left.inv ≫ compare.app source = compare.app target ≫ right.inv ∧
      F.map contract ≫ restriction.app (target.X 0) = restriction.app (target.X 1) ≫ G.map contract := by
  let action := groupContinuation root prior nextRoot next paid
  let compare := restriction.mapHomologicalComplex (ComplexShape.up ℕ)
  exact ⟨compare.naturality action.hom, compare.naturality action.inv,
    restriction.naturality (groupContraction root prior nextRoot next)⟩

/-- The full coherent forward and inverse are the limit lifts of their actual stage actions. -/
theorem continuation_cochain_from_tower (p : Nat.Primes) :
    let shape := ComplexShape.up ℕ
    let source := paidGroupComplex root prior
    let target := paidGroupComplex nextRoot next
    let action := groupContinuation root prior nextRoot next paid
    let coherent := continuationCochainThrough root prior nextRoot next paid (completionFunctor p)
    coherent.hom = (cochainCompletionIsLimit shape p target).lift
      ((Cone.postcompose (cochainStageTowerMap shape p action.hom)).obj (cochainCompletionCone shape p source)) ∧
    coherent.inv = (cochainCompletionIsLimit shape p source).lift
      ((Cone.postcompose (cochainStageTowerMap shape p action.inv)).obj (cochainCompletionCone shape p target)) := by
  let action := groupContinuation root prior nextRoot next paid
  exact ⟨cochain_completion_map_from_tower _ p action.hom, cochain_completion_map_from_tower _ p action.inv⟩

end SourceOperationCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
