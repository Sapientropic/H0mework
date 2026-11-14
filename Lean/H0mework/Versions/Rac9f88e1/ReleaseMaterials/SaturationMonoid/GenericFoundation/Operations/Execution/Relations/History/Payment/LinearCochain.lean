import H0mework.Versions.Rac9f88e1.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Relations.History.Payment.LinearFibre
import H0mework.Versions.R18f91d79.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.Operations.Closure.Continuation.Cochain

set_option autoImplicit false
set_option Elab.async false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationPaidRelations

open CategoryTheory SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations
open SourceOperationScalarPresentation
open CofinalHistorySettlement CofinalRelationGeneratedComplex

noncomputable section
universe u
variable {S A B : Type u} {V X : S → Type u} [∀ s, AddCommGroup (V s)]
variable {s : S} {environment : Env V X}
variable {op : V s →+ V s} {body : Expr V X s} {total input : V s}
variable {parent : Trace environment (.linear op body) (.const total)}
variable {child : Trace environment body (.const input)}

local notation "history" "[" root "," trace "]" => prefixHistory root (exposure trace)
local notation "Word" => Formal ℤ V X s

private theorem contextualTerminal (parentRoot : RootedAccountedUnfolding B)
    (actual : Trace.LinearInterleaving op parent child) :
    (Finsupp.single (.linear op (.const input)) 1 : Word) ∈ history[parentRoot,parent].generatorClosure := by
  have terminal := (terminalGenerator parentRoot parent).property
  change (Finsupp.single (.const total) 1 : Word) ∈ history[parentRoot,parent].generatorClosure at terminal
  have edge : (Finsupp.single (.linear op (.const input)) 1 - Finsupp.single (.const total) 1 : Word)
      ∈ history[parentRoot,parent].relationClosure := by
    rw [payment_relation_closure, write_payment_range]
    apply Submodule.subset_span
    change _ ∈ words parent
    rw [linear_words actual]
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  have restored := Submodule.add_mem _ ((history[parentRoot,parent]).relationClosure_le_generatorClosure edge) terminal
  simpa only [sub_add_cancel] using restored

private theorem linearGenerator_mem (childRoot : RootedAccountedUnfolding A)
    (parentRoot : RootedAccountedUnfolding B) (actual : Trace.LinearInterleaving op parent child)
    (generator : history[childRoot,child].generatorClosure) :
    linearWord op generator.val ∈ history[parentRoot,parent].generatorClosure := by
  let coefficient := coefficientSum generator.val
  let endpoint : Word := Finsupp.single (.const input) coefficient
  let delta : history[childRoot,child].relationClosure :=
    ⟨generator.val-endpoint, word_sub_terminal_in_relation childRoot child generator⟩
  have embedded := (linearRelation childRoot parentRoot actual delta).property
  rw [linear_relation_value childRoot parentRoot actual delta] at embedded
  have relation : linearWord op (generator.val-endpoint) ∈ history[parentRoot,parent].generatorClosure :=
    (history[parentRoot,parent]).relationClosure_le_generatorClosure embedded
  have atEndpoint : linearWord op endpoint ∈ history[parentRoot,parent].generatorClosure := by
    dsimp only [endpoint]
    rw [linearWord, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    simpa only [Finsupp.smul_single, smul_eq_mul, mul_one] using
      Submodule.smul_mem _ coefficient (contextualTerminal parentRoot actual)
  have result := Submodule.add_mem _ relation atEndpoint
  rw [map_sub, sub_add_cancel] at result
  exact result

/-- Interpret each generator in the retained linear context. -/
def linearGenerator (childRoot : RootedAccountedUnfolding A) (parentRoot : RootedAccountedUnfolding B)
    (actual : Trace.LinearInterleaving op parent child) :
    history[childRoot,child].generatorClosure →ₗ[ℤ] history[parentRoot,parent].generatorClosure :=
  LinearMap.codRestrict _ ((linearWord op).comp (history[childRoot,child]).generatorClosure.subtype)
    (linearGenerator_mem childRoot parentRoot actual)

theorem linear_differential (childRoot : RootedAccountedUnfolding A) (parentRoot : RootedAccountedUnfolding B)
    (actual : Trace.LinearInterleaving op parent child) (word : history[childRoot,child].relationClosure) :
    linearGenerator childRoot parentRoot actual (relationInclusion history[childRoot,child] word) =
      relationInclusion history[parentRoot,parent] (linearRelation childRoot parentRoot actual word) := by
  apply Subtype.ext
  change linearWord op word.val = (linearRelation childRoot parentRoot actual word).val
  exact (linear_relation_value childRoot parentRoot actual word).symm

open private relationComplexMap from H0mework.Versions.R18f91d79.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.Operations.Closure.Continuation.Cochain

/-- The two-term paid complexes are connected by the child's actual trace inclusion. -/
def linearCochain (childRoot : RootedAccountedUnfolding A) (parentRoot : RootedAccountedUnfolding B)
    (actual : Trace.LinearInterleaving op parent child) :
    natComplex history[childRoot,child] ⟶ natComplex history[parentRoot,parent] :=
  relationComplexMap history[childRoot,child] history[parentRoot,parent]
    (linearRelation childRoot parentRoot actual) (linearGenerator childRoot parentRoot actual)
    (linear_differential childRoot parentRoot actual)

/-- The same retained linear context transports the actual effect in every source update. -/
theorem linear_boundary_effect (parent : Trace environment (.linear op body) (.const total))
    (child : Trace environment body (.const input)) (increment : Env V X) :
    effectEvaluator (R := ℤ) environment increment
      (relationMap (R := ℤ) environment parent.relationWords) =
      op (effectEvaluator (R := ℤ) environment increment
        (relationMap (R := ℤ) environment child.relationWords)) := by
  rw [parent.relation_boundary, child.relation_boundary]
  simp only [map_sub, effectEvaluator, Finsupp.linearCombination_single, one_smul, Expr.effect, sub_zero]

end

end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationPaidRelations
