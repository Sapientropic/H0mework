import SaturationMonoid.GenericFoundation.Cofinal.Topology.Operations.Closure.Continuation

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationCompletion

open SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations SourceOperationPaidRelations
open CofinalHistorySettlement CofinalHistoryTransition CofinalRelationGeneratedComplex

open private coefficientSum_on_payment from
  SaturationMonoid.GenericFoundation.Operations.Execution.Relations.History.Payment.Completion

variable {S Root NextRoot : Type u} {V X : S → Type u} [∀ s, AddCommGroup (V s)]
variable {s : S} {old : Env V X} {before middle after : Expr V X s}
variable (root : RootedAccountedUnfolding Root) (prior : Trace old before middle)
variable (nextRoot : RootedAccountedUnfolding NextRoot) (next : Trace old before after)

local notation "history" "[" root "," paid "]" => prefixHistory root (exposure paid)
local notation "Word" => Formal ℤ V X s

private def readRelations : Word →ₗ[ℤ] history[root, prior].relationClosure :=
  (relationPaymentEquiv root prior).toLinearMap.comp (readPayment prior)

private theorem read_relation (relation : history[root, prior].relationClosure) :
    readRelations root prior relation.val = relation :=
  (relationPaymentEquiv root prior).apply_symm_apply relation

private theorem relation_charge (relation : history[root, prior].relationClosure) :
    coefficientSum relation.val = 0 := by
  let equiv := relationPaymentEquiv root prior
  have restored : writePayment prior (equiv.symm relation) = relation.val :=
    congrArg Subtype.val (equiv.apply_symm_apply relation)
  exact (congrArg (fun word : Word => coefficientSum word) restored).symm.trans
    (LinearMap.congr_fun (coefficientSum_on_payment prior) (equiv.symm relation))

private def restoreGenerators : Word →ₗ[ℤ] history[root, prior].generatorClosure :=
  ((relationInclusion history[root, prior]).comp (readRelations root prior)) +
    (LinearMap.toSpanSingleton ℤ _ (terminalGenerator root prior)).comp coefficientSum

private theorem restore_generator (word : history[root, prior].generatorClosure) :
    restoreGenerators root prior word.val = word := by
  have split := paid_differential_split root prior word
  rw [natComplex_d_zero_one] at split
  exact split

private theorem restore_charge (word : Word) :
    coefficientSum (restoreGenerators root prior word).val = coefficientSum word := by
  change coefficientSum ((readRelations root prior word).val + coefficientSum word • Finsupp.single middle 1) =
    coefficientSum word
  rw [map_add, relation_charge root prior, zero_add, map_smul]
  simp only [coefficientSum, Finsupp.linearCombination_single, smul_eq_mul, mul_one]

/-- Recover the original relation charges from the later paid word. -/
def continuationRelationBack : history[nextRoot, next].relationClosure →ₗ[ℤ] history[root, prior].relationClosure :=
  (readRelations root prior).comp history[nextRoot, next].relationClosure.subtype

/-- Recover the original generator with its original terminal unit. -/
def continuationGeneratorBack : history[nextRoot, next].generatorClosure →ₗ[ℤ] history[root, prior].generatorClosure :=
  (restoreGenerators root prior).comp history[nextRoot, next].generatorClosure.subtype

variable (paid : words prior <+: words next)

local notation "forward" => continuationTransition root nextRoot paid
local notation "includeRelation" => continuationRelation root nextRoot paid
local notation "includeGenerator" => forward.generatorMap history[root, prior] history[nextRoot, next]

/-- Both inclusions send the same raw word into the later generated complex. -/
theorem continuation_forward_differential (word : history[root, prior].relationClosure) :
    includeGenerator (relationInclusion history[root, prior] word) =
      relationInclusion history[nextRoot, next] (includeRelation word) :=
  Subtype.ext rfl

theorem continuation_backward_differential (word : history[nextRoot, next].relationClosure) :
    continuationGeneratorBack root prior nextRoot next (relationInclusion history[nextRoot, next] word) =
      relationInclusion history[root, prior] (continuationRelationBack root prior nextRoot next word) := by
  change relationInclusion history[root, prior] (readRelations root prior word.val) +
    coefficientSum word.val • terminalGenerator root prior = _
  rw [relation_charge nextRoot next word, zero_smul, add_zero]
  rfl

theorem continuation_relation_retract (word : history[root, prior].relationClosure) :
    continuationRelationBack root prior nextRoot next (includeRelation word) = word :=
  read_relation root prior word

theorem continuation_generator_retract (word : history[root, prior].generatorClosure) :
    continuationGeneratorBack root prior nextRoot next (includeGenerator word) = word :=
  restore_generator root prior word

/-- The unpaid difference between a later word and its restored prefix has the exact paid relation coordinates. -/
def continuationHomotopyMap : history[nextRoot, next].generatorClosure →ₗ[ℤ] history[nextRoot, next].relationClosure :=
  (readRelations nextRoot next).comp (history[nextRoot, next].generatorClosure.subtype -
    history[root, prior].generatorClosure.subtype.comp (continuationGeneratorBack root prior nextRoot next))

theorem continuation_homotopy_generator (word : history[nextRoot, next].generatorClosure) :
    relationInclusion history[nextRoot, next] (continuationHomotopyMap root prior nextRoot next word) =
      word - includeGenerator (continuationGeneratorBack root prior nextRoot next word) := by
  let difference := word - includeGenerator (continuationGeneratorBack root prior nextRoot next word)
  have balanced : coefficientSum difference.val = 0 := by
    change coefficientSum (word.val - (restoreGenerators root prior word.val).val) = 0
    rw [map_sub, restore_charge, sub_self]
  have split := paid_differential_split nextRoot next difference
  rw [natComplex_d_zero_one, balanced, zero_smul, add_zero] at split
  exact split

theorem continuation_homotopy_relation (word : history[nextRoot, next].relationClosure) :
    continuationHomotopyMap root prior nextRoot next (relationInclusion history[nextRoot, next] word) =
      word - includeRelation (continuationRelationBack root prior nextRoot next word) := by
  change readRelations nextRoot next
    (word.val - (continuationGeneratorBack root prior nextRoot next (relationInclusion history[nextRoot, next] word)).val) = _
  rw [continuation_backward_differential, map_sub, read_relation]
  have read := read_relation nextRoot next (includeRelation (continuationRelationBack root prior nextRoot next word))
  exact congrArg (fun payment => word - payment) read

end SourceOperationCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
