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

open private generatorCoordinates generator_restore_value from
  SaturationMonoid.GenericFoundation.Cofinal.Topology.Operations.Closure

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
  (generatorCoordinates root prior).symm.toLinearMap.comp ((readPayment prior).prod coefficientSum)

private theorem restore_generator (word : history[root, prior].generatorClosure) :
    restoreGenerators root prior word.val = word :=
  (generatorCoordinates root prior).symm_apply_apply word

private theorem restore_value (word : Word) :
    (restoreGenerators root prior word).val =
      writePayment prior (readPayment prior word) + Finsupp.single middle (coefficientSum word) :=
  generator_restore_value root prior (readPayment prior word) (coefficientSum word)

private theorem restore_charge (word : Word) :
    coefficientSum (restoreGenerators root prior word).val = coefficientSum word :=
  congrArg Prod.snd ((generatorCoordinates root prior).apply_symm_apply (readPayment prior word, coefficientSum word))

private theorem inclusions_commute {A : Type u} [AddCommGroup A]
    {p q r t : Submodule ℤ A} (left : p ≤ q) (right : r ≤ t) (first : p ≤ r) (second : q ≤ t) (x : p) :
    Submodule.inclusion second (Submodule.inclusion left x) =
      Submodule.inclusion right (Submodule.inclusion first x) :=
  Subtype.ext rfl

/-- Recover the original relation charges from the later paid word. -/
def continuationRelationBack : history[nextRoot, next].relationClosure →ₗ[ℤ] history[root, prior].relationClosure :=
  (readRelations root prior).comp history[nextRoot, next].relationClosure.subtype

/-- Recover the original generator with its original terminal unit. -/
def continuationGeneratorBack : history[nextRoot, next].generatorClosure →ₗ[ℤ] history[root, prior].generatorClosure :=
  (restoreGenerators root prior).comp history[nextRoot, next].generatorClosure.subtype

variable (paid : words prior <+: words next)

local notation "includeRelation" => continuationRelation root nextRoot paid
local notation "includeGenerator" =>
  GeneratedTransition.generatorMap history[root, prior] history[nextRoot, next] (continuationTransition root nextRoot paid)

/-- Both inclusions send the same raw word into the later generated complex. -/
theorem continuation_forward_differential (word : history[root, prior].relationClosure) :
    includeGenerator (relationInclusion history[root, prior] word) =
      relationInclusion history[nextRoot, next] (includeRelation word) :=
  inclusions_commute history[root, prior].relationClosure_le_generatorClosure
    history[nextRoot, next].relationClosure_le_generatorClosure
    (fun value belongs => (includeRelation ⟨value, belongs⟩).property)
    (continuationTransition root nextRoot paid).generatorCompatible word

theorem continuation_backward_differential (word : history[nextRoot, next].relationClosure) :
    continuationGeneratorBack root prior nextRoot next (relationInclusion history[nextRoot, next] word) =
      relationInclusion history[root, prior] (continuationRelationBack root prior nextRoot next word) := by
  have value := restore_value root prior word.val
  rw [relation_charge nextRoot next word, Finsupp.single_zero, add_zero] at value
  exact Subtype.ext value

theorem continuation_relation_retract (word : history[root, prior].relationClosure) :
    continuationRelationBack root prior nextRoot next (includeRelation word) = word :=
  read_relation root prior word

theorem continuation_generator_retract (word : history[root, prior].generatorClosure) :
    continuationGeneratorBack root prior nextRoot next (includeGenerator word) = word :=
  restore_generator root prior word

/-- Read the difference between a later word and its restored prefix in the actual paid relation basis. -/
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
  have value := restore_value nextRoot next difference.val
  rw [balanced, Finsupp.single_zero, add_zero] at value
  have same := congrArg Subtype.val (restore_generator nextRoot next difference)
  exact Subtype.ext (value.symm.trans same)

theorem continuation_homotopy_relation (word : history[nextRoot, next].relationClosure) :
    continuationHomotopyMap root prior nextRoot next (relationInclusion history[nextRoot, next] word) =
      word - includeRelation (continuationRelationBack root prior nextRoot next word) := by
  let differential := relationInclusion history[nextRoot, next]
  let restored := continuationRelationBack root prior nextRoot next word
  have backward := continuation_backward_differential root prior nextRoot next word
  have forward := continuation_forward_differential root prior nextRoot next paid restored
  have square := (congrArg (fun value : history[root, prior].generatorClosure => includeGenerator value) backward).trans forward
  have contraction := continuation_homotopy_generator root prior nextRoot next paid (differential word)
  apply Submodule.inclusion_injective history[nextRoot, next].relationClosure_le_generatorClosure
  exact contraction.trans ((congrArg (fun value => differential word - value) square).trans
    (map_sub differential word (includeRelation restored)).symm)

end SourceOperationCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
