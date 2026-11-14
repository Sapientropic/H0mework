import H0mework.Versions.R18f91d79.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.Operations.Closure.Continuation

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationCompletion

open SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations SourceOperationPaidRelations
open CofinalHistorySettlement CofinalHistoryTransition CofinalRelationGeneratedComplex

open private coefficientSum_on_payment from
  H0mework.Versions.R18f91d79.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Relations.History.Payment.Completion

open private generatorCoordinates generator_restore_value from
  H0mework.Versions.R18f91d79.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.Operations.Closure

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

private theorem read_inclusion {A : Type u} [AddCommGroup A] {source target : Submodule ℤ A}
    (included : source ≤ target) (read : A →ₗ[ℤ] source)
    (restores : ∀ word : source, read word.val = word) (word : source) :
    (read.comp target.subtype) (Submodule.inclusion included word) = word :=
  restores word

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
  read_inclusion (fun value belongs => (includeRelation ⟨value, belongs⟩).property)
    (readRelations root prior) (read_relation root prior) word

theorem continuation_generator_retract (word : history[root, prior].generatorClosure) :
    continuationGeneratorBack root prior nextRoot next (includeGenerator word) = word :=
  read_inclusion (continuationTransition root nextRoot paid).generatorCompatible
    (restoreGenerators root prior) (restore_generator root prior) word

private theorem read_balanced (word : history[root, prior].generatorClosure) (balanced : coefficientSum word.val = 0) :
    relationInclusion history[root, prior] (readRelations root prior word.val) = word := by
  have value := restore_value root prior word.val
  rw [balanced, Finsupp.single_zero, add_zero] at value
  exact Subtype.ext (value.symm.trans (congrArg Subtype.val (restore_generator root prior word)))

private theorem contraction_reads_difference {A : Type u} [AddCommGroup A]
    {oldGenerators newGenerators newRelations : Submodule ℤ A}
    (included : oldGenerators ≤ newGenerators) (relations : newRelations ≤ newGenerators)
    (back : newGenerators →ₗ[ℤ] oldGenerators) (read : A →ₗ[ℤ] newRelations) (charge : A →ₗ[ℤ] ℤ)
    (preserved : ∀ word, charge (back word).val = charge word.val)
    (balanced : ∀ word : newGenerators, charge word.val = 0 → Submodule.inclusion relations (read word.val) = word)
    (word : newGenerators) :
    Submodule.inclusion relations ((read.comp (newGenerators.subtype - oldGenerators.subtype.comp back)) word) =
      word - Submodule.inclusion included (back word) := by
  let difference := word - Submodule.inclusion included (back word)
  have zero : charge difference.val = 0 :=
    (map_sub charge word.val (back word).val).trans (sub_eq_zero.mpr (preserved word).symm)
  exact balanced difference zero

/-- Read the difference between a later word and its restored prefix in the actual paid relation basis. -/
def continuationHomotopyMap : history[nextRoot, next].generatorClosure →ₗ[ℤ] history[nextRoot, next].relationClosure :=
  (readRelations nextRoot next).comp (history[nextRoot, next].generatorClosure.subtype -
    history[root, prior].generatorClosure.subtype.comp (continuationGeneratorBack root prior nextRoot next))

theorem continuation_homotopy_generator (word : history[nextRoot, next].generatorClosure) :
    relationInclusion history[nextRoot, next] (continuationHomotopyMap root prior nextRoot next word) =
      word - includeGenerator (continuationGeneratorBack root prior nextRoot next word) :=
  contraction_reads_difference (continuationTransition root nextRoot paid).generatorCompatible
    history[nextRoot, next].relationClosure_le_generatorClosure
    (continuationGeneratorBack root prior nextRoot next) (readRelations nextRoot next) coefficientSum
    (fun value => restore_charge root prior value.val) (read_balanced nextRoot next) word

private theorem contraction_from_generator {R G NextR NextG : Type u}
    [AddCommGroup R] [AddCommGroup G] [AddCommGroup NextR] [AddCommGroup NextG]
    (sourceD : R →ₗ[ℤ] G) (nextD : NextR →ₗ[ℤ] NextG) (injective : Function.Injective nextD)
    (relForward : R →ₗ[ℤ] NextR) (genForward : G →ₗ[ℤ] NextG)
    (relBack : NextR →ₗ[ℤ] R) (genBack : NextG →ₗ[ℤ] G)
    (forward : ∀ x, genForward (sourceD x) = nextD (relForward x))
    (backward : ∀ x, genBack (nextD x) = sourceD (relBack x))
    (h : NextG →ₗ[ℤ] NextR) (equation : ∀ x, nextD (h x) = x - genForward (genBack x)) (x : NextR) :
    h (nextD x) = x - relForward (relBack x) := by
  have square := (congrArg (fun value => genForward value) (backward x)).trans (forward (relBack x))
  apply injective
  exact (equation (nextD x)).trans ((congrArg (fun value => nextD x - value) square).trans
    (map_sub nextD x (relForward (relBack x))).symm)

theorem continuation_homotopy_relation (word : history[nextRoot, next].relationClosure) :
    continuationHomotopyMap root prior nextRoot next (relationInclusion history[nextRoot, next] word) =
      word - includeRelation (continuationRelationBack root prior nextRoot next word) :=
  contraction_from_generator (relationInclusion history[root, prior]) (relationInclusion history[nextRoot, next])
    (Submodule.inclusion_injective history[nextRoot, next].relationClosure_le_generatorClosure)
    includeRelation includeGenerator (continuationRelationBack root prior nextRoot next)
    (continuationGeneratorBack root prior nextRoot next)
    (continuation_forward_differential root prior nextRoot next paid)
    (continuation_backward_differential root prior nextRoot next)
    (continuationHomotopyMap root prior nextRoot next) (continuation_homotopy_generator root prior nextRoot next paid) word

end SourceOperationCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
