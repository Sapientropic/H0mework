import H0mework.Versions.R18f91d79.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.Operations.Closure.Quotient
import H0mework.Realization.Completion.HistoryTransition

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationCompletion

open SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations SourceOperationPaidRelations
open CofinalHistorySettlement CofinalHistoryTransition

variable {S Root NextRoot : Type u} {V X : S → Type u} [∀ s, AddCommGroup (V s)]
variable {s : S} {old : Env V X} {before middle after : Expr V X s}
variable {prior : Trace old before middle} {next : Trace old before after}

local notation "history" "[" root "," paid "]" => prefixHistory root (exposure paid)

private theorem exposure_prefix (paid : words prior <+: words next) :
    (exposure prior).trace <+: (exposure next).trace := by
  let head := List.cons (PresentedRelationEventAt.generator before)
  let relation := PresentedRelationEventAt.relation (Generator := Expr V X s)
  have fromPrior : (exposure prior).trace = head ((words prior).map relation) :=
    congrArg head (events_trace prior)
  have fromNext : (exposure next).trace = head ((words next).map relation) :=
    congrArg head (events_trace next)
  exact Eq.mpr (congrArg₂ List.IsPrefix fromPrior fromNext)
    (List.cons_prefix_cons.mpr ⟨rfl, paid.map relation⟩)

private theorem retained_relations (root : RootedAccountedUnfolding Root)
    (nextRoot : RootedAccountedUnfolding NextRoot) (paid : words prior <+: words next) :
    history[root, prior].relationClosure ≤ history[nextRoot, next].relationClosure :=
  relations_next root (exposure prior) nextRoot (exposure next) (exposure_prefix paid).subset

def continuationRelation (root : RootedAccountedUnfolding Root) (nextRoot : RootedAccountedUnfolding NextRoot)
    (paid : words prior <+: words next) : history[root, prior].relationClosure →ₗ[ℤ] history[nextRoot, next].relationClosure :=
  Submodule.inclusion (retained_relations root nextRoot paid)

/-- A paid extension generates the original quotient transition from its retained source prefix. -/
def continuationTransition (root : RootedAccountedUnfolding Root) (nextRoot : RootedAccountedUnfolding NextRoot)
    (paid : words prior <+: words next) : GeneratedTransition history[root, prior] history[nextRoot, next] := by
  let generators := generators_next root (exposure prior) nextRoot (exposure next) (exposure_prefix paid).subset
  refine GeneratedTransition.create _ _ generators ?_
  intro word relation
  apply LinearMap.mem_ker.mpr
  change history[nextRoot, next].completionProjection (Submodule.inclusion generators word) = 0
  apply (Submodule.Quotient.mk_eq_zero _).2
  exact (continuationRelation root nextRoot paid ⟨word.val, relation⟩).property

theorem interpreted_prefix (p : Nat.Primes) (paid : words prior <+: words next) :
    words (trace p prior) <+: words (trace p next) := by
  exact Eq.mpr (congrArg₂ List.IsPrefix (trace_words p prior) (trace_words p next))
    (paid.map (wordMap p s))

private theorem inclusion_word_map {A B : Type u} [AddCommGroup A] [AddCommGroup B]
    {first last : Submodule ℤ A} {readFirst readLast : Submodule ℤ B}
    (included : first ≤ last) (readIncluded : readFirst ≤ readLast) (f : A →ₗ[ℤ] B)
    (read : first ≃ₗ[ℤ] readFirst) (readNext : last ≃ₗ[ℤ] readLast)
    (read_value : ∀ word, (read word).val = f word.val)
    (readNext_value : ∀ word, (readNext word).val = f word.val) (word : first) :
    readNext (Submodule.inclusion included word) = Submodule.inclusion readIncluded (read word) :=
  Subtype.ext ((readNext_value (Submodule.inclusion included word)).trans (read_value word).symm)

variable (root : RootedAccountedUnfolding Root) (nextRoot : RootedAccountedUnfolding NextRoot)
variable (p : Nat.Primes) (paid : words prior <+: words next)

/-- Interpretation preserves the inclusion of each prior relation in the actual later history. -/
theorem continuation_relation (word : history[root, prior].relationClosure) :
    relationEquiv nextRoot p next (continuationRelation root nextRoot paid word) =
      continuationRelation root nextRoot (interpreted_prefix p paid) (relationEquiv root p prior word) :=
  inclusion_word_map (retained_relations root nextRoot paid) (retained_relations root nextRoot (interpreted_prefix p paid))
    (wordMap p s) (relationEquiv root p prior) (relationEquiv nextRoot p next)
    (relation_equiv_value root p prior) (relation_equiv_value nextRoot p next) word

/-- The free maps restrict the same word map before and after the actual paid extension. -/
theorem continuation_generator (word : history[root, prior].generatorClosure) :
    let first := continuationTransition root nextRoot paid
    let interpreted := continuationTransition root nextRoot (interpreted_prefix p paid)
    generatorEquiv nextRoot p next (first.generatorMap _ _ word) =
      interpreted.generatorMap _ _ (generatorEquiv root p prior word) :=
  inclusion_word_map (continuationTransition root nextRoot paid).generatorCompatible
    (continuationTransition root nextRoot (interpreted_prefix p paid)).generatorCompatible
    (wordMap p s) (generatorEquiv root p prior) (generatorEquiv nextRoot p next)
    (generator_equiv_value root p prior) (generator_equiv_value nextRoot p next) word

/-- The generated continuation commutes with the complete interpreted relation quotient. -/
theorem continuation_completion (value : history[root, prior].CompletionCarrier) :
    let first := continuationTransition root nextRoot paid
    let interpreted := continuationTransition root nextRoot (interpreted_prefix p paid)
    completionEquiv nextRoot p next (first.completionMap _ _ value) =
      interpreted.completionMap _ _ (completionEquiv root p prior value) := by
  let source := history[root, prior]
  let target := history[nextRoot, next]
  let interpretedSource := history[root, trace p prior]
  let interpretedTarget := history[nextRoot, trace p next]
  let first := continuationTransition root nextRoot paid
  let interpreted := continuationTransition root nextRoot (interpreted_prefix p paid)
  let startEquiv := completionEquiv root p prior
  let endEquiv := completionEquiv nextRoot p next
  let push := first.completionMap source target
  let pushInterpreted := interpreted.completionMap interpretedSource interpretedTarget
  obtain ⟨word, rfl⟩ := source.relationInGeneratorClosure.mkQ_surjective value
  change endEquiv (push (source.completionProjection word)) =
    pushInterpreted (startEquiv (source.completionProjection word))
  have firstStep := GeneratedTransition.completionMap_projection source target first word
  have nextStep := GeneratedTransition.completionMap_projection interpretedSource interpretedTarget
    interpreted (generatorEquiv root p prior word)
  exact (congrArg (fun quotient : target.CompletionCarrier => endEquiv quotient) firstStep).trans
    ((completion_equiv_projection nextRoot p next (first.generatorMap source target word)).trans
    ((congrArg (fun generator : interpretedTarget.generatorClosure => interpretedTarget.completionProjection generator)
      (continuation_generator root nextRoot p paid word)).trans
    (nextStep.symm.trans (congrArg (fun quotient : interpretedSource.CompletionCarrier => pushInterpreted quotient)
      (completion_equiv_projection root p prior word).symm))))

end SourceOperationCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
