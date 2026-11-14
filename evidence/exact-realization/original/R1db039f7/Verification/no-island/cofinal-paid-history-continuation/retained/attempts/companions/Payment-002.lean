import SaturationMonoid.GenericFoundation.Cofinal.Topology.Operations.Closure.Continuation

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

private def prefixPayment (paid : words prior <+: words next) :
    (Fin (words prior).length →₀ ℤ) →ₗ[ℤ] (Fin (words next).length →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (Fin.castLEEmb paid.length_le)

private theorem write_prefix_payment (paid : words prior <+: words next) :
    (writePayment next).comp (prefixPayment paid) = writePayment prior := by
  apply Finsupp.lhom_ext
  intro index coefficient
  simp only [LinearMap.comp_apply, prefixPayment, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
    writePayment, Finsupp.linearCombination_single, List.get_eq_getElem]
  exact congrArg (fun word => coefficient • word) (paid.getElem index.isLt).symm

variable (root : RootedAccountedUnfolding Root) (nextRoot : RootedAccountedUnfolding NextRoot)

private theorem continuation_payment (paid : words prior <+: words next)
    (coefficient : Fin (words prior).length →₀ ℤ) :
    continuationRelation root nextRoot paid (relationPaymentEquiv root prior coefficient) =
      relationPaymentEquiv nextRoot next (prefixPayment paid coefficient) :=
  Subtype.ext (LinearMap.congr_fun (write_prefix_payment paid) coefficient).symm

/-- The old relation image has zero charge exactly on the newly paid suffix. -/
theorem continuation_relation_range (paid : words prior <+: words next)
    (word : history[nextRoot, next].relationClosure) :
    word ∈ LinearMap.range (continuationRelation root nextRoot paid) ↔
      ∀ index : Fin (words next).length, (words prior).length ≤ index.val →
        (relationPaymentEquiv nextRoot next).symm word index = 0 := by
  let embed := Fin.castLEEmb paid.length_le
  let source := relationPaymentEquiv root prior
  let target := relationPaymentEquiv nextRoot next
  let push := continuationRelation root nextRoot paid
  have coordinateRange : word ∈ LinearMap.range push ↔ target.symm word ∈ Set.range (Finsupp.mapDomain embed) := by
    constructor
    · rintro ⟨oldWord, rfl⟩
      let coeff := source.symm oldWord
      have written : push oldWord = target (prefixPayment paid coeff) :=
        (congrArg (fun relation => push relation) (source.apply_symm_apply oldWord)).symm.trans
          (continuation_payment root nextRoot paid coeff)
      exact ⟨coeff, ((congrArg (fun relation => target.symm relation) written).trans
        (target.symm_apply_apply (prefixPayment paid coeff))).symm⟩
    · rintro ⟨coeff, written⟩
      exact ⟨source coeff, (continuation_payment root nextRoot paid coeff).trans
        ((congrArg (fun coordinate => target coordinate) written).trans (target.apply_symm_apply word))⟩
  have outside (index : Fin (words next).length) : index ∉ Set.range embed ↔ (words prior).length ≤ index.val := by
    constructor
    · intro absent
      apply Nat.le_of_not_gt
      intro oldIndex
      exact absent ⟨⟨index.val, oldIndex⟩, Fin.ext rfl⟩
    · intro afterPrefix
      rintro ⟨oldIndex, exactIndex⟩
      have same : oldIndex.val = index.val := congrArg Fin.val exactIndex
      exact (Nat.not_lt_of_ge afterPrefix) (same ▸ oldIndex.isLt)
  rw [coordinateRange, Finsupp.mem_range_mapDomain_iff embed embed.injective (target.symm word)]
  simp only [outside]

/-- One actual paid append replaces the terminal generator by the new endpoint and its exact edge. -/
theorem continuation_terminal
    (written : words next = words prior ++ [Finsupp.single middle 1 - Finsupp.single after 1]) :
    let paid : words prior <+: words next := ⟨_, written.symm⟩
    let generated := continuationTransition root nextRoot paid
    let last : Fin (words next).length := ⟨(words prior).length, by simp only [written, List.length_append, List.length_cons,
      List.length_nil, Nat.zero_add, Nat.lt_succ_self]⟩
    let fresh := relationPaymentEquiv nextRoot next (Finsupp.single last 1)
    fresh.val = Finsupp.single middle 1 - Finsupp.single after 1 ∧
      generated.generatorMap _ _ (terminalGenerator root prior) = terminalGenerator nextRoot next +
        Submodule.inclusion history[nextRoot, next].relationClosure_le_generatorClosure fresh ∧
      fresh ∉ LinearMap.range (continuationRelation root nextRoot paid) := by
  dsimp only
  let paid : words prior <+: words next := ⟨_, written.symm⟩
  let last : Fin (words next).length := ⟨(words prior).length, by simp only [written, List.length_append, List.length_cons,
    List.length_nil, Nat.zero_add, Nat.lt_succ_self]⟩
  let fresh := relationPaymentEquiv nextRoot next (Finsupp.single last 1)
  have edge : fresh.val = Finsupp.single middle 1 - Finsupp.single after 1 := by
    change writePayment next (Finsupp.single last 1) = _
    rw [writePayment, Finsupp.linearCombination_single, one_smul, List.get_eq_getElem]
    simp only [last, written, List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_cons_zero]
  refine ⟨edge, ?_, ?_⟩
  · apply Subtype.ext
    change Finsupp.single middle 1 = Finsupp.single after 1 + fresh.val
    rw [edge, add_comm (Finsupp.single after 1), sub_add_cancel]
  · intro belongs
    have zero := (continuation_relation_range root nextRoot paid fresh).mp belongs last (Nat.le_refl _)
    have unit : (relationPaymentEquiv nextRoot next).symm fresh last = 1 :=
      (congrArg (fun coeff : Fin (words next).length →₀ ℤ => coeff last)
        ((relationPaymentEquiv nextRoot next).symm_apply_apply (Finsupp.single last 1))).trans (Finsupp.single_eq_same)
    exact one_ne_zero (unit.symm.trans zero)

end SourceOperationCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
