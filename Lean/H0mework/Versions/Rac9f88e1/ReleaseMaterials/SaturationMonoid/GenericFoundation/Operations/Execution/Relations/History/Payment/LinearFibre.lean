import H0mework.Versions.Rac9f88e1.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Relations.History.Payment.LinearContext
import H0mework.Versions.R18f91d79.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Relations.History.Payment.Closure

set_option autoImplicit false
set_option Elab.async false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationPaidRelations

open SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations CofinalHistorySettlement

noncomputable section
universe u
variable {S A B : Type u} {V X : S → Type u} [∀ s, AddCommGroup (V s)]
variable {s : S} {environment : Env V X}
variable {op : V s →+ V s} {body : Expr V X s} {total input : V s}
variable {parent : Trace environment (.linear op body) (.const total)}
variable {child : Trace environment body (.const input)}

/-- The dependent child receipt embeds its original integer charges into the parent prefix. -/
def linearPayment (actual : Trace.LinearInterleaving op parent child) :
    (Fin (words child).length →₀ ℤ) →ₗ[ℤ] (Fin (words parent).length →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (Fin.castLEEmb (linear_count_le actual))

theorem linear_write_payment (actual : Trace.LinearInterleaving op parent child)
    (charges : Fin (words child).length →₀ ℤ) :
    writePayment parent (linearPayment actual charges) = linearWord op (writePayment child charges) := by
  have square : (writePayment parent).comp (linearPayment actual) =
      (linearWord op).comp (writePayment child) := by
    apply Finsupp.lhom_ext
    intro index coefficient
    simp only [LinearMap.comp_apply, linearPayment, Finsupp.lmapDomain_apply,
      Finsupp.mapDomain_single, writePayment, Finsupp.linearCombination_single, map_smul]
    exact congrArg (fun word => coefficient • word) (linear_word_at actual index)
  exact LinearMap.congr_fun square charges

local notation "history" "[" root "," trace "]" => prefixHistory root (exposure trace)

variable (childRoot : RootedAccountedUnfolding A) (parentRoot : RootedAccountedUnfolding B)

/-- Write the retained child relation in the actual parent's own relation closure. -/
def linearRelation (actual : Trace.LinearInterleaving op parent child) :
    history[childRoot,child].relationClosure →ₗ[ℤ] history[parentRoot,parent].relationClosure :=
  (relationPaymentEquiv parentRoot parent).toLinearMap.comp
    ((linearPayment actual).comp (relationPaymentEquiv childRoot child).symm.toLinearMap)

theorem linear_relation_value (actual : Trace.LinearInterleaving op parent child)
    (relation : history[childRoot,child].relationClosure) :
    (linearRelation childRoot parentRoot actual relation).val = linearWord op relation.val := by
  let charge := (relationPaymentEquiv childRoot child).symm relation
  have source : writePayment child charge = relation.val :=
    congrArg Subtype.val ((relationPaymentEquiv childRoot child).apply_symm_apply relation)
  change writePayment parent (linearPayment actual charge) = linearWord op relation.val
  exact (linear_write_payment actual charge).trans (congrArg (linearWord op) source)

/-- The original parent can recover every child relation, including its integer multiplicities. -/
def linearRelationBack (actual : Trace.LinearInterleaving op parent child) :
    history[parentRoot,parent].relationClosure →ₗ[ℤ] history[childRoot,child].relationClosure :=
  (relationPaymentEquiv childRoot child).toLinearMap.comp
    ((Finsupp.lcomapDomain (Fin.castLEEmb (linear_count_le actual)) (Fin.castLEEmb (linear_count_le actual)).injective).comp
      (relationPaymentEquiv parentRoot parent).symm.toLinearMap)

theorem linear_relation_recover (actual : Trace.LinearInterleaving op parent child) :
    Function.LeftInverse (linearRelationBack childRoot parentRoot actual)
      (linearRelation childRoot parentRoot actual) := by
  intro relation
  simp only [linearRelation, linearRelationBack, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, linearPayment, Finsupp.lmapDomain_apply]
  let embed := Fin.castLEEmb (linear_count_le actual)
  rw [Finsupp.leftInverse_lcomapDomain_mapDomain (R := ℤ) (M := ℤ) embed embed.injective
    ((relationPaymentEquiv childRoot child).symm relation), LinearEquiv.apply_symm_apply]

/-- A parent relation descends exactly when the parent's own action charge vanishes. -/
theorem linear_relation_range (actual : Trace.LinearInterleaving op parent child)
    (relation : history[parentRoot,parent].relationClosure) :
    relation ∈ LinearMap.range (linearRelation childRoot parentRoot actual) ↔
      ∀ i : Fin (words parent).length, (words child).length ≤ i.val →
        (relationPaymentEquiv parentRoot parent).symm relation i = 0 := by
  let embed := Fin.castLEEmb (linear_count_le actual)
  let source := relationPaymentEquiv childRoot child
  let target := relationPaymentEquiv parentRoot parent
  let push := linearRelation childRoot parentRoot actual
  have push_eq (charges : Fin (words child).length →₀ ℤ) :
      push (source charges) = target (Finsupp.mapDomain embed charges) := by
    change target (linearPayment actual (source.symm (source charges))) = _
    rw [LinearEquiv.symm_apply_apply]
    rfl
  have atCoordinates : relation ∈ LinearMap.range push ↔
      target.symm relation ∈ Set.range (Finsupp.mapDomain embed) := by
    constructor
    · rintro ⟨word, rfl⟩
      let charges := source.symm word
      have restored := push_eq charges
      rw [source.apply_symm_apply] at restored
      exact ⟨charges, ((congrArg target.symm restored).trans (target.symm_apply_apply _)).symm⟩
    · rintro ⟨charges, equal⟩
      exact ⟨source charges, (push_eq charges).trans ((congrArg target equal).trans (target.apply_symm_apply _))⟩
  have outside (i : Fin (words parent).length) :
      i ∉ Set.range embed ↔ (words child).length ≤ i.val := by
    constructor
    · intro absent
      apply Nat.le_of_not_gt
      intro inside
      exact absent ⟨⟨i.val,inside⟩,Fin.ext rfl⟩
    · intro beyond
      rintro ⟨j,equal⟩
      exact (Nat.not_lt_of_ge beyond) ((congrArg Fin.val equal) ▸ j.isLt)
  change relation ∈ LinearMap.range push ↔ ∀ i, (words child).length ≤ i.val → target.symm relation i = 0
  rw [atCoordinates, Finsupp.mem_range_mapDomain_iff embed embed.injective (target.symm relation)]
  simp only [outside]

end

end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationPaidRelations
