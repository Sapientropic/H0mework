import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Receipts.AnchorsAcross

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringReceipts
open MotherRestructuringOrigin MotherObligationOrigin ResponsibilityLifecycle
noncomputable section

def listMemberEquiv {A C : Type} (e : A ≃ C) (values : List A) :
    {value // value ∈ values} ≃ {value // value ∈ listEquiv e values} :=
  Equiv.subtypeEquiv e (by
    intro value
    change value ∈ values ↔ e value ∈ values.map e
    constructor
    · exact fun member => List.mem_map.mpr ⟨value, member, rfl⟩
    · intro member
      obtain ⟨other, member, same⟩ := List.mem_map.mp member
      exact e.injective same ▸ member)

variable {old generated : Sorts} {left : Families old} {right : Families generated}
    (sorts : ∀ i, old i ≃ generated i) (families : FamilyMap sorts left right)
    {original : Operations old left} {output : Operations generated right}
    (p : OperationsAcross sorts families original output)

theorem obligation_content (value : AdmittedObligation (vocabulary old left original)) :
    (obligationEquiv sorts families p value).content = sorts 1 value.content := rfl

theorem list_content (values : List (AdmittedObligation (vocabulary old left original))) :
    (listEquiv (obligationEquiv sorts families p) values).map AdmittedObligation.content =
      (values.map AdmittedObligation.content).map (sorts 1) := by
  induction values with
  | nil => rfl
  | cons value rest ih => exact congrArg₂ List.cons (obligation_content sorts families p value) ih

def descendantEquiv (source : old 0) (parent child : AdmittedObligation (vocabulary old left original)) :
    (restructuring old left original).DescendantAt source parent.sourceIncidence parent.content child.sourceIncidence child.content ≃
      (restructuring generated right output).DescendantAt (sorts 0 source)
        (obligationEquiv sorts families p parent).sourceIncidence (obligationEquiv sorts families p parent).content
        (obligationEquiv sorts families p child).sourceIncidence (obligationEquiv sorts families p child).content := by
  let args : Args old (signature 26) := (source, parent.sourceIncidence, parent.content, child.sourceIncidence, child.content, PUnit.unit)
  have same : argsEquiv sorts (signature 26) args =
      (sorts 0 source, (obligationEquiv sorts families p parent).sourceIncidence, (obligationEquiv sorts families p parent).content,
        (obligationEquiv sorts families p child).sourceIncidence, (obligationEquiv sorts families p child).content, PUnit.unit) :=
    congrArg₂ (fun (a b : generated 7) => (sorts 0 source, a, sorts 1 parent.content, b, sorts 1 child.content, PUnit.unit))
      (obligation_incidence sorts families p parent).symm (obligation_incidence sorts families p child).symm
  exact (families 26 args).trans (Equiv.cast (congrArg (right 26) same))

def splitCoverageEquiv (source : old 0) (parent : AdmittedObligation (vocabulary old left original))
    (children : List (AdmittedObligation (vocabulary old left original))) :
    (restructuring old left original).SplitCoverageAt source parent.content (children.map AdmittedObligation.content) ≃
      (restructuring generated right output).SplitCoverageAt (sorts 0 source) (obligationEquiv sorts families p parent).content
        ((listEquiv (obligationEquiv sorts families p) children).map AdmittedObligation.content) := by
  let args : Args old (signature 27) := (source, parent.content, children.map AdmittedObligation.content, PUnit.unit)
  have same : argsEquiv sorts (signature 27) args =
      (sorts 0 source, (obligationEquiv sorts families p parent).content,
        (listEquiv (obligationEquiv sorts families p) children).map AdmittedObligation.content, PUnit.unit) :=
    congrArg (fun values : List (generated 1) => (sorts 0 source, sorts 1 parent.content, values, PUnit.unit))
      (list_content sorts families p children).symm
  exact (families 27 args).trans (Equiv.cast (congrArg (right 27) same))

def mergeCoverageEquiv (source : old 0) (parents : List (AdmittedObligation (vocabulary old left original)))
    (target : AdmittedObligation (vocabulary old left original)) :
    (restructuring old left original).MergeCoverageAt source (parents.map AdmittedObligation.content) target.content ≃
      (restructuring generated right output).MergeCoverageAt (sorts 0 source)
        ((listEquiv (obligationEquiv sorts families p) parents).map AdmittedObligation.content)
        (obligationEquiv sorts families p target).content := by
  let args : Args old (signature 28) := (source, parents.map AdmittedObligation.content, target.content, PUnit.unit)
  have same : argsEquiv sorts (signature 28) args =
      (sorts 0 source, (listEquiv (obligationEquiv sorts families p) parents).map AdmittedObligation.content,
        (obligationEquiv sorts families p target).content, PUnit.unit) :=
    congrArg (fun values : List (generated 1) => (sorts 0 source, values, sorts 1 target.content, PUnit.unit))
      (list_content sorts families p parents).symm
  exact (families 28 args).trans (Equiv.cast (congrArg (right 28) same))

def localDischargeEquiv (source : old 0) (parent child : AdmittedObligation (vocabulary old left original)) :
    (restructuring old left original).LocalDischargePreservedAt source parent.content child.content ≃
      (restructuring generated right output).LocalDischargePreservedAt (sorts 0 source)
        (obligationEquiv sorts families p parent).content (obligationEquiv sorts families p child).content :=
  families 29 (source, parent.content, child.content, PUnit.unit)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringReceipts
