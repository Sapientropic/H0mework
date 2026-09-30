import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Receipts.ReceiptValidity

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringReceipts
open MotherRestructuringOrigin MotherObligationOrigin ResponsibilityLifecycle
noncomputable section

variable {old generated : Sorts} {left : Families old} {right : Families generated}
    (sorts : ∀ i, old i ≃ generated i) (families : FamilyMap sorts left right)
    {original : Operations old left} {output : Operations generated right}
    (p : OperationsAcross sorts families original output)

def childBodyEquiv (source : old 0) (parent child : AdmittedObligation (vocabulary old left original)) :
    ChildBody (restructuring old left original) source parent child ≃
      ChildBody (restructuring generated right output) (sorts 0 source)
        (obligationEquiv sorts families p parent) (obligationEquiv sorts families p child) :=
  Equiv.prodCongr (descendantEquiv sorts families p source parent child)
    (Equiv.prodCongr (obligationAnchorTransport sorts families p parent child)
      (localDischargeEquiv sorts families p source parent child))

def splitDataEquiv (parent : AdmittedObligation (vocabulary old left original)) :
    SplitBody (restructuring old left original) parent ≃
      SplitBody (restructuring generated right output) (obligationEquiv sorts families p parent) :=
  Equiv.sigmaCongr (sorts 0) (fun source => Equiv.sigmaCongr (listEquiv (obligationEquiv sorts families p)) (fun children =>
    Equiv.prodCongr (splitCoverageEquiv sorts families p source parent children)
      (Equiv.piCongr (listMemberEquiv (obligationEquiv sorts families p) children)
        (fun child => childBodyEquiv sorts families p source parent child.val))))

theorem split_valid_iff (parent : AdmittedObligation (vocabulary old left original))
    (body : SplitBody (restructuring old left original) parent) :
    SplitBodyValid (restructuring old left original) parent body ↔
      SplitBodyValid (restructuring generated right output) (obligationEquiv sorts families p parent)
        (splitDataEquiv sorts families p parent body) := by
  rcases body with ⟨source, children, coverage, data⟩
  exact and_congr (list_nonempty_iff (obligationEquiv sorts families p) children)
    (and_congr (anchor_ownership_iff sorts families p source parent)
      (and_congr (incidence_ownership_iff sorts families p source parent)
        (forall_members_iff (obligationEquiv sorts families p) children
          (SameDebtLineage parent) (SameDebtLineage (obligationEquiv sorts families p parent))
          (debt_lineage_iff sorts families p parent))))

/-- Complete original receipts, including whole anchor functions and every
dependent evidence value, have a genuine two-sided vocabulary transport. -/
def splitReceiptEquiv (parent : AdmittedObligation (vocabulary old left original)) :
    SplitReceipt (restructuring old left original) parent ≃
      SplitReceipt (restructuring generated right output) (obligationEquiv sorts families p parent) :=
  (splitBodyEquiv (restructuring old left original) parent).trans
    ((Equiv.subtypeEquiv (splitDataEquiv sorts families p parent) (split_valid_iff sorts families p parent)).trans
      (splitBodyEquiv (restructuring generated right output) (obligationEquiv sorts families p parent)).symm)

theorem split_source {parent : AdmittedObligation (vocabulary old left original)}
    (receipt : SplitReceipt (restructuring old left original) parent) :
    (splitReceiptEquiv sorts families p parent receipt).sourceEvent = sorts 0 receipt.sourceEvent := rfl

theorem split_children {parent : AdmittedObligation (vocabulary old left original)}
    (receipt : SplitReceipt (restructuring old left original) parent) :
    (splitReceiptEquiv sorts families p parent receipt).children = listEquiv (obligationEquiv sorts families p) receipt.children := rfl

def mergeDataEquiv : MergeBody (restructuring old left original) ≃ MergeBody (restructuring generated right output) :=
  Equiv.sigmaCongr (sorts 0) (fun source => Equiv.sigmaCongr (listEquiv (obligationEquiv sorts families p)) (fun parents =>
    Equiv.sigmaCongr (obligationEquiv sorts families p) (fun target =>
      Equiv.prodCongr (mergeCoverageEquiv sorts families p source parents target)
        (Equiv.piCongr (listMemberEquiv (obligationEquiv sorts families p) parents)
          (fun parent => childBodyEquiv sorts families p source parent.val target)))))

theorem merge_valid_iff (body : MergeBody (restructuring old left original)) :
    MergeBodyValid (restructuring old left original) body ↔
      MergeBodyValid (restructuring generated right output) (mergeDataEquiv sorts families p body) := by
  rcases body with ⟨source, parents, target, coverage, data⟩
  exact and_congr (list_nonempty_iff (obligationEquiv sorts families p) parents)
    (and_congr (anchor_ownership_iff sorts families p source target)
      (and_congr (incidence_ownership_iff sorts families p source target)
        (forall_members_iff (obligationEquiv sorts families p) parents
          (fun parent => SameDebtLineage parent target)
          (fun parent => SameDebtLineage parent (obligationEquiv sorts families p target))
          (fun parent => debt_lineage_iff sorts families p parent target))))

def mergeReceiptEquiv : MergeReceipt (restructuring old left original) ≃ MergeReceipt (restructuring generated right output) :=
  (mergeBodyEquiv (restructuring old left original)).trans
    ((Equiv.subtypeEquiv (mergeDataEquiv sorts families p) (merge_valid_iff sorts families p)).trans
      (mergeBodyEquiv (restructuring generated right output)).symm)

theorem merge_source (receipt : MergeReceipt (restructuring old left original)) :
    (mergeReceiptEquiv sorts families p receipt).sourceEvent = sorts 0 receipt.sourceEvent := rfl

theorem merge_parents (receipt : MergeReceipt (restructuring old left original)) :
    (mergeReceiptEquiv sorts families p receipt).parents = listEquiv (obligationEquiv sorts families p) receipt.parents := rfl

theorem merge_target (receipt : MergeReceipt (restructuring old left original)) :
    (mergeReceiptEquiv sorts families p receipt).target = obligationEquiv sorts families p receipt.target := rfl

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringReceipts
