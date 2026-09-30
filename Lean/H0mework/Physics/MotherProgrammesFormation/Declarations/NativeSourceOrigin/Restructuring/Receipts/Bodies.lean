import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Receipts.ReceiptFields

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringReceipts
open ResponsibilityLifecycle
noncomputable section

variable (R : RestructuringVocabulary.{0})

abbrev ChildBody (source : R.base.SourceEvent) (parent child : R.Obligation) :=
  R.DescendantAt source parent.sourceIncidence parent.content child.sourceIncidence child.content ×
  SourceAnchorTransport parent.sourceAnchor child.sourceAnchor ×
  R.LocalDischargePreservedAt source parent.content child.content

abbrev SplitBody (parent : R.Obligation) := Σ source : R.base.SourceEvent, Σ children : List R.Obligation,
  R.SplitCoverageAt source parent.content (children.map AdmittedObligation.content) ×
    ((child : {child // child ∈ children}) → ChildBody R source parent child.val)

def SplitBodyValid (parent : R.Obligation) (body : SplitBody R parent) : Prop :=
  body.2.1 ≠ [] ∧ R.base.sourceAnchor body.1 = parent.sourceAnchor ∧
    R.base.sourceIncidence body.1 = parent.sourceIncidence ∧
    ∀ child, child ∈ body.2.1 → SameDebtLineage parent child

def splitBodyEquiv (parent : R.Obligation) : SplitReceipt R parent ≃ {body : SplitBody R parent // SplitBodyValid R parent body} where
  toFun := fun receipt => ⟨⟨receipt.sourceEvent, receipt.children, receipt.coverage,
    fun child => (receipt.descendant child.val child.property, receipt.anchorTransport child.val child.property,
      receipt.localDischarge child.val child.property)⟩,
    receipt.children_nonempty, receipt.sourceOwnership.anchor_eq, receipt.sourceOwnership.incidence_eq, receipt.lineage⟩
  invFun := fun value => {
    sourceEvent := value.val.1
    sourceOwnership := ⟨value.property.2.1, value.property.2.2.1⟩
    children := value.val.2.1
    children_nonempty := value.property.1
    coverage := value.val.2.2.1
    descendant := fun child member => (value.val.2.2.2 ⟨child, member⟩).1
    anchorTransport := fun child member => (value.val.2.2.2 ⟨child, member⟩).2.1
    lineage := value.property.2.2.2
    localDischarge := fun child member => (value.val.2.2.2 ⟨child, member⟩).2.2 }
  left_inv := fun receipt => by cases receipt; rfl
  right_inv := by rintro ⟨⟨source, children, coverage, data⟩, valid⟩; rfl

abbrev MergeBody := Σ source : R.base.SourceEvent, Σ parents : List R.Obligation, Σ target : R.Obligation,
  R.MergeCoverageAt source (parents.map AdmittedObligation.content) target.content ×
    ((parent : {parent // parent ∈ parents}) → ChildBody R source parent.val target)

def MergeBodyValid (body : MergeBody R) : Prop :=
  body.2.1 ≠ [] ∧ R.base.sourceAnchor body.1 = body.2.2.1.sourceAnchor ∧
    R.base.sourceIncidence body.1 = body.2.2.1.sourceIncidence ∧
    ∀ parent, parent ∈ body.2.1 → SameDebtLineage parent body.2.2.1

def mergeBodyEquiv : MergeReceipt R ≃ {body : MergeBody R // MergeBodyValid R body} where
  toFun := fun receipt => ⟨⟨receipt.sourceEvent, receipt.parents, receipt.target, receipt.coverage,
    fun parent => (receipt.ancestor parent.val parent.property, receipt.anchorTransport parent.val parent.property,
      receipt.localDischarge parent.val parent.property)⟩,
    receipt.parents_nonempty, receipt.sourceOwnership.anchor_eq, receipt.sourceOwnership.incidence_eq, receipt.lineage⟩
  invFun := fun value => {
    sourceEvent := value.val.1
    parents := value.val.2.1
    parents_nonempty := value.property.1
    target := value.val.2.2.1
    sourceOwnership := ⟨value.property.2.1, value.property.2.2.1⟩
    coverage := value.val.2.2.2.1
    ancestor := fun parent member => (value.val.2.2.2.2 ⟨parent, member⟩).1
    anchorTransport := fun parent member => (value.val.2.2.2.2 ⟨parent, member⟩).2.1
    lineage := value.property.2.2.2
    localDischarge := fun parent member => (value.val.2.2.2.2 ⟨parent, member⟩).2.2 }
  left_inv := fun receipt => by cases receipt; rfl
  right_inv := by rintro ⟨⟨source, parents, target, coverage, data⟩, valid⟩; rfl

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringReceipts
