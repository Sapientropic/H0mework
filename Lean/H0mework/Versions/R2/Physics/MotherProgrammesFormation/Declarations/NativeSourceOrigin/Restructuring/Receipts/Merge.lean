import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Receipts.Split

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringReceipts
open MotherNetworkFactory MotherRestructuringOrigin MotherObligationOrigin ResponsibilityLifecycle
open scoped Classical
noncomputable section

abbrev MergeHeader (R : RestructuringVocabulary.{0}) := R.base.SourceEvent × List R.Obligation × R.Obligation

variable {R : RestructuringVocabulary.{0}} {I : Type} (coordinates : ReceiptCoordinates R) (index : I ↪ B)

def mergeHeaderAddress : MergeHeader R ↪ B :=
  productEmbedding coordinates.event (productEmbedding (listEmbedding coordinates.obligation) coordinates.obligation)

abbrev MergeParent (headers : I → MergeHeader R) := Σ i, {parent : R.Obligation // parent ∈ (headers i).2.1}

def mergeParentAddress (headers : I → MergeHeader R) : MergeParent headers ↪ B :=
  sigmaEmbedding index (fun i => (⟨Subtype.val, fun _ _ same => Subtype.ext same⟩ :
    {parent : R.Obligation // parent ∈ (headers i).2.1} ↪ R.Obligation).trans coordinates.obligation)

structure MergePure (headers : I → MergeHeader R) : Prop where
  nonempty : ∀ i, (headers i).2.1 ≠ []
  anchor : ∀ i, R.base.sourceAnchor (headers i).1 = (headers i).2.2.sourceAnchor
  incidence : ∀ i, R.base.sourceIncidence (headers i).1 = (headers i).2.2.sourceIncidence
  lineage : ∀ (parent : MergeParent headers), SameDebtLineage parent.2.val (headers parent.1).2.2

abbrev MergeCoverage (headers : I → MergeHeader R) (i : I) :=
  R.MergeCoverageAt (headers i).1 ((headers i).2.1.map AdmittedObligation.content) (headers i).2.2.content

abbrev MergeParentData (headers : I → MergeHeader R) (parent : MergeParent headers) :=
  R.DescendantAt (headers parent.1).1 parent.2.val.sourceIncidence parent.2.val.content
    (headers parent.1).2.2.sourceIncidence (headers parent.1).2.2.content ×
  R.LocalDischargePreservedAt (headers parent.1).1 parent.2.val.content (headers parent.1).2.2.content

abbrev MergeAnchors (headers : I → MergeHeader R) := (parent : MergeParent headers) →
  SourceAnchorTransport parent.2.val.sourceAnchor (headers parent.1).2.2.sourceAnchor

def mergeCoverageAddress (headers : I → MergeHeader R) (i : I) : MergeCoverage headers i ↪ B :=
  coordinates.merge (headers i).1 (headers i).2.1 (headers i).2.2

def mergeParentDataAddress (headers : I → MergeHeader R) (parent : MergeParent headers) : MergeParentData headers parent ↪ B :=
  productEmbedding (coordinates.descendant (headers parent.1).1 parent.2.val (headers parent.1).2.2)
    (coordinates.discharge (headers parent.1).1 parent.2.val (headers parent.1).2.2)

def mergeSection (headers : I → MergeHeader R) (checked : MergePure headers)
    (coverage : ∀ i, MergeCoverage headers i) (data : ∀ parent, MergeParentData headers parent)
    (anchors : MergeAnchors headers) : I → MergeReceipt R := fun i => {
  sourceEvent := (headers i).1
  parents := (headers i).2.1
  parents_nonempty := checked.nonempty i
  target := (headers i).2.2
  sourceOwnership := ⟨checked.anchor i, checked.incidence i⟩
  coverage := coverage i
  ancestor := fun parent member => (data ⟨i, parent, member⟩).1
  anchorTransport := fun parent member => anchors ⟨i, parent, member⟩
  lineage := fun parent member => checked.lineage ⟨i, parent, member⟩
  localDischarge := fun parent member => (data ⟨i, parent, member⟩).2 }

def formMergeParts (headerMaterial coverageMaterial parentMaterial anchorMaterial : M) : Option (I → MergeReceipt R) :=
  (NativeSection.form index (fun _ => mergeHeaderAddress coordinates) headerMaterial).bind (fun headers =>
    if checked : MergePure headers then
      (NativeSection.form index (mergeCoverageAddress coordinates headers) coverageMaterial).bind (fun coverage =>
        (NativeSection.form (mergeParentAddress coordinates index headers) (mergeParentDataAddress coordinates headers) parentMaterial).bind (fun data =>
          (formAnchorSection (mergeParentAddress coordinates index headers) coordinates.observation
            (fun parent => parent.2.val.sourceAnchor) (fun parent => (headers parent.1).2.2.sourceAnchor) anchorMaterial).map
            (mergeSection headers checked coverage data)))
    else none)

def formMergeSection (material : M) : Option (I → MergeReceipt R) :=
  let first := MotherHigherLawValue.split material
  let second := MotherHigherLawValue.split first.2
  let third := MotherHigherLawValue.split second.2
  formMergeParts coordinates index first.1 second.1 third.1 third.2

theorem every_merge_section (original : I → MergeReceipt R) :
    ∃ material : M, formMergeSection coordinates index material = some original := by
  let headers : I → MergeHeader R := fun i => ((original i).sourceEvent, (original i).parents, (original i).target)
  let coverage : ∀ i, MergeCoverage headers i := fun i => (original i).coverage
  let data : ∀ parent, MergeParentData headers parent := fun parent =>
    ((original parent.1).ancestor parent.2.val parent.2.property, (original parent.1).localDischarge parent.2.val parent.2.property)
  let anchors : MergeAnchors headers := fun parent => (original parent.1).anchorTransport parent.2.val parent.2.property
  have checked : MergePure headers := {
    nonempty := fun i => (original i).parents_nonempty
    anchor := fun i => (original i).sourceOwnership.anchor_eq
    incidence := fun i => (original i).sourceOwnership.incidence_eq
    lineage := fun parent => (original parent.1).lineage parent.2.val parent.2.property }
  obtain ⟨headerMaterial, headerFormed⟩ := NativeSection.every_section index (fun _ => mergeHeaderAddress coordinates) headers
  obtain ⟨coverageMaterial, coverageFormed⟩ := NativeSection.every_section index (mergeCoverageAddress coordinates headers) coverage
  obtain ⟨parentMaterial, parentFormed⟩ := NativeSection.every_section (mergeParentAddress coordinates index headers)
    (mergeParentDataAddress coordinates headers) data
  obtain ⟨anchorMaterial, anchorFormed⟩ := every_anchor_section (mergeParentAddress coordinates index headers) coordinates.observation
    (fun parent => parent.2.val.sourceAnchor) (fun parent => (headers parent.1).2.2.sourceAnchor) anchors
  refine ⟨MotherHigherLawValue.pack (headerMaterial, MotherHigherLawValue.pack
    (coverageMaterial, MotherHigherLawValue.pack (parentMaterial, anchorMaterial))), ?_⟩
  simp only [formMergeSection, MotherHigherLawValue.split_pack, formMergeParts, headerFormed, Option.bind_some,
    dif_pos checked, coverageFormed, parentFormed, anchorFormed, Option.map_some]
  congr 1

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringReceipts
