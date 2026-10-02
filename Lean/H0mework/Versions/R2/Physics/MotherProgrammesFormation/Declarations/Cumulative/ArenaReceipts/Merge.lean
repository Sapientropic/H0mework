import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaReceipts.Split
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Receipts.Merge

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaReceipts
open MotherArenaNetwork MotherRestructuringOrigin MotherObligationOrigin ResponsibilityLifecycle
open scoped Classical
open MotherObligationOrigin
open MotherRestructuringReceipts
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

variable {R : RestructuringVocabulary.{0}} {I : Type} (coordinates : ReceiptCoordinates (rank := rank) R) (index : I ↪ MotherArenaHigher.Base rank)

def mergeHeaderAddress : MergeHeader R ↪ B :=
  MotherArenaObligation.productEmbedding coordinates.event (MotherArenaObligation.productEmbedding (MotherArenaRestructuringVocabulary.listEmbedding coordinates.obligation) coordinates.obligation)

def mergeParentAddress (headers : I → MergeHeader R) : MergeParent headers ↪ B :=
  MotherArenaObligation.sigmaEmbedding index (fun i => (⟨Subtype.val, fun _ _ same => Subtype.ext same⟩ :
    {parent : R.Obligation // parent ∈ (headers i).2.1} ↪ R.Obligation).trans coordinates.obligation)

def mergeCoverageAddress (headers : I → MergeHeader R) (i : I) : MergeCoverage headers i ↪ B :=
  coordinates.merge (headers i).1 (headers i).2.1 (headers i).2.2

def mergeParentDataAddress (headers : I → MergeHeader R) (parent : MergeParent headers) : MergeParentData headers parent ↪ B :=
  MotherArenaObligation.productEmbedding (coordinates.descendant (headers parent.1).1 parent.2.val (headers parent.1).2.2)
    (coordinates.discharge (headers parent.1).1 parent.2.val (headers parent.1).2.2)

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
  let first := (MotherArenaHigher.split rank) material
  let second := (MotherArenaHigher.split rank) first.2
  let third := (MotherArenaHigher.split rank) second.2
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
  refine ⟨(MotherArenaHigher.pack rank) (headerMaterial, (MotherArenaHigher.pack rank)
    (coverageMaterial, (MotherArenaHigher.pack rank) (parentMaterial, anchorMaterial))), ?_⟩
  simp only [formMergeSection, MotherArenaHigher.split_pack, formMergeParts, headerFormed, Option.bind_some,
    dif_pos checked, coverageFormed, parentFormed, anchorFormed, Option.map_some]
  congr 1

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaReceipts
