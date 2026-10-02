import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaReceipts.Sections
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Receipts.Split

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

variable {R : RestructuringVocabulary.{0}} {I : Type}
    (coordinates : ReceiptCoordinates (rank := rank) R) (index : I ↪ MotherArenaHigher.Base rank) (parent : I → R.Obligation)

def splitHeaderAddress : SplitHeader R ↪ B := MotherArenaObligation.productEmbedding coordinates.event (MotherArenaRestructuringVocabulary.listEmbedding coordinates.obligation)

def splitChildAddress (headers : I → SplitHeader R) : SplitChild headers ↪ B :=
  MotherArenaObligation.sigmaEmbedding index (fun i => (⟨Subtype.val, fun _ _ same => Subtype.ext same⟩ :
    {child : R.Obligation // child ∈ (headers i).2} ↪ R.Obligation).trans coordinates.obligation)

def splitCoverageAddress (headers : I → SplitHeader R) (i : I) : SplitCoverage parent headers i ↪ B :=
  coordinates.split (headers i).1 (parent i) (headers i).2

def splitChildDataAddress (headers : I → SplitHeader R) (child : SplitChild headers) : SplitChildData parent headers child ↪ B :=
  MotherArenaObligation.productEmbedding (coordinates.descendant (headers child.1).1 (parent child.1) child.2.val)
    (coordinates.discharge (headers child.1).1 (parent child.1) child.2.val)

def formSplitParts (headerMaterial coverageMaterial childMaterial anchorMaterial : M) : Option ((i : I) → SplitReceipt R (parent i)) :=
  (NativeSection.form index (fun _ => splitHeaderAddress coordinates) headerMaterial).bind (fun headers =>
    if checked : SplitPure parent headers then
      (NativeSection.form index (splitCoverageAddress coordinates parent headers) coverageMaterial).bind (fun coverage =>
        (NativeSection.form (splitChildAddress coordinates index headers) (splitChildDataAddress coordinates parent headers) childMaterial).bind (fun data =>
          (formAnchorSection (splitChildAddress coordinates index headers) coordinates.observation
            (fun child => (parent child.1).sourceAnchor) (fun child => child.2.val.sourceAnchor) anchorMaterial).map
            (splitSection parent headers checked coverage data)))
    else none)

def formSplitSection (material : M) : Option ((i : I) → SplitReceipt R (parent i)) :=
  let first := (MotherArenaHigher.split rank) material
  let second := (MotherArenaHigher.split rank) first.2
  let third := (MotherArenaHigher.split rank) second.2
  formSplitParts coordinates index parent first.1 second.1 third.1 third.2

theorem every_split_section (original : (i : I) → SplitReceipt R (parent i)) :
    ∃ material : M, formSplitSection coordinates index parent material = some original := by
  let headers : I → SplitHeader R := fun i => ((original i).sourceEvent, (original i).children)
  let coverage : ∀ i, SplitCoverage parent headers i := fun i => (original i).coverage
  let data : ∀ child, SplitChildData parent headers child := fun child =>
    ((original child.1).descendant child.2.val child.2.property, (original child.1).localDischarge child.2.val child.2.property)
  let anchors : SplitAnchors parent headers := fun child => (original child.1).anchorTransport child.2.val child.2.property
  have checked : SplitPure parent headers := {
    nonempty := fun i => (original i).children_nonempty
    anchor := fun i => (original i).sourceOwnership.anchor_eq
    incidence := fun i => (original i).sourceOwnership.incidence_eq
    lineage := fun child => (original child.1).lineage child.2.val child.2.property }
  obtain ⟨headerMaterial, headerFormed⟩ := NativeSection.every_section index (fun _ => splitHeaderAddress coordinates) headers
  obtain ⟨coverageMaterial, coverageFormed⟩ := NativeSection.every_section index (splitCoverageAddress coordinates parent headers) coverage
  obtain ⟨childMaterial, childFormed⟩ := NativeSection.every_section (splitChildAddress coordinates index headers)
    (splitChildDataAddress coordinates parent headers) data
  obtain ⟨anchorMaterial, anchorFormed⟩ := every_anchor_section (splitChildAddress coordinates index headers) coordinates.observation
    (fun child => (parent child.1).sourceAnchor) (fun child => child.2.val.sourceAnchor) anchors
  refine ⟨(MotherArenaHigher.pack rank) (headerMaterial, (MotherArenaHigher.pack rank)
    (coverageMaterial, (MotherArenaHigher.pack rank) (childMaterial, anchorMaterial))), ?_⟩
  simp only [formSplitSection, MotherArenaHigher.split_pack, formSplitParts, headerFormed, Option.bind_some,
    dif_pos checked, coverageFormed, childFormed, anchorFormed, Option.map_some]
  congr 1

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaReceipts
