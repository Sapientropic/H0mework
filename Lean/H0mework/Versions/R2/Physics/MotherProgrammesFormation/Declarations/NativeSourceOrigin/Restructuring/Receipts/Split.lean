import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Receipts.Sections

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringReceipts
open MotherNetworkFactory MotherRestructuringOrigin MotherObligationOrigin ResponsibilityLifecycle
open scoped Classical
noncomputable section

abbrev SplitHeader (R : RestructuringVocabulary.{0}) := R.base.SourceEvent × List R.Obligation

variable {R : RestructuringVocabulary.{0}} {I : Type}
    (coordinates : ReceiptCoordinates R) (index : I ↪ B) (parent : I → R.Obligation)

def splitHeaderAddress : SplitHeader R ↪ B := productEmbedding coordinates.event (listEmbedding coordinates.obligation)

abbrev SplitChild (headers : I → SplitHeader R) := Σ i, {child : R.Obligation // child ∈ (headers i).2}

def splitChildAddress (headers : I → SplitHeader R) : SplitChild headers ↪ B :=
  sigmaEmbedding index (fun i => (⟨Subtype.val, fun _ _ same => Subtype.ext same⟩ :
    {child : R.Obligation // child ∈ (headers i).2} ↪ R.Obligation).trans coordinates.obligation)

structure SplitPure (headers : I → SplitHeader R) : Prop where
  nonempty : ∀ i, (headers i).2 ≠ []
  anchor : ∀ i, R.base.sourceAnchor (headers i).1 = (parent i).sourceAnchor
  incidence : ∀ i, R.base.sourceIncidence (headers i).1 = (parent i).sourceIncidence
  lineage : ∀ (child : SplitChild headers), SameDebtLineage (parent child.1) child.2.val

abbrev SplitCoverage (headers : I → SplitHeader R) (i : I) :=
  R.SplitCoverageAt (headers i).1 (parent i).content ((headers i).2.map AdmittedObligation.content)

abbrev SplitChildData (headers : I → SplitHeader R) (child : SplitChild headers) :=
  R.DescendantAt (headers child.1).1 (parent child.1).sourceIncidence (parent child.1).content
    child.2.val.sourceIncidence child.2.val.content ×
  R.LocalDischargePreservedAt (headers child.1).1 (parent child.1).content child.2.val.content

abbrev SplitAnchors (headers : I → SplitHeader R) := (child : SplitChild headers) →
  SourceAnchorTransport (parent child.1).sourceAnchor child.2.val.sourceAnchor

def splitCoverageAddress (headers : I → SplitHeader R) (i : I) : SplitCoverage parent headers i ↪ B :=
  coordinates.split (headers i).1 (parent i) (headers i).2

def splitChildDataAddress (headers : I → SplitHeader R) (child : SplitChild headers) : SplitChildData parent headers child ↪ B :=
  productEmbedding (coordinates.descendant (headers child.1).1 (parent child.1) child.2.val)
    (coordinates.discharge (headers child.1).1 (parent child.1) child.2.val)

def splitSection (headers : I → SplitHeader R) (checked : SplitPure parent headers)
    (coverage : ∀ i, SplitCoverage parent headers i) (data : ∀ child, SplitChildData parent headers child)
    (anchors : SplitAnchors parent headers) : (i : I) → SplitReceipt R (parent i) := fun i => {
  sourceEvent := (headers i).1
  sourceOwnership := ⟨checked.anchor i, checked.incidence i⟩
  children := (headers i).2
  children_nonempty := checked.nonempty i
  coverage := coverage i
  descendant := fun child member => (data ⟨i, child, member⟩).1
  anchorTransport := fun child member => anchors ⟨i, child, member⟩
  lineage := fun child member => checked.lineage ⟨i, child, member⟩
  localDischarge := fun child member => (data ⟨i, child, member⟩).2 }

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
  let first := MotherHigherLawValue.split material
  let second := MotherHigherLawValue.split first.2
  let third := MotherHigherLawValue.split second.2
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
  refine ⟨MotherHigherLawValue.pack (headerMaterial, MotherHigherLawValue.pack
    (coverageMaterial, MotherHigherLawValue.pack (childMaterial, anchorMaterial))), ?_⟩
  simp only [formSplitSection, MotherHigherLawValue.split_pack, formSplitParts, headerFormed, Option.bind_some,
    dif_pos checked, coverageFormed, childFormed, anchorFormed, Option.map_some]
  congr 1

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringReceipts
