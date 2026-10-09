import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Producer.Closure

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Root
structure InputMaterial where
  guideNotation : List Char
  mrnaNotation : List Char
  referenceRna : Bases
  genomicReference : Bases
  originalPages : String
  registration : String
  provenance : String
structure SequenceMaterial where
  guide : RegisteredRna
  mrna : RegisteredRna
  editorCoding : Bases
  editorProtein : List Char
  genomic : Target.Edits → Bases
  coding : Target.Edits → Bases
  firstStop : Target.Edits → Option (List String)
  intendedRepair : Bases
structure ExperimentMaterial where
  rows : List AssayRow
  metric : String
  clinical : ClinicalRegistration
  infusions : List Clinical.Infusion
structure ResponseMaterial where
  assayNet : Nat → Option ℚ
  reportResidual : Nat → Option ℚ
  completeModelConsumer : Target.Edits → Bool × Option (List String)
  originalFirstTaper : List ℚ
  finalMedication : ℚ
  secondInfusion : Clinical.Infusion
def generatedInputMaterial : InputMaterial :=
  ⟨Source.rawGuide,Source.rawMrna,Source.referenceRna,Source.genomic,Source.originalPages,
    Source.registration,Source.sourceProvenance⟩
def generatedSequenceMaterial : SequenceMaterial :=
  ⟨Molecules.guide,Molecules.mrna,Molecules.editorCoding,Source.editorProtein,Target.genomic,Target.coding,
    Target.stopChain,Target.genomic ⟨false,true,false⟩⟩
def generatedExperimentMaterial : ExperimentMaterial :=
  ⟨Source.assays,Source.assayMetric,Source.clinical,Clinical.doses⟩
def generatedResponseMaterial : ResponseMaterial :=
  ⟨Assay.net?,Assay.residual?,Consumer.extension.revisedFace,Clinical.firstAttempt,
    Clinical.finalMedication,Clinical.second⟩
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Root
