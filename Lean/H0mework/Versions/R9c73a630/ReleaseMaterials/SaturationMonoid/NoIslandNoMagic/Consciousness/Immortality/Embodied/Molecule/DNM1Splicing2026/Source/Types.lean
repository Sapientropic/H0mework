import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.ChemicalGenomeInformation.Interface.OrientedChemicalGenomeCarrier

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.DNM1Splicing2026

abbrev Bases := ChemicalGenomeInformation.Interface.GenomeSequence

structure VariantKey where
  build : String
  chromosome : String
  position : Nat
  reference : String
  alternate : String
  strand : String
  deriving DecidableEq, Repr

structure SequenceContext where
  start : Nat
  stop : Nat
  dna : Bases
  rawDna : String
  deriving DecidableEq, Repr

structure Transcript where
  accession : String
  strand : String
  cdsStart : Nat
  cdsEnd : Nat
  exonStarts : List Nat
  exonEnds : List Nat
  deriving DecidableEq, Repr

/-- The integer is the original IEEE binary32 bit pattern, not a decimal rounding. -/
structure Trace where
  allele : String
  head : String
  name : String
  strand : String
  ontology : String
  metadata : String
  bits : List Nat
  deriving DecidableEq, Repr

structure Junction where
  start : Nat
  stop : Nat
  strand : String
  referenceNeuron : Nat
  referenceBlood : Nat
  alternateNeuron : Nat
  alternateBlood : Nat
  deriving DecidableEq, Repr

structure CdnaExperiment where
  source : String
  doi : String
  figure : String
  build : String
  transcript : String
  hgvs : String
  nextCodingCoordinate : Nat
  intronicDistance : Nat
  reference : String
  alternate : String
  strand : String
  sample : String
  rnaExtraction : String
  reverseTranscription : String
  readout : String
  instrument : String
  basecallSoftware : String
  insertion : String
  insertionBases : Bases
  reportedLength : Nat
  heterozygous : Bool
  deriving DecidableEq, Repr

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.DNM1Splicing2026
