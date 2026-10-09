import H0mework.Foundation.Relations.ConsumerFace

/-!
# An oriented chemical carrier for genome information

This is a domain table, not a second living-law calculus.  Canonical DNA bases
are represented by chemically discriminating atom/bond signatures; directed
phosphodiester incidence supplies order.  Sequence is a readout, while
topology, modification, damage and strand breaks remain a dependent residual.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace ChemicalGenomeInformation.Interface

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Representation

inductive CanonicalNucleobase where
  | adenine
  | cytosine
  | guanine
  | thymine
  deriving DecidableEq, Repr

abbrev GenomeSequence : Type := List CanonicalNucleobase

inductive BaseRingTopology where
  | fusedPurine
  | singlePyrimidine
  deriving DecidableEq, Repr

/-- A canonical neutral-base signature.  Besides atom and functional-group
counts, it records their numbered ring incidence and the glycosidic attachment
site.  Thus a positional isomer cannot enter merely by matching a formula. -/
structure CanonicalBaseBondSignature where
  carbonAtoms : Nat
  nitrogenAtoms : Nat
  oxygenAtoms : Nat
  ringTopology : BaseRingTopology
  carbonylDoubleBonds : Nat
  exocyclicAmineSingleBonds : Nat
  methylSubstituentSingleBonds : Nat
  ringNitrogenSites : List Nat
  carbonylSites : List Nat
  exocyclicAmineSites : List Nat
  methylSites : List Nat
  glycosidicNitrogenSite : Nat
  deriving DecidableEq, Repr

def baseBondSignature :
    CanonicalNucleobase → CanonicalBaseBondSignature
  | .adenine =>
      { carbonAtoms := 5
        nitrogenAtoms := 5
        oxygenAtoms := 0
        ringTopology := .fusedPurine
        carbonylDoubleBonds := 0
        exocyclicAmineSingleBonds := 1
        methylSubstituentSingleBonds := 0
        ringNitrogenSites := [1, 3, 7, 9]
        carbonylSites := []
        exocyclicAmineSites := [6]
        methylSites := []
        glycosidicNitrogenSite := 9 }
  | .cytosine =>
      { carbonAtoms := 4
        nitrogenAtoms := 3
        oxygenAtoms := 1
        ringTopology := .singlePyrimidine
        carbonylDoubleBonds := 1
        exocyclicAmineSingleBonds := 1
        methylSubstituentSingleBonds := 0
        ringNitrogenSites := [1, 3]
        carbonylSites := [2]
        exocyclicAmineSites := [4]
        methylSites := []
        glycosidicNitrogenSite := 1 }
  | .guanine =>
      { carbonAtoms := 5
        nitrogenAtoms := 5
        oxygenAtoms := 1
        ringTopology := .fusedPurine
        carbonylDoubleBonds := 1
        exocyclicAmineSingleBonds := 1
        methylSubstituentSingleBonds := 0
        ringNitrogenSites := [1, 3, 7, 9]
        carbonylSites := [6]
        exocyclicAmineSites := [2]
        methylSites := []
        glycosidicNitrogenSite := 9 }
  | .thymine =>
      { carbonAtoms := 5
        nitrogenAtoms := 2
        oxygenAtoms := 2
        ringTopology := .singlePyrimidine
        carbonylDoubleBonds := 2
        exocyclicAmineSingleBonds := 0
        methylSubstituentSingleBonds := 1
        ringNitrogenSites := [1, 3]
        carbonylSites := [2, 4]
        exocyclicAmineSites := []
        methylSites := [5]
        glycosidicNitrogenSite := 1 }

def decodeBaseBondSignature
    (signature : CanonicalBaseBondSignature) : Option CanonicalNucleobase :=
  if signature = baseBondSignature .adenine then some .adenine
  else if signature = baseBondSignature .cytosine then some .cytosine
  else if signature = baseBondSignature .guanine then some .guanine
  else if signature = baseBondSignature .thymine then some .thymine
  else none

structure UnaddressedBaseBondInventory where
  carbonAtoms : Nat
  nitrogenAtoms : Nat
  oxygenAtoms : Nat
  ringTopology : BaseRingTopology
  carbonylDoubleBonds : Nat
  exocyclicAmineSingleBonds : Nat
  methylSubstituentSingleBonds : Nat
  deriving DecidableEq, Repr

def unaddressedBaseBondInventory
    (signature : CanonicalBaseBondSignature) : UnaddressedBaseBondInventory :=
  { carbonAtoms := signature.carbonAtoms
    nitrogenAtoms := signature.nitrogenAtoms
    oxygenAtoms := signature.oxygenAtoms
    ringTopology := signature.ringTopology
    carbonylDoubleBonds := signature.carbonylDoubleBonds
    exocyclicAmineSingleBonds := signature.exocyclicAmineSingleBonds
    methylSubstituentSingleBonds := signature.methylSubstituentSingleBonds }

def decodeOrderedBaseBondSignatures :
    List CanonicalBaseBondSignature → Option GenomeSequence
  | [] => some []
  | signature :: rest => do
      let base ← decodeBaseBondSignature signature
      let sequence ← decodeOrderedBaseBondSignatures rest
      pure (base :: sequence)

inductive StrandTopology where
  | linear
  | circular
  deriving DecidableEq, Repr

inductive SugarStereochemistry where
  | betaDDeoxyribofuranose
  | betaDRibofuranose
  deriving DecidableEq, Repr

structure PolymerEndAnchors where
  fivePrime : Option Nat
  threePrime : Option Nat
  deriving DecidableEq, Repr

def canonicalDNAEndAnchors
    (topology : StrandTopology) (length : Nat) : PolymerEndAnchors :=
  match topology, length with
  | _, 0 => ⟨none, none⟩
  | .linear, length + 1 => ⟨some 0, some length⟩
  | .circular, _length + 1 => ⟨none, none⟩

inductive SiteChemicalState where
  | canonical
  | methylated
  | oxidized
  | abasic
  deriving DecidableEq, Repr

/-- Chemical state is indexed by the decoded sequence length.  Thus a residual
cannot be moved to a different genome without an explicit transport. -/
structure GenomeChemicalResidual (sequence : GenomeSequence) where
  topology : StrandTopology
  siteChemistry : List SiteChemicalState
  siteChemistryLength : siteChemistry.length = sequence.length
  strandBreakAfter : List Bool
  strandBreakLength : strandBreakAfter.length = sequence.length
  supercoiled : Bool

structure GenomeChemicalResidualData where
  topology : StrandTopology
  siteChemistry : List SiteChemicalState
  strandBreakAfter : List Bool
  supercoiled : Bool
  deriving DecidableEq, Repr

def GenomeChemicalResidual.data {sequence : GenomeSequence}
    (residual : GenomeChemicalResidual sequence) : GenomeChemicalResidualData :=
  { topology := residual.topology
    siteChemistry := residual.siteChemistry
    strandBreakAfter := residual.strandBreakAfter
    supercoiled := residual.supercoiled }

structure ChemicalGenomeState where
  sequence : GenomeSequence
  residual : GenomeChemicalResidualData
  siteChemistryLength : residual.siteChemistry.length = sequence.length
  strandBreakLength : residual.strandBreakAfter.length = sequence.length

def ChemicalGenomeState.dependentView (state : ChemicalGenomeState) :
    (sequence : GenomeSequence) ×' GenomeChemicalResidual sequence :=
  ⟨state.sequence,
    { topology := state.residual.topology
      siteChemistry := state.residual.siteChemistry
      siteChemistryLength := state.siteChemistryLength
      strandBreakAfter := state.residual.strandBreakAfter
      strandBreakLength := state.strandBreakLength
      supercoiled := state.residual.supercoiled }⟩

def ChemicalGenomeState.ofDependent
    (state : (sequence : GenomeSequence) ×'
      GenomeChemicalResidual sequence) : ChemicalGenomeState :=
  { sequence := state.1
    residual := state.2.data
    siteChemistryLength := state.2.siteChemistryLength
    strandBreakLength := state.2.strandBreakLength }

structure DirectedPhosphodiesterBond where
  fromResidue : Nat
  toResidue : Nat
  deriving DecidableEq, Repr

def adjacentBackboneBonds : Nat → List DirectedPhosphodiesterBond
  | 0 => []
  | length + 1 =>
      (List.range length).map fun index =>
        { fromResidue := index, toResidue := index + 1 }

def directedBackboneIncidence
    (topology : StrandTopology) (length : Nat) :
    List DirectedPhosphodiesterBond :=
  match topology, length with
  | _, 0 => []
  | .linear, length + 1 => adjacentBackboneBonds (length + 1)
  | .circular, length + 1 =>
      adjacentBackboneBonds (length + 1) ++
        [{ fromResidue := length, toResidue := 0 }]

/-- The exact carrier retains addressed base signatures and directed backbone
incidence.  It is deliberately stronger than a multiset of atoms or bonds. -/
structure OrientedDNAChemicalBondCarrier where
  orderedBaseBondSignatures : List CanonicalBaseBondSignature
  sugarStereochemistryByResidue : List SugarStereochemistry
  directedBackbone : List DirectedPhosphodiesterBond
  fivePrimeToThreePrimeOrientation : Bool
  endAnchors : PolymerEndAnchors
  residual : GenomeChemicalResidualData
  deriving DecidableEq, Repr

def chemicalBondCarrier (state : ChemicalGenomeState) :
    OrientedDNAChemicalBondCarrier :=
  { orderedBaseBondSignatures := state.sequence.map baseBondSignature
    sugarStereochemistryByResidue :=
      List.replicate state.sequence.length .betaDDeoxyribofuranose
    directedBackbone :=
      directedBackboneIncidence state.residual.topology state.sequence.length
    fivePrimeToThreePrimeOrientation := true
    endAnchors :=
      canonicalDNAEndAnchors state.residual.topology state.sequence.length
    residual := state.residual }

def decodeChemicalBondCarrierSequence
    (carrier : OrientedDNAChemicalBondCarrier) : Option GenomeSequence :=
  decodeOrderedBaseBondSignatures carrier.orderedBaseBondSignatures

/-- A carrier is admitted only after the sequence is computed from its ordered
bond signatures and all topology/residual lengths commute.  The sequence field
is a uniquely checked decoder output, not a caller-selected genome label. -/
structure CanonicalDNAChemicalBondOccurrence where
  carrier : OrientedDNAChemicalBondCarrier
  decodedSequence : GenomeSequence
  sequenceReadExact :
    decodeChemicalBondCarrierSequence carrier = some decodedSequence
  sugarStereochemistryExact :
    carrier.sugarStereochemistryByResidue =
      List.replicate decodedSequence.length .betaDDeoxyribofuranose
  orientationExact : carrier.fivePrimeToThreePrimeOrientation = true
  backboneExact : carrier.directedBackbone =
    directedBackboneIncidence carrier.residual.topology decodedSequence.length
  endAnchorsExact : carrier.endAnchors =
    canonicalDNAEndAnchors carrier.residual.topology decodedSequence.length
  siteChemistryLength :
    carrier.residual.siteChemistry.length = decodedSequence.length
  strandBreakLength :
    carrier.residual.strandBreakAfter.length = decodedSequence.length

def CanonicalDNAChemicalBondOccurrence.toState
    (occurrence : CanonicalDNAChemicalBondOccurrence) : ChemicalGenomeState :=
  { sequence := occurrence.decodedSequence
    residual := occurrence.carrier.residual
    siteChemistryLength := occurrence.siteChemistryLength
    strandBreakLength := occurrence.strandBreakLength }

inductive ChemicalGenomeConsumer where
  | sequence
  | topology
  | siteChemistry
  | strandBreaks
  | supercoiling
  deriving DecidableEq, Repr

def ChemicalGenomeOutput : ChemicalGenomeConsumer → Type
  | .sequence => GenomeSequence
  | .topology => StrandTopology
  | .siteChemistry => List SiteChemicalState
  | .strandBreaks => List Bool
  | .supercoiling => Bool

def chemicalGenomeRead
    (consumer : ChemicalGenomeConsumer) (state : ChemicalGenomeState) :
    ChemicalGenomeOutput consumer :=
  match consumer with
  | .sequence => state.sequence
  | .topology => state.residual.topology
  | .siteChemistry => state.residual.siteChemistry
  | .strandBreaks => state.residual.strandBreakAfter
  | .supercoiling => state.residual.supercoiled

def chemicalGenomeConsumers : IndependentConsumerSystem ChemicalGenomeState where
  Consumer := ChemicalGenomeConsumer
  Output := ChemicalGenomeOutput
  read := chemicalGenomeRead
  positive := ⟨.sequence⟩

structure UnaddressedChemicalBondInventory where
  carbonAtoms : Nat
  nitrogenAtoms : Nat
  oxygenAtoms : Nat
  carbonylDoubleBonds : Nat
  exocyclicAmineSingleBonds : Nat
  methylSubstituentSingleBonds : Nat
  phosphodiesterBonds : Nat
  deriving DecidableEq, Repr

def sumSignatureField
    (field : CanonicalBaseBondSignature → Nat)
    (signatures : List CanonicalBaseBondSignature) : Nat :=
  signatures.foldl (fun total signature => total + field signature) 0

/-- This inventory forgets the address and direction of every local bond
signature.  It is the precise thin carrier rejected by the hostile theorem. -/
def unaddressedChemicalBondInventory (state : ChemicalGenomeState) :
    UnaddressedChemicalBondInventory :=
  let carrier := chemicalBondCarrier state
  { carbonAtoms :=
      sumSignatureField CanonicalBaseBondSignature.carbonAtoms
        carrier.orderedBaseBondSignatures
    nitrogenAtoms :=
      sumSignatureField CanonicalBaseBondSignature.nitrogenAtoms
        carrier.orderedBaseBondSignatures
    oxygenAtoms :=
      sumSignatureField CanonicalBaseBondSignature.oxygenAtoms
        carrier.orderedBaseBondSignatures
    carbonylDoubleBonds :=
      sumSignatureField CanonicalBaseBondSignature.carbonylDoubleBonds
        carrier.orderedBaseBondSignatures
    exocyclicAmineSingleBonds :=
      sumSignatureField CanonicalBaseBondSignature.exocyclicAmineSingleBonds
        carrier.orderedBaseBondSignatures
    methylSubstituentSingleBonds :=
      sumSignatureField CanonicalBaseBondSignature.methylSubstituentSingleBonds
        carrier.orderedBaseBondSignatures
    phosphodiesterBonds := carrier.directedBackbone.length }

def cleanLinearResidual (sequence : GenomeSequence) :
    GenomeChemicalResidual sequence :=
  { topology := .linear
    siteChemistry := List.replicate sequence.length .canonical
    siteChemistryLength := by simp
    strandBreakAfter := List.replicate sequence.length false
    strandBreakLength := by simp
    supercoiled := false }

end ChemicalGenomeInformation.Interface
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
