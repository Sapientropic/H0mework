import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LMNACorrection2021.Source.Inputs

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LMNACorrection2021.Genome
open ChemicalGenomeInformation.Interface

def complement : CanonicalNucleobase → CanonicalNucleobase
  | .adenine => .thymine | .thymine => .adenine
  | .cytosine => .guanine | .guanine => .cytosine
def reverseComplement (bases : Bases) : Bases := bases.reverse.map complement
def prefixMatches : Bases → Bases → Bool
  | [],_ => true | _::_,[] => false
  | a::rest,b::tail => a == b && prefixMatches rest tail
private def sitesFrom (part : Bases) : Nat → Bases → List Nat
  | i,[] => if part.isEmpty then [i] else []
  | i,whole@(_::tail) =>
    if prefixMatches part whole then i :: sitesFrom part (i+1) tail else sitesFrom part (i+1) tail
def sites (whole part : Bases) : List Nat := sitesFrom part 0 whole
private def firstFrom (part : Bases) : Nat → Bases → Option Nat
  | i,[] => if part.isEmpty then some i else none
  | i,whole@(_::tail) => if prefixMatches part whole then some i else firstFrom part (i+1) tail
def firstSite (whole part : Bases) : Nat := (firstFrom part 0 whole).getD 0

def targetOffset : Nat := 156138613-1-Source.context.start
def genomic (g : Genotype) : Bases :=
  (Source.context.dna.set targetOffset (if g.targetT then .thymine else .cytosine)).set
    (targetOffset-4) (if g.bystanderC then .cytosine else .thymine)
def coding (g : Genotype) : Bases :=
  (Source.coding.set 1823 (if g.targetT then .thymine else .cytosine)).set
    1819 (if g.bystanderC then .cytosine else .thymine)
def rna (g : Genotype) : Bases :=
  (Source.rna.set (249+1823) (if g.targetT then .thymine else .cytosine)).set
    (249+1819) (if g.bystanderC then .cytosine else .thymine)

def dnaStart : Nat := firstSite Source.context.dna Source.dnaForward
def dnaStop : Nat := firstSite Source.context.dna (reverseComplement Source.dnaReverse) + Source.dnaReverse.length
def dnaWord (g : Genotype) : Bases := (genomic g).drop dnaStart |>.take (dnaStop-dnaStart)
def codingStart : Nat := firstSite Source.coding (dnaWord ⟨false,false⟩)
def guideStart : Nat := firstSite (genomic ⟨true,false⟩) (reverseComplement Source.guide)
def pam : Bases := reverseComplement ((genomic ⟨true,false⟩).drop (guideStart-3) |>.take 3)

/-- The published primary activity window is applied to the original reverse-strand
guide. Observed bystander products remain separate source genotypes. -/
def windowPositions : List Nat := (List.range 4).map (3+·)
def intendedEdits : List (Nat × CanonicalNucleobase) :=
  ((windowPositions.map fun i => guideStart+Source.guide.length-1-i).filter fun i =>
    (genomic ⟨true,false⟩)[i]? == some .thymine).map fun i => (i,.cytosine)
def intendedRepair : Bases :=
  intendedEdits.foldl (fun bases edit => bases.set edit.1 edit.2) (genomic ⟨true,false⟩)

theorem original_source_coordinates :
    Source.context.start = 156138000 ∧ Source.context.stop = 156139500 ∧
    Source.context.dna.length = 1500 ∧ Source.coding.length = 1995 ∧
    (Source.rna.drop 249).take 1995 = Source.coding := by decide +kernel

theorem original_guide_in_full_vector :
    Source.vector.length = 14234 ∧ Source.guide.length = 20 ∧
    (sites Source.vector Source.guide).length = 1 ∧
    sites (genomic ⟨true,false⟩) (reverseComplement Source.guide) = [598] ∧
    pam = [.thymine,.guanine,.adenine] := by decide +kernel

theorem original_genomic_coding_words (target bystander : Bool) :
    dnaStart = 512 ∧ dnaStop = 639 ∧ codingStart = 1723 ∧
    dnaWord ⟨target,bystander⟩ = ((coding ⟨target,bystander⟩).drop codingStart).take 127 ∧
    ((rna ⟨target,bystander⟩).drop 249).take 1995 = coding ⟨target,bystander⟩ := by
  cases target <;> cases bystander <;> decide +kernel

theorem source_window_generates_actual_target :
    intendedEdits = [(targetOffset,.cytosine)] ∧
    (genomic ⟨true,false⟩)[targetOffset]? = some .thymine ∧
    intendedRepair = Source.context.dna ∧
    intendedRepair = genomic ⟨false,false⟩ := by decide +kernel

theorem bystander_is_retained :
    genomic ⟨false,true⟩ ≠ intendedRepair ∧
    ((coding ⟨false,true⟩).drop 1818).take 3 = [.guanine,.cytosine,.guanine] := by decide +kernel

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LMNACorrection2021.Genome
