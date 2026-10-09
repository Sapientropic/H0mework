import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Kernel.Rna
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LMNACorrection2021.Producer.Genome

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Coding
abbrev code := LMNACorrection2021.Source.code
abbrev reverseComplement := LMNACorrection2021.Genome.reverseComplement
abbrev sites := LMNACorrection2021.Genome.sites
abbrev translate := DNM1Splicing2026.Sequence.translate?
def isStop (codon : Bases) : Bool :=
  codon == [.thymine,.adenine,.adenine] || codon == [.thymine,.adenine,.guanine] ||
  codon == [.thymine,.guanine,.adenine]
def startFrom : Nat → Bases → Option Nat
  | i,a :: b :: c :: rest =>
    if [a,b,c] == [.adenine,.thymine,.guanine] then some i
    else startFrom (i+1) (b :: c :: rest)
  | _,_ => none
def stopFrom : Nat → Bases → Option Nat
  | i,a :: b :: c :: rest => if isStop [a,b,c] then some i else stopFrom (i+1) rest
  | _,_ => none
def firstStart (dna : Bases) : Option Nat := startFrom 0 dna
def firstFrameStop (dna : Bases) : Option Nat := stopFrom 0 dna
def coding? (dna : Bases) : Option Bases := do
  let start ← firstStart dna
  let tail := dna.drop start
  let last ← firstFrameStop tail
  pure (tail.take ((last+1)*3))
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Coding
