import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.DNM1Splicing2026.Source.Types

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.DNM1Splicing2026.Sequence

open ChemicalGenomeInformation.Interface

def upperBase : Char → Char
  | 'a' => 'A' | 'c' => 'C' | 'g' => 'G' | 't' => 'T' | c => c

def normalized (text : String) : List Char := text.toList.map upperBase

def base? (c : Char) : Option CanonicalNucleobase :=
  match upperBase c with
  | 'A' => some .adenine | 'C' => some .cytosine | 'G' => some .guanine | 'T' => some .thymine | _ => none

def decode? (text : String) : Option GenomeSequence := text.toList.mapM base?

def render (bases : Bases) : String := String.ofList (bases.map fun base =>
  match base with
  | .adenine => 'A' | .cytosine => 'C' | .guanine => 'G' | .thymine => 'T')

def singleBase? : String → Option CanonicalNucleobase
  | "A" => some .adenine | "C" => some .cytosine | "G" => some .guanine | "T" => some .thymine | _ => none

def edit? (key : VariantKey) (context : SequenceContext) : Option Bases := do
  if key.strand != "+" || key.position = 0 || key.reference.length != 1 ||
      key.alternate.length != 1 || key.reference = key.alternate then none else do
    let offset := key.position - 1 - context.start
    if key.position - 1 < context.start || context.stop ≤ key.position - 1 ||
        context.dna.length != context.stop - context.start then none else do
      let reference ← singleBase? key.reference
      let alternate ← singleBase? key.alternate
      let bases := context.dna
      if bases[offset]? != some reference then none else
        pure (bases.take offset ++ [alternate] ++ bases.drop (offset+1))

def restriction? (context : SequenceContext) (start stop : Nat) : Option Bases :=
  if context.start ≤ start && start ≤ stop && stop ≤ context.stop &&
      context.dna.length = context.stop - context.start then
    some (context.dna.drop (start-context.start) |>.take (stop-start))
  else none

/-- A codon table is source data; no predicted peptide is an argument. -/
def translate? (code : List (Bases × String)) : Bases → Option (List String)
  | [] => some []
  | a :: b :: c :: rest => do
      let pair ← code.find? fun row => row.1 = [a,b,c]
      let tail ← translate? code rest
      pure (pair.2 :: tail)
  | _ => none

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.DNM1Splicing2026.Sequence
