import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.DNM1Splicing2026.Kernel.Sequence

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025
abbrev Bases := DNM1Splicing2026.Bases

inductive Nucleoside | adenosine | cytidine | guanosine | uridine | n1Methylpseudouridine
  deriving DecidableEq, Repr, Inhabited
structure Residue where
  nucleoside : Nucleoside
  ribose2OMethyl : Bool
  deriving DecidableEq, Repr, Inhabited
structure RegisteredRna where
  residues : List Residue
  sulfurAfter : List Nat
  deriving DecidableEq, Repr, Inhabited

namespace Rna
def residue? : Char → Option Residue
  | 'A' => some ⟨.adenosine,false⟩ | 'a' => some ⟨.adenosine,true⟩
  | 'C' => some ⟨.cytidine,false⟩ | 'c' => some ⟨.cytidine,true⟩
  | 'G' => some ⟨.guanosine,false⟩ | 'g' => some ⟨.guanosine,true⟩
  | 'U' => some ⟨.uridine,false⟩ | 'u' => some ⟨.uridine,true⟩
  | 'Ψ' => some ⟨.n1Methylpseudouridine,false⟩
  | _ => none

/-- The source `s` is a linkage after a nucleotide, never another nucleotide. -/
def parseAux (count : Nat) (residues : List Residue) (links : List Nat)
    (pendingLink : Bool) : List Char → Option RegisteredRna
  | [] => if pendingLink then none else some ⟨residues.reverse,links.reverse⟩
  | 's' :: rest =>
    if count == 0 || pendingLink then none
    else parseAux count residues (count :: links) true rest
  | c :: rest => do
    let residue ← residue? c
    parseAux (count+1) (residue :: residues) links false rest
def parse (text : List Char) : Option RegisteredRna := parseAux 0 [] [] false text

/-- A coding-template projection; modified RNA chemistry remains in RegisteredRna. -/
def templateBase (residue : Residue) : ChemicalGenomeInformation.Interface.CanonicalNucleobase :=
  match residue.nucleoside with
  | .adenosine => .adenine | .cytidine => .cytosine | .guanosine => .guanine
  | .uridine | .n1Methylpseudouridine => .thymine
def template (rna : RegisteredRna) : Bases := rna.residues.map templateBase
def eraseModifications (rna : RegisteredRna) : RegisteredRna :=
  ⟨rna.residues.map (fun r => ⟨if r.nucleoside == .n1Methylpseudouridine then .uridine else r.nucleoside,false⟩),[]⟩
def methylCount (rna : RegisteredRna) : Nat := (rna.residues.filter Residue.ribose2OMethyl).length
def pseudoCount (rna : RegisteredRna) : Nat :=
  (rna.residues.filter (fun r => r.nucleoside == .n1Methylpseudouridine)).length

theorem template_forgets_modifications (rna : RegisteredRna) :
    template (eraseModifications rna) = template rna := by
  unfold template eraseModifications
  simp only [List.map_map]
  apply List.map_congr_left
  intro residue _
  rcases residue with ⟨kind,modified⟩
  cases kind <;> rfl

end Rna
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025
