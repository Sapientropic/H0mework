import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.ChemicalGenomeInformation.Interface.OrientedChemicalGenomeCarrier
import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace CPS1Deamination

open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.ChemicalGenomeInformation.Interface

inductive Base | A | C | G | T | I deriving DecidableEq, Repr
inductive Atom | C | H | N | O | P deriving DecidableEq, Repr

namespace Base
def ofCanonical : CanonicalNucleobase → Base
  | .adenine => .A | .cytosine => .C | .guanine => .G | .thymine => .T

def ofOpposite : CanonicalNucleobase → Base
  | .adenine => .T | .cytosine => .G | .guanine => .C | .thymine => .A

/-- Inosine recognition changes a sequence readout, not the chemical carrier. -/
def recognize : Base → CanonicalNucleobase
  | .A => .adenine | .C => .cytosine | .G => .guanine | .T => .thymine | .I => .guanine

def oppositeRead : Base → CanonicalNucleobase
  | .A => .thymine | .C => .guanine | .G => .cytosine | .T => .adenine | .I => .cytosine

def signature : Base → CanonicalBaseBondSignature
  | .A => baseBondSignature .adenine
  | .C => baseBondSignature .cytosine
  | .G => baseBondSignature .guanine
  | .T => baseBondSignature .thymine
  | .I =>
    { carbonAtoms := 5
      nitrogenAtoms := 4
      oxygenAtoms := 1
      ringTopology := .fusedPurine
      carbonylDoubleBonds := 1
      exocyclicAmineSingleBonds := 0
      methylSubstituentSingleBonds := 0
      ringNitrogenSites := [1,3,7,9]
      carbonylSites := [6]
      exocyclicAmineSites := []
      methylSites := []
      glycosidicNitrogenSite := 9 }

/-- Neutral glycosidically attached base moieties. Sugar/phosphate and end
chemistry are a separate unchanged scaffold, not inferred from a sequence. -/
def atoms (base : Base) : Atom → Nat
  | .C => base.signature.carbonAtoms
  | .N => base.signature.nitrogenAtoms
  | .O => base.signature.oxygenAtoms
  | .P => 0
  | .H => match base with
    | .A | .C | .G => 4 | .T => 5 | .I => 3

theorem opposite_roundtrip (base : CanonicalNucleobase) :
    (ofOpposite base).oppositeRead = base := by cases base <;> rfl

theorem inosine_is_not_guanine :
    Base.I.recognize = .guanine ∧ Base.I ≠ Base.G ∧
    Base.I.signature ≠ Base.G.signature ∧
    decodeBaseBondSignature Base.I.signature = none := by decide +kernel

theorem deamination_preserves_ring_and_attachment :
    Base.I.signature.ringTopology = Base.A.signature.ringTopology ∧
    Base.I.signature.ringNitrogenSites = Base.A.signature.ringNitrogenSites ∧
    Base.I.signature.glycosidicNitrogenSite = Base.A.signature.glycosidicNitrogenSite ∧
    Base.A.signature.exocyclicAmineSites = [6] ∧
    Base.I.signature.exocyclicAmineSites = [] ∧
    Base.I.signature.carbonylSites = [6] := by decide +kernel
end Base

def waterAtoms : Atom → Nat | .H => 2 | .O => 1 | _ => 0
def ammoniaAtoms : Atom → Nat | .H => 3 | .N => 1 | _ => 0
def wordAtoms (word : List Base) (atom : Atom) : Nat := (word.map (fun b => b.atoms atom)).sum

theorem deamination_atom_balance (left right : List Base) (atom : Atom) :
    wordAtoms (left ++ Base.A :: right) atom + waterAtoms atom =
      wordAtoms (left ++ Base.I :: right) atom + ammoniaAtoms atom := by
  cases atom <;> simp [wordAtoms, Base.atoms, Base.signature, baseBondSignature,
    waterAtoms, ammoniaAtoms] <;> omega

theorem scaffold_preserved (scaffold : Atom → Nat) (left right : List Base) (atom : Atom) :
    scaffold atom + wordAtoms (left ++ Base.A :: right) atom + waterAtoms atom =
      scaffold atom + wordAtoms (left ++ Base.I :: right) atom + ammoniaAtoms atom := by
  have balance := deamination_atom_balance left right atom
  omega

end CPS1Deamination
