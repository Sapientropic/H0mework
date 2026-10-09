import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1LocalChemicalExecution.Actual
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1LocalChemicalExecution.Chemistry

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CPS1LocalChemicalExecution.PeptideMaterial
open CPS1ResourceExecution

inductive Element | C | H | N | O | P | K | Mg | S deriving DecidableEq,Repr

def Element.ofMolecule : Chemistry.Atom → Element
  | .C => .C | .H => .H | .N => .N | .O => .O | .P => .P | .K => .K | .Mg => .Mg

def formula (c h n o s : Nat) : Element → Nat
  | .C => c | .H => h | .N => n | .O => o | .S => s | .P | .K | .Mg => 0

/-- Fixed neutral free-AA formulas from the PubChem CID table. Bath protonation,
crosslinks and side-chain modifications remain independent chemical material. -/
def freeAtoms : AA → Element → Nat
  | .A => formula 3 7 1 2 0
  | .C => formula 3 7 1 2 1
  | .D => formula 4 7 1 4 0
  | .E => formula 5 9 1 4 0
  | .F => formula 9 11 1 2 0
  | .G => formula 2 5 1 2 0
  | .H => formula 6 9 3 2 0
  | .I | .L => formula 6 13 1 2 0
  | .K => formula 6 14 2 2 0
  | .M => formula 5 11 1 2 1
  | .N => formula 4 8 2 3 0
  | .P => formula 5 9 1 2 0
  | .Q => formula 5 10 2 3 0
  | .R => formula 6 14 4 2 0
  | .S => formula 3 7 1 3 0
  | .T => formula 4 9 1 3 0
  | .V => formula 5 11 1 2 0
  | .W => formula 11 12 2 2 0
  | .Y => formula 9 11 1 3 0

def waterAtoms : Element → Nat | .H => 2 | .O => 1 | _ => 0
def bondCount (word : List AA) : Nat := word.length - 1
def freeWordAtoms (word : List AA) (element : Element) : Int :=
  ((word.map (fun aa => freeAtoms aa element)).sum : Nat)

/-- Signed accounting prevents Nat subtraction from silently truncating. Each
source peptide bond removes one water; each actual hydrolysis returns that water
to the two new termini. Valid cuts are supplied by the consuming bond trace. -/
def wordAtoms (word : List AA) (hydrolysed : Nat) (element : Element) : Int :=
  freeWordAtoms word element - (bondCount word : Int) * (waterAtoms element : Int) +
    (hydrolysed : Int) * (waterAtoms element : Int)

def moleculeAtoms (molecule : Chemistry.Molecule) : Element → Nat
  | .C => molecule.atoms .C | .H => molecule.atoms .H | .N => molecule.atoms .N
  | .O => molecule.atoms .O | .P => molecule.atoms .P | .K => molecule.atoms .K
  | .Mg => molecule.atoms .Mg | .S => 0

theorem water_is_same_material (element : Element) :
    moleculeAtoms .water element = waterAtoms element := by cases element <;> rfl

theorem molecular_restriction (molecule : Chemistry.Molecule) (atom : Chemistry.Atom) :
    moleculeAtoms molecule (Element.ofMolecule atom) = molecule.atoms atom := by cases atom <;> rfl

theorem hydrolysis_atoms (word : List AA) (cuts : Nat) (element : Element) :
    wordAtoms word cuts element + (waterAtoms element : Int) = wordAtoms word (cuts+1) element := by
  simp only [wordAtoms,Nat.cast_add,Nat.cast_one]
  ring

theorem complete_hydrolysis (word : List AA) (element : Element) :
    wordAtoms word (bondCount word) element = freeWordAtoms word element := by
  simp only [wordAtoms]
  ring

theorem empty_material (element : Element) : wordAtoms [] 0 element = 0 := by
  simp [wordAtoms,freeWordAtoms,bondCount]

theorem singleton_material (aa : AA) (element : Element) :
    wordAtoms [aa] 0 element = (freeAtoms aa element : Int) := by
  simp [wordAtoms,freeWordAtoms,bondCount]

theorem free_word_add (left right : List AA) (element : Element) :
    freeWordAtoms (left ++ right) element = freeWordAtoms left element + freeWordAtoms right element := by
  simp [freeWordAtoms,List.map_append,List.sum_append]

theorem cleavage_fragments (left right : List AA) (leftPresent : left ≠ []) (rightPresent : right ≠ [])
    (element : Element) :
    wordAtoms (left ++ right) 0 element + (waterAtoms element : Int) =
      wordAtoms left 0 element + wordAtoms right 0 element := by
  have ll : 0 < left.length := by
    cases left with
    | nil => exact False.elim (leftPresent rfl)
    | cons aa rest => exact Nat.zero_lt_succ _
  have rr : 0 < right.length := by
    cases right with
    | nil => exact False.elim (rightPresent rfl)
    | cons aa rest => exact Nat.zero_lt_succ _
  have bonds : bondCount (left ++ right) = bondCount left + bondCount right + 1 := by
    simp only [bondCount,List.length_append]
    omega
  simp only [wordAtoms,free_word_add,bonds,Nat.cast_add,Nat.cast_one,Nat.cast_zero,zero_mul,add_zero]
  ring

theorem source_cleavage_water (frame : CPS1Recycling.Frame) (cuts : Nat) (element : Element) :
    wordAtoms (Actual.cps1 frame).word cuts element + (waterAtoms element : Int) =
      wordAtoms (Actual.cps1 frame).word (cuts+1) element := hydrolysis_atoms _ _ _

end CPS1LocalChemicalExecution.PeptideMaterial
