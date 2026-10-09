import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AddressedChemicalReaction.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AtomicSource.Graph

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace CPS1AddressedHydrolysis
open CPS1LocalChemicalExecution CPS1AtomicSource CPS1ResourceExecution

structure Water where
  batch : Nat
  ordinal : Nat
  deriving DecidableEq

/-- The two hydrogens have distinct source slots within this raw water packet.
This chemical rule supplies no pose, reaction endpoint, or product atom map. -/
inductive WaterAtom | aminoH | hydroxylH | oxygen deriving DecidableEq

def WaterAtom.element : WaterAtom → PeptideMaterial.Element
  | .aminoH | .hydroxylH => .H
  | .oxygen => .O

def WaterAtom.charge (_ : WaterAtom) : Int := 0

def Water.material (frame : CPS1Recycling.Frame) (water : Water) :
    CPS1AddressedChemicalReaction.Source.LocalMaterial frame :=
  .raw water.batch water.ordinal (molecule frame .water)

def waterSource? {frame : CPS1Recycling.Frame}
    (material : CPS1AddressedChemicalReaction.Source.LocalMaterial frame) : Option Water :=
  match material with
  | .raw batch ordinal species => if species = molecule frame .water then some ⟨batch,ordinal⟩ else none
  | _ => none

theorem water_source_exact {frame : CPS1Recycling.Frame}
    (material : CPS1AddressedChemicalReaction.Source.LocalMaterial frame) (water : Water)
    (actual : waterSource? material = some water) : material = water.material frame := by
  cases material with
  | inherited => cases actual
  | product => cases actual
  | raw batch ordinal species =>
    by_cases matched : species = molecule frame .water
    · simp only [waterSource?,if_pos matched,Option.some.injEq] at actual
      subst water
      simp only [Water.material,matched]
    · simp only [waterSource?,if_neg matched] at actual
      cases actual

theorem raw_water_source (frame : CPS1Recycling.Frame) (water : Water) :
    waterSource? (water.material frame) = some water := by
  simp only [Water.material,waterSource?,if_true]

def waterAtoms : List WaterAtom := [.aminoH,.hydroxylH,.oxygen]
def waterBonds : List (WaterAtom × WaterAtom) := [(.oxygen,.aminoH),(.oxygen,.hydroxylH)]

theorem water_rule (element : PeptideMaterial.Element) :
    (waterAtoms.filter (fun atom => atom.element = element)).length =
      PeptideMaterial.moleculeAtoms Chemistry.Molecule.water element ∧
    (waterAtoms.map WaterAtom.charge).sum = Chemistry.Molecule.water.charge ∧
    waterAtoms.Nodup ∧ (∀ atom ∈ waterAtoms, ∃ left right,
      (left,right) ∈ waterBonds ∧ (atom = left ∨ atom = right)) := by
  refine ⟨?_,rfl,by decide +kernel,?_⟩
  · cases element <;> rfl
  · intro atom _
    cases atom with
    | aminoH => exact ⟨.oxygen,.aminoH,by decide +kernel,Or.inr rfl⟩
    | hydroxylH => exact ⟨.oxygen,.hydroxylH,by decide +kernel,Or.inr rfl⟩
    | oxygen => exact ⟨.oxygen,.aminoH,by decide +kernel,Or.inl rfl⟩

def terminalAtoms (aa : AA) (leave : Primary.TerminalLeave) : List Primary.Atom :=
  (Primary.template aa).atoms.filter (fun atom => atom.terminalLeave = leave)

def terminalWaterAtom (leave : Primary.TerminalLeave) (atom : Primary.Atom) : WaterAtom :=
  if leave = .amino then .aminoH else if atom.element = .O then .oxygen else .hydroxylH

theorem terminal_water_slots (aa : AA) :
    (terminalAtoms aa .amino).map (terminalWaterAtom .amino) = [.aminoH] ∧
    (terminalAtoms aa .carboxyl).map (terminalWaterAtom .carboxyl) = [.oxygen,.hydroxylH] := by
  cases aa <;> decide +kernel

theorem terminal_water_payload (aa : AA) (leave : Primary.TerminalLeave)
    (terminal : leave = .amino ∨ leave = .carboxyl) :
    ∀ atom ∈ terminalAtoms aa leave,
      (terminalWaterAtom leave atom).element = atom.element ∧
        (terminalWaterAtom leave atom).charge = atom.charge := by
  rcases terminal with rfl | rfl <;> cases aa <;> decide +kernel

theorem terminal_source (aa : AA) (leave : Primary.TerminalLeave)
    (atom : Primary.Atom) (member : atom ∈ terminalAtoms aa leave) :
    atom ∈ (Primary.template aa).atoms ∧ atom.terminalLeave = leave := by
  exact ⟨(List.mem_filter.mp member).1,of_decide_eq_true (List.mem_filter.mp member).2⟩

end CPS1AddressedHydrolysis
