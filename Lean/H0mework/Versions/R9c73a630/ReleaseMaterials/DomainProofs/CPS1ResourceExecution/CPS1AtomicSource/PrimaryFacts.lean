import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AtomicSource.Primary

set_option autoImplicit false
set_option maxHeartbeats 0
namespace CPS1AtomicSource.Primary
open CPS1ResourceExecution CPS1LocalChemicalExecution
open PeptideMaterial

def atomCount (atoms : List Atom) (element : Element) : Nat :=
  (atoms.map (fun atom => if atom.element = element then 1 else 0)).sum

def templateCharge (aa : AA) : Int := ((template aa).atoms.map Atom.charge).sum

def additionalProtons (aa : AA) : Nat := (templateCharge aa).toNat

theorem original_formula (aa : AA) (element : Element) :
    atomCount (template aa).atoms element = freeAtoms aa element +
      if element = .H then additionalProtons aa else 0 := by
  cases aa <;> cases element <;> decide +kernel

theorem original_charge (aa : AA) : templateCharge aa = (additionalProtons aa : Int) := by
  cases aa <;> rfl

theorem original_names_unique (aa : AA) : ((template aa).atoms.map Atom.name).Nodup := by
  cases aa <;> decide +kernel

theorem original_backbone (aa : AA) :
    ((template aa).atoms.any (fun atom => atom.name = "C" && atom.terminalLeave = .none)) = true ∧
    ((template aa).atoms.any (fun atom => atom.name = "N" && atom.terminalLeave = .none)) = true := by
  cases aa <;> exact ⟨rfl,rfl⟩

theorem original_ends (aa : AA) (element : Element) :
    atomCount ((template aa).atoms.filter (fun atom => atom.terminalLeave = .amino)) element =
      (if element = .H then 1 else 0) ∧
    atomCount ((template aa).atoms.filter (fun atom => atom.terminalLeave = .carboxyl)) element =
      (if element = .H ∨ element = .O then 1 else 0) := by
  cases aa <;> cases element <;> exact ⟨rfl,rfl⟩

theorem original_end_charge (aa : AA) :
    (((template aa).atoms.filter (fun atom => atom.terminalLeave = .amino)).map Atom.charge).sum = 0 ∧
    (((template aa).atoms.filter (fun atom => atom.terminalLeave = .carboxyl)).map Atom.charge).sum = 0 := by
  cases aa <;> exact ⟨rfl,rfl⟩

theorem source_proline_amino_name :
    ((template .P).atoms.filter (fun atom => atom.terminalLeave = .amino)).map Atom.name = ["H"] ∧
    ((template .A).atoms.filter (fun atom => atom.terminalLeave = .amino)).map Atom.name = ["H2"] := ⟨rfl,rfl⟩

theorem original_bond_endpoints (aa : AA) :
    (template aa).bonds.all (fun bond =>
      ((template aa).atoms.any (fun atom => atom.name = bond.left)) &&
      ((template aa).atoms.any (fun atom => atom.name = bond.right))) = true := by
  cases aa <;> decide +kernel

theorem original_charge_location (aa : AA) :
    (template aa).atoms.all (fun atom =>
      atom.charge == 0 || (atom.charge == 1 && atom.terminalLeave == .none)) = true := by
  cases aa <;> decide +kernel

end CPS1AtomicSource.Primary
