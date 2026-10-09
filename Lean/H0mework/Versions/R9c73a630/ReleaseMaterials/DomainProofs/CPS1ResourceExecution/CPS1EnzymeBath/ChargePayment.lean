import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1EnzymeBath.Consumers

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace CPS1EnzymeBath
noncomputable section
open CPS1ResourceExecution CPS1AtomicDynamics CPS1LocalChemicalExecution

theorem attach_material_paid (frame : CPS1Recycling.Frame) (state : Joint.State frame)
    (kind : Primary.TemplateKind) (element : Primary.Element) :
    Joint.elementCount (Joint.atoms frame (Joint.attach frame state kind)) element =
      Joint.elementCount (Joint.atoms frame state) element +
        PeptideMaterial.moleculeAtoms kind.molecule element := by
  rw [Joint.append_atoms]
  simp only [Joint.elementCount,List.map_append,List.sum_append]
  rw [show ((Primary.template kind).atoms.map (Joint.bathAtom ⟨state.nextOccurrence,kind⟩) |>.map
    (fun atom => if atom.descriptor.source.element = element then 1 else 0)).sum =
      PeptideMaterial.moleculeAtoms kind.molecule element from Joint.bath_material _ element]

theorem attach_charge_paid (frame : CPS1Recycling.Frame) (state : Joint.State frame)
    (kind : Primary.TemplateKind) :
    Joint.charge frame (Joint.attach frame state kind) = Joint.charge frame state+kind.molecule.charge := by
  simp only [Joint.charge,Joint.append_atoms,List.map_append,List.sum_append]
  rw [Joint.bath_charge]

theorem source_component_paid (frame : CPS1Recycling.Frame) (state : Joint.State frame)
    (kind : Primary.TemplateKind) (stock surplus : CPS1EnzymeBath.Stock frame)
    (inventory : stock.Perm ([Species.joint state,componentSpecies frame kind] ++ surplus)) :
    let result := CPS1EnzymeBath.execute frame [.attach state kind] stock
    result.stock.Perm (.joint (Joint.attach frame state kind) :: surplus) ∧
      (∀ element, Joint.elementCount (Joint.atoms frame (Joint.attach frame state kind)) element =
        Joint.elementCount (Joint.atoms frame state) element+PeptideMaterial.moleculeAtoms kind.molecule element) ∧
      Joint.charge frame (Joint.attach frame state kind) = Joint.charge frame state+kind.molecule.charge ∧
      Joint.dangling frame (Joint.attach frame state kind) = [] ∧
      (∀ particle ∈ Joint.particles frame state,
        particle ∈ Joint.particles frame (Joint.attach frame state kind)) := by
  have actual := attach_existing frame state kind stock surplus inventory
  exact ⟨actual.2.2.2,attach_material_paid frame state kind,attach_charge_paid frame state kind,
    Joint.no_dangling frame _,Joint.old_particle_retained frame state kind⟩

end
end CPS1EnzymeBath
