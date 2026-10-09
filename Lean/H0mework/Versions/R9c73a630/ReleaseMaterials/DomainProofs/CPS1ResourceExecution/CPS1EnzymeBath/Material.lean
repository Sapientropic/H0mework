import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1EnzymeBath.Joint
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1EnzymeBath.PrimaryFacts

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace CPS1EnzymeBath.Joint
noncomputable section
open CPS1AtomicDynamics CPS1AtomicSource CPS1LocalChemicalExecution

def elementCount (atoms : List Atom) (element : Primary.Element) : Nat :=
  (atoms.map (fun atom => if atom.descriptor.source.element = element then 1 else 0)).sum

def charge (frame : CPS1Recycling.Frame) (state : State frame) : Int :=
  ((atoms frame state).map (fun atom => atom.descriptor.source.charge)).sum

private theorem count_as_sum (atoms : List Primary.Atom) (element : Primary.Element) :
    (atoms.map (fun atom => if atom.element = element then 1 else 0)).sum =
      Primary.atomCount atoms element := by
  induction atoms with
  | nil => rfl
  | cons head rest ih =>
    by_cases same : head.element = element <;>
      simp [Primary.atomCount,same,ih,Nat.add_comm]

private theorem sum_flatMap {A B : Type} [AddCommMonoid B] (rows : List A) (f : A → List B) :
    (rows.flatMap f).sum = (rows.map (fun row => (f row).sum)).sum := by
  induction rows with
  | nil => rfl
  | cons row rest ih => simp only [List.flatMap_cons,List.sum_append,List.map_cons,List.sum_cons,ih]

theorem bath_material (component : Component) (element : Primary.Element) :
    elementCount ((Primary.template component.kind).atoms.map (bathAtom component)) element =
      PeptideMaterial.moleculeAtoms component.kind.molecule element := by
  unfold elementCount
  rw [List.map_map]
  change ((Primary.template component.kind).atoms.map
    (fun atom => if atom.element = element then 1 else 0)).sum = _
  rw [count_as_sum,Primary.original_formula]

theorem whole_material (frame : CPS1Recycling.Frame) (state : State frame) (element : Primary.Element) :
    elementCount (atoms frame state) element = Graph.atoms (Body.graph frame state.originBody) element +
      (state.components.map (fun component => PeptideMaterial.moleculeAtoms component.kind.molecule element)).sum := by
  unfold atoms elementCount
  rw [List.map_append,List.sum_append,List.map_flatMap,sum_flatMap]
  congr 1
  · simp only [List.map_map,Function.comp_def,Graph.atoms]
  · apply congrArg List.sum
    apply List.map_congr_left
    intro component _
    exact bath_material component element

theorem bath_charge (component : Component) :
    (((Primary.template component.kind).atoms.map (bathAtom component)).map
      (fun atom => atom.descriptor.source.charge)).sum = component.kind.molecule.charge := by
  simp only [List.map_map,Function.comp_def,bathAtom]
  exact Primary.original_charge component.kind

theorem whole_charge (frame : CPS1Recycling.Frame) (state : State frame) :
    charge frame state = Graph.charge (Body.graph frame state.originBody) +
      (state.components.map (fun component => component.kind.molecule.charge)).sum := by
  unfold charge atoms
  rw [List.map_append,List.sum_append,List.map_flatMap,sum_flatMap]
  congr 1
  · simp only [List.map_map,Function.comp_def,Graph.charge]
  · apply congrArg List.sum
    apply List.map_congr_left
    intro component _
    exact bath_charge component

theorem descriptor_atom_valid (frame : CPS1Recycling.Frame) (state : State frame)
    (atom : Graph.Atom) (member : atom ∈ (descriptorGraph frame state).atoms) :
    atom.source.charge ≤ (Charged.atomicNumber atom.source.element : Int) := by
  rcases List.mem_map.mp member with ⟨original,present,same⟩
  subst atom
  rcases List.mem_append.mp present with enzyme | bath
  · rcases List.mem_map.mp enzyme with ⟨source,sourceMember,same⟩
    subst original
    exact Charged.graph_atom_valid (Actual.cps1 frame).word state.originBody.source.bonds source sourceMember
  · rcases List.mem_flatMap.mp bath with ⟨component,_,member⟩
    rcases List.mem_map.mp member with ⟨source,sourceMember,same⟩
    subst original
    exact Primary.original_electron_count component.kind source sourceMember

theorem particle_charge (frame : CPS1Recycling.Frame) (state : State frame) :
    Charged.charge (particles frame state) = charge frame state := by
  simpa only [particles,Graph.charge,descriptorGraph,charge,List.map_map,Function.comp_def] using
    Charged.particles_charge (descriptorGraph frame state) (descriptor_atom_valid frame state)

theorem particle_unique (frame : CPS1Recycling.Frame) (state : State frame) :
    ((particles frame state).map Charged.Particle.address).Nodup :=
  Charged.particles_unique (descriptorGraph frame state)

end
end CPS1EnzymeBath.Joint
