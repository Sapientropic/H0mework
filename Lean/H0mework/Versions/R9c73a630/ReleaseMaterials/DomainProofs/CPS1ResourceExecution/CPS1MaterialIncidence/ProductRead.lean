import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.OriginGraph
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1PhosphorylExchange.Base

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1MaterialIncidence
noncomputable section
open CPS1AtomicSource CPS1AtomicDynamics CPS1SameEventFunction CPS1PhosphorylExchange
open scoped BigOperators
variable {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}

def adjacent {atoms : List (Atom cursor)} (graph : OriginGraph atoms)
    (first second : AtomOrigin cursor) : Bool :=
  graph.incidence.support.toList.any (fun bond => decide (0 < graph.incidence bond) &&
    ((bond.left == first && bond.right == second) || (bond.left == second && bond.right == first)))

def growComponent {atoms : List (Atom cursor)} (graph : OriginGraph atoms)
    (reached : List (AtomOrigin cursor)) : List (AtomOrigin cursor) :=
  (atoms.map Atom.origin).filter (fun origin => reached.contains origin || reached.any (adjacent graph origin))

def component {atoms : List (Atom cursor)} (graph : OriginGraph atoms)
    (seed : AtomOrigin cursor) : List (AtomOrigin cursor) :=
  Nat.rec ((atoms.map Atom.origin).filter (fun origin => origin == seed))
    (fun _ reached => growComponent graph reached) atoms.length

theorem component_vertices {atoms : List (Atom cursor)} (graph : OriginGraph atoms)
    (seed origin : AtomOrigin cursor) (held : origin ∈ component graph seed) : origin ∈ atoms.map Atom.origin := by
  unfold component at held
  generalize atoms.length = count at held
  cases count with
  | zero => exact (List.mem_filter.mp held).1
  | succ count => exact (List.mem_filter.mp held).1

theorem component_unique {atoms : List (Atom cursor)} (graph : OriginGraph atoms)
    (unique : (atoms.map Atom.origin).Nodup) (seed : AtomOrigin cursor) : (component graph seed).Nodup := by
  unfold component
  generalize atoms.length = count
  cases count <;> exact unique.filter _

def componentAtoms {atoms : List (Atom cursor)} (graph : OriginGraph atoms)
    (seed : AtomOrigin cursor) : List (Atom cursor) :=
  atoms.filter (fun atom => (component graph seed).contains atom.origin)

def componentBonds {atoms : List (Atom cursor)} (graph : OriginGraph atoms)
    (seed : AtomOrigin cursor) : List (SourceBond cursor × ℤ) :=
  graph.incidence.support.toList.filterMap (fun bond =>
    if decide (0 < graph.incidence bond) && (component graph seed).contains bond.left &&
        (component graph seed).contains bond.right then some (bond,graph.incidence bond) else none)

def componentFormula {atoms : List (Atom cursor)} (graph : OriginGraph atoms)
    (seed : AtomOrigin cursor) (element : CPS1LocalChemicalExecution.PeptideMaterial.Element) : Nat :=
  ((componentAtoms graph seed).filter (fun atom => atom.descriptor.source.element == element)).length

def componentCharge {atoms : List (Atom cursor)} (graph : OriginGraph atoms) (seed : AtomOrigin cursor) : ℤ :=
  ((component graph seed).map graph.formalCharge).sum

def reactionOrigin (origin : AtomOrigin cursor) : Bool :=
  match origin with | .prior (.chain _) => false | _ => true

def reactionAtoms (atoms : List (Atom cursor)) : List (Atom cursor) :=
  atoms.filter (fun atom => reactionOrigin atom.origin)

def reactionDescriptors (fuel : List FuelKind) : List Graph.Atom :=
  ammoniaGraph.atoms ++ fuel.zipIdx.flatMap (fun entry => (fuelGraph entry.1).atoms)

theorem reaction_descriptors_source (prior : Classical.Source cursor) (fuel : List FuelKind) :
    (reactionAtoms (commonAtoms prior fuel)).map Atom.descriptor = reactionDescriptors fuel := by
  simp [reactionAtoms,reactionOrigin,commonAtoms,Classical.Source.atoms,reactionDescriptors,
    Classical.AtomOrigin.descriptor,List.filter_map,List.filter_flatMap,List.map_flatMap,
    List.map_map,Function.comp_def]

def descriptorCharge (atoms : List Graph.Atom) : ℤ := (atoms.map (fun atom => atom.source.charge)).sum
def descriptorElectrons (atoms : List Graph.Atom) : Nat := (atoms.map (fun atom => Charged.electrons atom.source)).sum

theorem first_reaction_descriptor_budget :
    (reactionDescriptors firstFuel).length = 95 ∧
    descriptorCharge (reactionDescriptors firstFuel) = -9 ∧
    descriptorElectrons (reactionDescriptors firstFuel) = 562 := by decide

theorem first_reaction_atoms_budget (prior : Classical.Source cursor) :
    (reactionAtoms (commonAtoms prior firstFuel)).length = 95 ∧
    descriptorCharge ((reactionAtoms (commonAtoms prior firstFuel)).map Atom.descriptor) = -9 ∧
    descriptorElectrons ((reactionAtoms (commonAtoms prior firstFuel)).map Atom.descriptor) = 562 := by
  have descriptors := reaction_descriptors_source prior firstFuel
  have length := congrArg List.length descriptors
  simp only [List.length_map] at length
  exact ⟨length.trans first_reaction_descriptor_budget.1,
    (congrArg descriptorCharge descriptors).trans first_reaction_descriptor_budget.2.1,
    (congrArg descriptorElectrons descriptors).trans first_reaction_descriptor_budget.2.2⟩

end
end CPS1MaterialIncidence
