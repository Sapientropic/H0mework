import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AddressedHydrolysis.Atomic
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AtomicDynamics.Body
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AtomicDynamics.Unique
import Mathlib.Data.List.Nodup

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace CPS1AddressedReactiveJoint
open CPS1AddressedHydrolysis CPS1LocalChemicalExecution CPS1AtomicSource
variable {frame : CPS1Recycling.Frame}

inductive Address
  | nucleus (origin : Origin)
  | electron (origin : Origin) (orbital : Nat)
  deriving DecidableEq

def Address.origin : Address → Origin
  | .nucleus source | .electron source _ => source

structure Particle where
  address : Address
  atom : Atom
  readout : CPS1AtomicDynamics.Charged.Particle
  deriving DecidableEq

def atomParticles (row : Atom × Nat) : List Particle :=
  ⟨.nucleus row.1.origin,row.1,
    ⟨.nucleus row.2,row.1.descriptor,
      (CPS1AtomicDynamics.Charged.atomicNumber row.1.descriptor.source.element : Int)⟩⟩ ::
    (List.range (CPS1AtomicDynamics.Charged.electrons row.1.descriptor.source)).map (fun orbital =>
      ⟨.electron row.1.origin orbital,row.1,⟨.electron row.2 orbital,row.1.descriptor,-1⟩⟩)

def particles (atoms : List Atom) : List Particle := atoms.zipIdx.flatMap atomParticles

def descriptorGraph (atoms : List Atom) : Graph.Molecule := ⟨atoms.map Atom.descriptor,[],[]⟩

theorem atom_particle_readout (row : Atom × Nat) :
    (atomParticles row).map Particle.readout =
      CPS1AtomicDynamics.Charged.atomParticles (row.1.descriptor,row.2) := by
  simp only [atomParticles,CPS1AtomicDynamics.Charged.atomParticles,List.map_cons,List.map_map,Function.comp_def]

theorem particle_readout (atoms : List Atom) :
    (particles atoms).map Particle.readout = CPS1AtomicDynamics.Charged.particles (descriptorGraph atoms) := by
  simp only [particles,CPS1AtomicDynamics.Charged.particles,descriptorGraph,List.map_flatMap,
    atom_particle_readout]
  rw [List.zipIdx_map]
  rw [List.flatMap_map]
  rfl

theorem particle_source (atoms : List Atom) (particle : Particle) (member : particle ∈ particles atoms) :
    particle.atom ∈ atoms ∧ particle.readout.source = particle.atom.descriptor := by
  rcases List.mem_flatMap.mp member with ⟨row,held,generated⟩
  have original := List.fst_mem_of_mem_zipIdx held
  rcases List.mem_cons.mp generated with nucleus | electron
  · subst particle
    exact ⟨original,rfl⟩
  · rcases List.mem_map.mp electron with ⟨orbital,_,rfl⟩
    exact ⟨original,rfl⟩

theorem particle_readout_unique (atoms : List Atom) :
    ((particles atoms).map (fun particle => particle.readout.address)).Nodup := by
  change ((particles atoms).map (CPS1AtomicDynamics.Charged.Particle.address ∘ Particle.readout)).Nodup
  rw [← List.map_map,particle_readout]
  exact CPS1AtomicDynamics.Charged.particles_unique _

theorem atom_particle_origin (row : Atom × Nat) (particle : Particle)
    (member : particle ∈ atomParticles row) : particle.address.origin = row.1.origin := by
  rcases List.mem_cons.mp member with first | rest
  · cases first
    rfl
  · rcases List.mem_map.mp rest with ⟨orbital,_,rfl⟩
    rfl

theorem atom_particles_unique (row : Atom × Nat) :
    ((atomParticles row).map Particle.address).Nodup := by
  simp only [atomParticles,List.map_cons,List.map_map,Function.comp_def]
  apply List.nodup_cons.mpr
  constructor
  · simp
  · exact List.nodup_range.map (fun _ _ same => (Address.electron.inj same).2)

theorem particles_unique (atoms : List Atom) (unique : (atoms.map Atom.origin).Nodup) :
    ((particles atoms).map Particle.address).Nodup := by
  have origins : (atoms.zipIdx.map (fun row => row.1.origin)).Nodup := by
    change (atoms.zipIdx.map (Atom.origin ∘ Prod.fst)).Nodup
    rw [← List.map_map,List.zipIdx_map_fst]
    exact unique
  have rows := List.pairwise_map.mp origins
  apply List.pairwise_map.mpr
  apply List.pairwise_flatMap.mpr
  constructor
  · intro row _
    exact List.pairwise_map.mp (atom_particles_unique row)
  · apply rows.imp
    intro first second different a amember b bmember same
    apply different
    have key := congrArg Address.origin same
    rw [atom_particle_origin first a amember,atom_particle_origin second b bmember] at key
    exact key

def rawWaterAtoms (water : Water) : List Atom :=
  waterAtoms.map (fun slot =>
    ⟨.water water slot,
      ⟨⟨water.batch,toString water.ordinal ++ "/" ++
        (match slot with | .aminoH => "H0" | .hydroxylH => "H1" | .oxygen => "O")⟩,
        ⟨(match slot with | .aminoH => "H0" | .hydroxylH => "H1" | .oxygen => "O"),
          slot.element,slot.charge,false,"rawWater",false,false,false,false⟩⟩⟩)

theorem raw_water_origins (water : Water) :
    (rawWaterAtoms water).map Atom.origin = waterAtoms.map (Origin.water water) := by
  simp only [rawWaterAtoms,List.map_map,Function.comp_def]

theorem raw_water_payload (water : Water) (atom : Atom) (member : atom ∈ rawWaterAtoms water) :
    ∃ slot ∈ waterAtoms, atom.origin = .water water slot ∧
      atom.descriptor.source.element = slot.element ∧ atom.descriptor.source.charge = slot.charge := by
  rcases List.mem_map.mp member with ⟨slot,held,rfl⟩
  exact ⟨slot,held,rfl,rfl,rfl⟩

def seeded (material : LocalMaterial frame) (chain : Chain frame) : Atomic.Carrier frame :=
  let graph := Graph.fromChain frame chain
  let atoms := oldAtoms graph
  ⟨material,chain,atoms,graph.bonds.filterMap (resolveBond? atoms)⟩

theorem seeded_aligned (material : LocalMaterial frame) (chain : Chain frame) :
    Atomic.Aligned (seeded material chain).atoms chain := by
  refine ⟨?_,?_,?_⟩
  · have same : ((seeded material chain).atoms.map Atom.descriptor) = (Graph.fromChain frame chain).atoms := by
      simp only [seeded,oldAtoms,List.map_map,Function.comp_def]
      exact List.zipIdx_map_fst 0 _
    exact same ▸ List.Perm.refl _
  · rw [show (seeded material chain).atoms = oldAtoms (Graph.fromChain frame chain) from rfl,old_origins]
    exact List.nodup_range.map (fun _ _ same => Origin.old.inj same)
  · have same : ((seeded material chain).atoms.map (fun atom => atom.descriptor.address)) =
        (Graph.fromChain frame chain).atoms.map Graph.Atom.address := by
      simp only [seeded,oldAtoms,List.map_map,Function.comp_def]
      change ((Graph.fromChain frame chain).atoms.zipIdx.map
        (Graph.Atom.address ∘ Prod.fst)) = _
      rw [← List.map_map,List.zipIdx_map_fst]
    rw [same]
    exact graph_addresses_unique _ _

def descriptorAtom? (atoms : List Atom) (source : Graph.Atom) : Option Atom :=
  atoms.find? (fun atom => atom.descriptor = source)

def orderAtoms (atoms : List Atom) (source : List Graph.Atom) : List Atom :=
  source.filterMap (descriptorAtom? atoms)

theorem descriptor_atom_exists (atoms : List Atom) (source : Graph.Atom)
    (member : source ∈ atoms.map Atom.descriptor) :
    ∃ atom, descriptorAtom? atoms source = some atom ∧ atom ∈ atoms ∧ atom.descriptor = source := by
  have available : (descriptorAtom? atoms source).isSome := by
    apply List.find?_isSome.mpr
    rcases List.mem_map.mp member with ⟨atom,held,same⟩
    exact ⟨atom,held,decide_eq_true same⟩
  cases found : descriptorAtom? atoms source with
  | none => rw [found] at available; cases available
  | some atom =>
    exact ⟨atom,rfl,List.mem_of_find?_eq_some found,
      of_decide_eq_true (List.find?_some (p := fun value : Atom => decide (value.descriptor = source)) found)⟩

theorem ordered_source (atoms : List Atom) (source : List Graph.Atom) (atom : Atom)
    (member : atom ∈ orderAtoms atoms source) : atom ∈ atoms := by
  rcases List.mem_filterMap.mp member with ⟨descriptor,_,selected⟩
  exact List.mem_of_find?_eq_some selected

theorem ordered_descriptors (atoms : List Atom) (source : List Graph.Atom)
    (represented : ∀ descriptor ∈ source, descriptor ∈ atoms.map Atom.descriptor) :
    (orderAtoms atoms source).map Atom.descriptor = source := by
  induction source with
  | nil => rfl
  | cons descriptor rest ih =>
    rcases descriptor_atom_exists atoms descriptor (represented descriptor List.mem_cons_self) with
      ⟨atom,selected,_,identity⟩
    rw [orderAtoms,List.filterMap_cons,selected,List.map_cons,identity]
    exact congrArg (List.cons descriptor) (ih (fun source held => represented source (List.mem_cons_of_mem _ held)))

theorem ordered_permutation (carrier : Atomic.Carrier frame) (aligned : Atomic.Aligned carrier.atoms carrier.chain) :
    (orderAtoms carrier.atoms (Graph.fromChain frame carrier.chain).atoms).Perm carrier.atoms := by
  let ordered := orderAtoms carrier.atoms (Graph.fromChain frame carrier.chain).atoms
  have sourceUnique : (Graph.fromChain frame carrier.chain).atoms.Nodup :=
    List.Nodup.of_map Graph.Atom.address (graph_addresses_unique _ _)
  have unique : (carrier.atoms.map Atom.descriptor).Nodup := aligned.1.nodup_iff.mpr sourceUnique
  have descriptors : ordered.map Atom.descriptor = (Graph.fromChain frame carrier.chain).atoms :=
    ordered_descriptors carrier.atoms _ (fun source held => aligned.1.mem_iff.mpr held)
  have orderedUnique : ordered.Nodup := List.Nodup.of_map Atom.descriptor (descriptors ▸ sourceUnique)
  apply (List.perm_ext_iff_of_nodup orderedUnique (List.Nodup.of_map Atom.descriptor unique)).mpr
  intro atom
  constructor
  · exact ordered_source _ _ atom
  · intro member
    have descriptorPresent : atom.descriptor ∈ ordered.map Atom.descriptor := by
      rw [descriptors]
      exact aligned.1.mem_iff.mp (List.mem_map.mpr ⟨atom,member,rfl⟩)
    rcases List.mem_map.mp descriptorPresent with ⟨selected,held,same⟩
    have identity := List.inj_on_of_nodup_map unique (ordered_source _ _ _ held) member same
    simpa only [identity] using held

inductive Missing
  | materialGraph
  | atomicHistory
  | incompatibleCarrier
  deriving DecidableEq

inductive Block (frame : CPS1Recycling.Frame)
  | chain (carrier : Atomic.Carrier frame)
  | water (material : LocalMaterial frame) (source : Water)
  | residual (material : LocalMaterial frame) (reason : Missing)

def Block.material : Block frame → LocalMaterial frame
  | .chain carrier => carrier.material
  | .water material _ | .residual material _ => material

def Block.atoms : Block frame → List Atom
  | .chain carrier => orderAtoms carrier.atoms (Graph.fromChain frame carrier.chain).atoms
  | .water _ sourceWater => rawWaterAtoms sourceWater
  | .residual .. => []

def block (history : List (Atomic.Carrier frame)) (material : LocalMaterial frame) : Block frame := by
  exact match material.species with
  | .chain chain =>
    match Atomic.carrierAt? history material with
    | some previous =>
      if previous.chain = chain ∧ Atomic.Aligned previous.atoms chain then
        .chain {previous with material := material}
      else .residual material .incompatibleCarrier
    | none =>
      if chain.hydrolysed = [] then .chain (seeded material chain)
      else .residual material .atomicHistory
  | _ =>
    match waterSource? material with
    | some water => .water material water
    | none => .residual material .materialGraph

def blocks (history : List (Atomic.Carrier frame)) (stock : List (LocalMaterial frame)) : List (Block frame) :=
  stock.map (block history)

def atoms (history : List (Atomic.Carrier frame)) (stock : List (LocalMaterial frame)) : List Atom :=
  (blocks history stock).flatMap Block.atoms

def residuals (history : List (Atomic.Carrier frame)) (stock : List (LocalMaterial frame)) :
    List (LocalMaterial frame × Missing) :=
  (blocks history stock).filterMap (fun block => match block with
    | .residual material reason => some (material,reason) | _ => none)

theorem block_material (history : List (Atomic.Carrier frame)) (material : LocalMaterial frame) :
    (block history material).material = material := by
  unfold block
  cases kind : material.species <;> simp only
  case chain chain =>
    cases found : Atomic.carrierAt? history material <;> simp only
    all_goals split <;> rfl
  all_goals cases source : waterSource? material <;> rfl

theorem blocks_whole (history : List (Atomic.Carrier frame)) (stock : List (LocalMaterial frame)) :
    (blocks history stock).map Block.material = stock := by
  simp only [blocks,List.map_map,Function.comp_def,block_material,List.map_id_fun',id_eq]

theorem block_charge_valid (history : List (Atomic.Carrier frame)) (material : LocalMaterial frame)
    (atom : Atom) (member : atom ∈ (block history material).atoms) :
    atom.descriptor.source.charge ≤ (CPS1AtomicDynamics.Charged.atomicNumber atom.descriptor.source.element : Int) := by
  have from_chain (chain : Chain frame) (carrier : Atomic.Carrier frame)
      (aligned : Atomic.Aligned carrier.atoms chain) (present : atom ∈ carrier.atoms) :
      atom.descriptor.source.charge ≤ (CPS1AtomicDynamics.Charged.atomicNumber atom.descriptor.source.element : Int) := by
    have source := aligned.1.mem_iff.mp (List.mem_map.mpr ⟨atom,present,rfl⟩)
    exact CPS1AtomicDynamics.Charged.graph_atom_valid _ _ _ source
  have from_water (water : Water) (present : atom ∈ rawWaterAtoms water) :
      atom.descriptor.source.charge ≤ (CPS1AtomicDynamics.Charged.atomicNumber atom.descriptor.source.element : Int) := by
    rcases raw_water_payload water atom present with ⟨slot,_,_,element,charge⟩
    rw [element,charge]
    cases slot <;> decide
  unfold block at member
  cases kind : material.species <;> simp only [kind] at member
  case chain chain =>
    cases found : Atomic.carrierAt? history material with
    | none =>
      simp only [found] at member
      split at member
      · exact from_chain chain (seeded material chain) (seeded_aligned material chain)
          (ordered_source _ _ _ member)
      · exact False.elim (List.not_mem_nil member)
    | some previous =>
      simp only [found] at member
      split at member
      · rename_i paid
        exact from_chain chain previous paid.2 (ordered_source _ _ _ member)
      · exact False.elim (List.not_mem_nil member)
  all_goals
    cases source : waterSource? material <;> simp only [source] at member
    · exact False.elim (List.not_mem_nil member)
    · exact from_water _ member

theorem atoms_charge_valid (history : List (Atomic.Carrier frame)) (stock : List (LocalMaterial frame)) :
    ∀ atom ∈ atoms history stock,
      atom.descriptor.source.charge ≤ (CPS1AtomicDynamics.Charged.atomicNumber atom.descriptor.source.element : Int) := by
  intro atom member
  rcases List.mem_flatMap.mp member with ⟨piece,held,present⟩
  rcases List.mem_map.mp held with ⟨material,_,rfl⟩
  exact block_charge_valid history material atom present

theorem generated_charge (history : List (Atomic.Carrier frame)) (stock : List (LocalMaterial frame)) :
    CPS1AtomicDynamics.Charged.charge ((particles (atoms history stock)).map Particle.readout) =
      Graph.charge (descriptorGraph (atoms history stock)) := by
  rw [particle_readout]
  apply CPS1AtomicDynamics.Charged.particles_charge
  intro atom member
  rcases List.mem_map.mp member with ⟨source,held,rfl⟩
  exact atoms_charge_valid history stock source held

end CPS1AddressedReactiveJoint
