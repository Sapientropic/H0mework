import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1PhosphorylExchange.Native
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AtomicSource.PrimaryFacts
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1EnzymeBath.PrimaryFacts
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1MaterialIncidence
noncomputable section
open CPS1AtomicSource CPS1AtomicDynamics CPS1SameEventFunction CPS1PhosphorylExchange
open scoped BigOperators
variable {frame : CPS1Recycling.Frame}

private theorem residue_atoms_unique (edges : List Nat) (row : CPS1ResourceExecution.AA × Nat) :
    (Graph.residueAtoms Primary.template edges row).Nodup := by
  have original : (Primary.template row.1).atoms.Nodup :=
    List.Nodup.of_map Primary.Atom.name (Primary.original_names_unique row.1)
  apply List.Nodup.map _ (original.filter _)
  intro first second same
  exact congrArg Graph.Atom.source same

private theorem residue_atom_index (edges : List Nat) (row : CPS1ResourceExecution.AA × Nat)
    (atom : Graph.Atom) (held : atom ∈ Graph.residueAtoms Primary.template edges row) :
    atom.address.residue = row.2 := by
  obtain ⟨original,_,same⟩ := List.mem_map.mp held
  subst atom
  rfl

theorem chain_atoms_unique (word : List CPS1ResourceExecution.AA) (edges : List Nat) :
    (Graph.build Primary.template word edges).atoms.Nodup := by
  have ordinals : (word.zipIdx.map Prod.snd).Nodup := by
    rw [List.zipIdx_map_snd]
    exact List.nodup_range' _
  apply List.pairwise_flatMap.mpr
  refine ⟨fun row _ => residue_atoms_unique _ row,?_⟩
  apply (List.pairwise_map.mp ordinals).imp
  intro first second different left leftHeld right rightHeld same
  have index := congrArg (fun atom : Graph.Atom => atom.address.residue) same
  rw [residue_atom_index _ first left leftHeld,residue_atom_index _ second right rightHeld] at index
  exact different index

theorem prior_origins_unique {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Classical.Source cursor) : source.atoms.Nodup := by
  have chain : source.graph.atoms.Nodup :=
    chain_atoms_unique (CPS1LocalChemicalExecution.Actual.cps1 frame).word source.chain.bonds
  have ammonia : ammoniaGraph.atoms.Nodup := by decide
  unfold Classical.Source.atoms
  apply List.nodup_append.mpr
  refine ⟨List.Nodup.map (fun _ _ same => Classical.AtomOrigin.chain.inj same) chain,
    List.Nodup.map (fun _ _ same => (Classical.AtomOrigin.ammonia.inj same).2) ammonia,?_⟩
  intro first firstHeld second secondHeld same
  obtain ⟨left,_,leftSame⟩ := List.mem_map.mp firstHeld
  obtain ⟨right,_,rightSame⟩ := List.mem_map.mp secondHeld
  subst first
  subst second
  cases leftSame

private def fuelOrigins {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (entry : FuelKind × Nat) : List (AtomOrigin cursor) :=
  (fuelGraph entry.1).atoms.map (AtomOrigin.fuel entry.2 entry.1)

private theorem fuel_atoms_unique (kind : FuelKind) : (fuelGraph kind).atoms.Nodup := by
  cases kind <;> decide

private theorem fuel_origin_slot {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (entry : FuelKind × Nat) (origin : AtomOrigin cursor) (held : origin ∈ fuelOrigins entry) :
    ∃ payload, origin = .fuel entry.2 entry.1 payload := by
  obtain ⟨payload,_,same⟩ := List.mem_map.mp held
  exact ⟨payload,same.symm⟩

private theorem fuel_origins_unique {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (fuel : List FuelKind) : (fuel.zipIdx.flatMap (fuelOrigins (cursor := cursor))).Nodup := by
  have ordinals : (fuel.zipIdx.map Prod.snd).Nodup := by
    rw [List.zipIdx_map_snd]
    exact List.nodup_range' _
  apply List.pairwise_flatMap.mpr
  constructor
  · intro entry _
    exact List.Nodup.map (fun _ _ same => (AtomOrigin.fuel.inj same).2.2)
      (fuel_atoms_unique entry.1)
  · apply (List.pairwise_map.mp ordinals).imp
    intro first second different left leftHeld right rightHeld same
    obtain ⟨leftAtom,leftActual⟩ := fuel_origin_slot first left leftHeld
    obtain ⟨rightAtom,rightActual⟩ := fuel_origin_slot second right rightHeld
    rw [leftActual,rightActual] at same
    exact different (AtomOrigin.fuel.inj same).1

theorem common_origins_unique {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Classical.Source cursor) (fuel : List FuelKind) :
    ((commonAtoms source fuel).map Atom.origin).Nodup := by
  simp only [commonAtoms,List.map_append,List.map_map,List.map_flatMap,Function.comp_def]
  change (source.atoms.map AtomOrigin.prior ++ fuel.zipIdx.flatMap fuelOrigins).Nodup
  apply List.nodup_append.mpr
  refine ⟨List.Nodup.map (fun _ _ same => AtomOrigin.prior.inj same) (prior_origins_unique source),
    fuel_origins_unique fuel,?_⟩
  intro first firstHeld second secondHeld same
  obtain ⟨prior,_,priorActual⟩ := List.mem_map.mp firstHeld
  obtain ⟨entry,_,entryHeld⟩ := List.mem_flatMap.mp secondHeld
  obtain ⟨payload,payloadActual⟩ := fuel_origin_slot entry second entryHeld
  rw [← priorActual,payloadActual] at same
  cases same

variable {cursor : CPS1ReactiveNuclear.SourceCursor frame} {priorRaw : Classical.Raw}
variable {before : Classical.Current cursor priorRaw} {step : Classical.NativeStep before priorRaw.time}
variable {raw : CPS1PhosphorylExchange.Raw}

def vertices (source : Common before step raw) : List (AtomOrigin cursor) := source.atoms.map Atom.origin

theorem source_vertices_unique (source : Common before step raw) : (vertices source).Nodup := by
  rw [vertices,source.atomSource]
  exact common_origins_unique before.packet.source raw.fuel

def originAt (source : Common before step raw) (slot : Fin source.atoms.length) : AtomOrigin cursor :=
  (source.atoms.get slot).origin

theorem source_origin_injective (source : Common before step raw) : Function.Injective (originAt source) := by
  intro first second same
  apply Fin.ext
  have equal : (vertices source)[first.val]'(by simp [vertices]) =
      (vertices source)[second.val]'(by simp [vertices]) := by
    simpa only [vertices,List.getElem_map,originAt,List.get_eq_getElem] using same
  exact (List.getElem_inj (source_vertices_unique source)).mp equal

private theorem atom_particle_descriptor (entry : Graph.Atom × Nat) (particle : Charged.Particle)
    (held : particle ∈ Charged.atomParticles entry) : particle.source = entry.1 := by
  rcases List.mem_cons.mp held with first | rest
  · subst particle
    rfl
  · obtain ⟨orbital,_,same⟩ := List.mem_map.mp rest
    subst particle
    rfl

theorem current_particles_source (source : Common before step raw) (current : NativeCurrent source) :
    current.nodes.map Body.Node.particle = commonParticles before.packet.source raw.fuel :=
  current.atomsActual.trans (common_measured_whole source).1

private theorem current_atom_slot_generated (source : Common before step raw) (current : NativeCurrent source)
    (node : Body.Node) (held : node ∈ current.nodes) :
    ∃ atom : Atom cursor, source.atoms[node.particle.address.slot]? = some atom ∧
      node.particle.source = atom.descriptor := by
  have generated : node.particle ∈ commonParticles before.packet.source raw.fuel := by
    rw [← current_particles_source source current]
    exact List.mem_map_of_mem held
  have table : commonParticles before.packet.source raw.fuel =
      source.atoms.zipIdx.flatMap (fun entry => Charged.atomParticles (entry.1.descriptor,entry.2)) := by
    rw [source.atomSource]
    rfl
  rw [table] at generated
  obtain ⟨entry,entryHeld,particleHeld⟩ := List.mem_flatMap.mp generated
  have slot := Charged.atom_particle_slot (entry.1.descriptor,entry.2) node.particle particleHeld
  refine ⟨entry.1,?_,atom_particle_descriptor _ _ particleHeld⟩
  rw [slot]
  exact List.mk_mem_zipIdx_iff_getElem?.mp entryHeld

theorem current_atom_slot_lt (source : Common before step raw) (current : NativeCurrent source)
    (node : Body.Node) (held : node ∈ current.nodes) : node.particle.address.slot < source.atoms.length := by
  obtain ⟨atom,found,_⟩ := current_atom_slot_generated source current node held
  exact (List.getElem?_eq_some_iff.mp found).1

def atomIndex (source : Common before step raw) (current : NativeCurrent source)
    (node : Body.Node) (held : node ∈ current.nodes) : Fin source.atoms.length :=
  ⟨node.particle.address.slot,current_atom_slot_lt source current node held⟩

def atomOriginAtNode (source : Common before step raw) (current : NativeCurrent source)
    (node : Body.Node) (held : node ∈ current.nodes) : AtomOrigin cursor :=
  originAt source (atomIndex source current node held)

theorem current_atom_descriptor (source : Common before step raw) (current : NativeCurrent source)
    (node : Body.Node) (held : node ∈ current.nodes) :
    node.particle.source = (source.atoms.get (atomIndex source current node held)).descriptor := by
  obtain ⟨atom,found,descriptor⟩ := current_atom_slot_generated source current node held
  have actual : source.atoms.get (atomIndex source current node held) = atom := by
    exact (List.getElem?_eq_some_iff.mp found).2
  rw [actual]
  exact descriptor

theorem current_atom_origin (source : Common before step raw) (current : NativeCurrent source)
    (node : Body.Node) (held : node ∈ current.nodes) :
    originAt? source.atoms node.particle.address = some (atomOriginAtNode source current node held) := by
  have actual : source.atoms[node.particle.address.slot]? =
      some (source.atoms.get (atomIndex source current node held)) := by
    exact List.getElem?_eq_getElem (current_atom_slot_lt source current node held)
  simp only [originAt?,actual,Option.map_some,atomOriginAtNode,originAt]

theorem current_nucleus_slot (source : Common before step raw) (current : NativeCurrent source)
    (node : Body.Node) (held : node ∈ nucleusNodes current.nodes) :
      node.particle.address = .nucleus (atomIndex source current node (List.mem_filter.mp held).1).val := by
  have nuclear := (List.mem_filter.mp held).2
  change node.particle.address = .nucleus node.particle.address.slot
  cases address : node.particle.address with
  | electron slot orbital => simp only [address,Bool.false_eq_true] at nuclear
  | nucleus slot => rfl

private def resolveGraphBonds (graph : Graph.Molecule) (origin : Graph.Atom → AtomOrigin cursor) :
    List (SourceBond cursor) :=
  graph.bonds.filterMap (fun bond => do
    let first ← graph.atoms.find? (fun atom => atom.address == bond.left)
    let second ← graph.atoms.find? (fun atom => atom.address == bond.right)
    pure ⟨origin first,origin second,bond.order,bond.aromatic,bond.stereo⟩)

private theorem resolved_bond_vertices (graph : Graph.Molecule) (origin : Graph.Atom → AtomOrigin cursor)
    (bond : SourceBond cursor) (held : bond ∈ resolveGraphBonds graph origin) :
    bond.left ∈ graph.atoms.map origin ∧ bond.right ∈ graph.atoms.map origin := by
  obtain ⟨original,_,found⟩ := List.mem_filterMap.mp held
  simp only [Bind.bind,Option.bind_eq_some_iff,Pure.pure,Option.some.injEq] at found
  obtain ⟨left,leftFound,right,rightFound,same⟩ := found
  subst bond
  exact ⟨List.mem_map_of_mem (List.mem_of_find?_eq_some leftFound),
    List.mem_map_of_mem (List.mem_of_find?_eq_some rightFound)⟩

private theorem common_bonds_resolved (prior : Classical.Source cursor) (fuel : List FuelKind) :
    commonBonds prior fuel =
      resolveGraphBonds prior.graph (fun atom => .prior (.chain atom)) ++
      resolveGraphBonds ammoniaGraph (fun atom => .prior (.ammonia prior.ammonia.slot atom)) ++
      fuel.zipIdx.flatMap (fun entry => resolveGraphBonds (fuelGraph entry.1) (.fuel entry.2 entry.1)) := rfl

theorem common_bond_vertices (prior : Classical.Source cursor) (fuel : List FuelKind)
    (bond : SourceBond cursor) (held : bond ∈ commonBonds prior fuel) :
    bond.left ∈ (commonAtoms prior fuel).map Atom.origin ∧
      bond.right ∈ (commonAtoms prior fuel).map Atom.origin := by
  rw [common_bonds_resolved] at held
  have priorHeld (origin : AtomOrigin cursor)
      (present : origin ∈ (prior.atoms.map (fun atom => AtomOrigin.prior atom))) :
      origin ∈ (commonAtoms prior fuel).map Atom.origin := by
    simpa only [commonAtoms,List.map_append,List.map_flatMap,List.map_map,Function.comp_def] using
      List.mem_append_left (fuel.zipIdx.flatMap (fun entry => (fuelGraph entry.1).atoms.map
        (fun atom => AtomOrigin.fuel entry.2 entry.1 atom))) present
  rcases List.mem_append.mp held with priorBond | fuelBond
  · rcases List.mem_append.mp priorBond with chainBond | ammoniaBond
    · have endpoints := resolved_bond_vertices prior.graph (fun atom => .prior (.chain atom)) bond chainBond
      have injectOrigin (origin : AtomOrigin cursor) (present : origin ∈ prior.graph.atoms.map (fun atom => .prior (.chain atom))) :
          origin ∈ (commonAtoms prior fuel).map Atom.origin := by
        apply priorHeld
        simpa only [Classical.Source.atoms,List.map_append,List.map_map,Function.comp_def] using
          List.mem_append_left (ammoniaGraph.atoms.map (fun atom => AtomOrigin.prior (.ammonia prior.ammonia.slot atom))) present
      exact ⟨injectOrigin _ endpoints.1,injectOrigin _ endpoints.2⟩
    · have endpoints := resolved_bond_vertices ammoniaGraph (fun atom => .prior (.ammonia prior.ammonia.slot atom)) bond ammoniaBond
      have injectOrigin (origin : AtomOrigin cursor) (present : origin ∈ ammoniaGraph.atoms.map (fun atom => .prior (.ammonia prior.ammonia.slot atom))) :
          origin ∈ (commonAtoms prior fuel).map Atom.origin := by
        apply priorHeld
        simpa only [Classical.Source.atoms,List.map_append,List.map_map,Function.comp_def] using
          List.mem_append_right (prior.graph.atoms.map (fun atom => AtomOrigin.prior (.chain atom))) present
      exact ⟨injectOrigin _ endpoints.1,injectOrigin _ endpoints.2⟩
  · obtain ⟨entry,entryHeld,bondHeld⟩ := List.mem_flatMap.mp fuelBond
    have endpoints := resolved_bond_vertices (fuelGraph entry.1) (.fuel entry.2 entry.1) bond bondHeld
    have injectOrigin (origin : AtomOrigin cursor) (present : origin ∈ (fuelGraph entry.1).atoms.map (.fuel entry.2 entry.1)) :
        origin ∈ (commonAtoms prior fuel).map Atom.origin := by
      simp only [commonAtoms,List.map_append,List.map_map,List.map_flatMap,Function.comp_def]
      exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨entry,entryHeld,present⟩)
    exact ⟨injectOrigin _ endpoints.1,injectOrigin _ endpoints.2⟩

theorem source_bond_vertices (source : Common before step raw)
    (bond : SourceBond cursor) (held : bond ∈ source.bonds) :
    bond.left ∈ vertices source ∧ bond.right ∈ vertices source := by
  rw [source.bondSource] at held
  rw [vertices,source.atomSource]
  exact common_bond_vertices before.packet.source raw.fuel bond held

abbrev Incidence (cursor : CPS1ReactiveNuclear.SourceCursor frame) := SourceBond cursor →₀ ℤ
abbrev Charges (cursor : CPS1ReactiveNuclear.SourceCursor frame) := AtomOrigin cursor →₀ ℤ

def bondInventory (bonds : List (SourceBond cursor)) : Incidence cursor :=
  (bonds.map (fun bond => Finsupp.single bond 1)).sum

def chargeInventory (atoms : List (Atom cursor)) : Charges cursor :=
  (atoms.map (fun atom => Finsupp.single atom.origin atom.descriptor.source.charge)).sum

structure OriginGraph (atoms : List (Atom cursor)) where
  incidence : Incidence cursor
  formalCharge : Charges cursor

def sourceGraph (source : Common before step raw) : OriginGraph source.atoms :=
  ⟨bondInventory source.bonds,chargeInventory source.atoms⟩

def graphAt (source : Common before step raw) (_current : NativeCurrent source) : OriginGraph source.atoms :=
  sourceGraph source

def sourceMaterial (source : Common before step raw) (current : NativeCurrent source) :
    NativeCurrent source × OriginGraph source.atoms :=
  (current,sourceGraph source)

theorem graph_at_source (source : Common before step raw) (current : NativeCurrent source) :
    (graphAt source current).incidence = bondInventory (commonBonds before.packet.source raw.fuel) ∧
    current.nodes.map Body.Node.particle = commonParticles before.packet.source raw.fuel ∧
    current.occupied.conjTranspose * current.occupied = 1 ∧
    Matrix.trace (density current.occupied) = (electronCount source.nodes : ℂ) ∧
    current.remaining = unspentLive before.packet.source current.chainSlot := by
  exact ⟨congrArg bondInventory source.bondSource,current_particles_source source current,
    current.occupiedGram,current.electronNumber,current.remainingActual⟩

structure BondToken (cursor : CPS1ReactiveNuclear.SourceCursor frame) where
  debit : SourceBond cursor
  credit : SourceBond cursor
  deriving DecidableEq

def BondToken.delta (token : BondToken cursor) : Incidence cursor :=
  Finsupp.single token.credit 1-Finsupp.single token.debit 1

def applyToken {atoms : List (Atom cursor)} (graph : OriginGraph atoms) (token : BondToken cursor) : OriginGraph atoms :=
  {graph with incidence := graph.incidence+token.delta}

def foldTokens {atoms : List (Atom cursor)} (graph : OriginGraph atoms) (tokens : List (BondToken cursor)) : OriginGraph atoms :=
  tokens.foldl applyToken graph

def foldMaterial (source : Common before step raw)
    (material : NativeCurrent source × OriginGraph source.atoms) (tokens : List (BondToken cursor)) :
    NativeCurrent source × OriginGraph source.atoms :=
  (material.1,foldTokens material.2 tokens)

theorem material_field_preserved (source : Common before step raw) (current : NativeCurrent source)
    (tokens : List (BondToken cursor)) :
    (foldMaterial source (sourceMaterial source current) tokens).1 = current := rfl

theorem apply_token_incidence {atoms : List (Atom cursor)} (graph : OriginGraph atoms) (token : BondToken cursor) :
    (applyToken graph token).incidence = graph.incidence+token.delta := rfl

theorem apply_token_other {atoms : List (Atom cursor)} (graph : OriginGraph atoms) (token : BondToken cursor)
    (bond : SourceBond cursor) (notDebit : bond ≠ token.debit) (notCredit : bond ≠ token.credit) :
    (applyToken graph token).incidence bond = graph.incidence bond := by
  simp [applyToken,BondToken.delta,notDebit,notCredit]

theorem fold_tokens_incidence {atoms : List (Atom cursor)} (graph : OriginGraph atoms) (tokens : List (BondToken cursor)) :
    (foldTokens graph tokens).incidence = graph.incidence+(tokens.map BondToken.delta).sum := by
  induction tokens generalizing graph with
  | nil => simp [foldTokens]
  | cons token rest ih =>
    simp only [foldTokens,List.foldl_cons]
    rw [show (List.foldl applyToken (applyToken graph token) rest).incidence =
      (applyToken graph token).incidence+(rest.map BondToken.delta).sum from ih (applyToken graph token)]
    simp only [applyToken,List.map_cons,List.sum_cons]
    abel

theorem fold_tokens_charge {atoms : List (Atom cursor)} (graph : OriginGraph atoms) (tokens : List (BondToken cursor)) :
    (foldTokens graph tokens).formalCharge = graph.formalCharge := by
  induction tokens generalizing graph with
  | nil => rfl
  | cons token rest ih => exact ih (applyToken graph token)

def sourceToken? (source : Common before step raw) (current : NativeCurrent source) : Option (BondToken cursor) := do
  let centre ← originAt? source.atoms current.channel.phosphorus
  let leaving ← originAt? source.atoms current.channel.leavingOxygen
  let attacking ← originAt? source.atoms current.channel.attackingOxygen
  let old ← source.bonds.find? (fun bond =>
    ((bond.left == centre && bond.right == leaving) || (bond.left == leaving && bond.right == centre)) &&
      bond.order == "SING")
  pure ⟨old,{old with left := centre,right := attacking}⟩

private theorem origin_lookup_mem (atoms : List (Atom cursor)) (address : Charged.Address)
    (origin : AtomOrigin cursor) (found : originAt? atoms address = some origin) :
    origin ∈ atoms.map Atom.origin := by
  unfold originAt? at found
  obtain ⟨atom,atomFound,same⟩ := Option.map_eq_some_iff.mp found
  rw [← same]
  exact List.mem_map_of_mem (List.mem_of_getElem? atomFound)

theorem source_token_vertices (source : Common before step raw) (current : NativeCurrent source)
    (token : BondToken cursor) (actual : sourceToken? source current = some token) :
    token.debit ∈ source.bonds ∧ token.debit.left ∈ vertices source ∧ token.debit.right ∈ vertices source ∧
      token.credit.left ∈ vertices source ∧ token.credit.right ∈ vertices source := by
  unfold sourceToken? at actual
  simp only [Bind.bind,Option.bind_eq_some_iff,Pure.pure,Option.some.injEq] at actual
  obtain ⟨centre,centreFound,leaving,_,attacking,attackingFound,old,oldFound,same⟩ := actual
  subst token
  have oldHeld := List.mem_of_find?_eq_some oldFound
  have oldVertices := source_bond_vertices source old oldHeld
  exact ⟨oldHeld,oldVertices.1,oldVertices.2,origin_lookup_mem source.atoms _ _ centreFound,
    origin_lookup_mem source.atoms _ _ attackingFound⟩

end
end CPS1MaterialIncidence
