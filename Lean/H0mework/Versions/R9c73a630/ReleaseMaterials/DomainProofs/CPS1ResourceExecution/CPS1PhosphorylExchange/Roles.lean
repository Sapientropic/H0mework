import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1PhosphorylExchange.Base

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1PhosphorylExchange
noncomputable section
open CPS1AtomicDynamics CPS1AtomicSource CPS1SameEventFunction
open scoped Topology BigOperators
variable {frame : CPS1Recycling.Frame}

def phosphorusDescriptor : Graph.Atom := atpGraph.atoms.get ⟨28,by decide⟩
def leavingDescriptor : Graph.Atom := atpGraph.atoms.get ⟨25,by decide⟩
def attackingDescriptor : Graph.Atom := bicarbonateGraph.atoms.get ⟨2,by decide⟩

theorem selected_descriptor_charges :
    (Charged.atomicNumber phosphorusDescriptor.source.element : Int) = 15 ∧
    (Charged.atomicNumber leavingDescriptor.source.element : Int) = 8 ∧
    (Charged.atomicNumber attackingDescriptor.source.element : Int) = 8 := by decide

theorem first_channel_distinct {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Classical.Source cursor) :
    (firstChannel source).phosphorus ≠ (firstChannel source).leavingOxygen ∧
    (firstChannel source).phosphorus ≠ (firstChannel source).attackingOxygen ∧
    (firstChannel source).leavingOxygen ≠ (firstChannel source).attackingOxygen := by
  simp [firstChannel]

private theorem selected_fresh_atoms {cursor : CPS1ReactiveNuclear.SourceCursor frame} :
    (freshAtoms (cursor := cursor))[28]? =
      some ⟨.fuel 0 .atp phosphorusDescriptor,phosphorusDescriptor⟩ ∧
    (freshAtoms (cursor := cursor))[25]? =
      some ⟨.fuel 0 .atp leavingDescriptor,leavingDescriptor⟩ ∧
    (freshAtoms (cursor := cursor))[88]? =
      some ⟨.fuel 2 .bicarbonate attackingDescriptor,attackingDescriptor⟩ := by
  exact ⟨rfl,rfl,rfl⟩

def phosphorusNode {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Classical.Source cursor) (x height : ℝ) : Body.Node :=
  ⟨⟨(firstChannel source).phosphorus,phosphorusDescriptor,15⟩,
    ⟨transversePoint x height 0,0,1⟩⟩

def leavingNode {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Classical.Source cursor) (x height : ℝ) : Body.Node :=
  ⟨⟨(firstChannel source).leavingOxygen,leavingDescriptor,8⟩,
    ⟨transversePoint x (height+1) 0,0,1⟩⟩

def attackingNode {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Classical.Source cursor) (x height : ℝ) : Body.Node :=
  ⟨⟨(firstChannel source).attackingOxygen,attackingDescriptor,8⟩,
    ⟨transversePoint x (height+2) 0,0,1⟩⟩

private theorem fresh_nucleus_numbered {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Classical.Source cursor) (ordinal : Nat) (atom : Atom cursor)
    (generated : (freshAtoms (cursor := cursor))[ordinal]? = some atom) :
    ∃ particleOrdinal,
      (⟨.nucleus (source.atoms.length+ordinal),atom.descriptor,
        (Charged.atomicNumber atom.descriptor.source.element : Int)⟩,particleOrdinal) ∈
          (freshParticles source).zipIdx := by
  have indexed : (atom,source.atoms.length+ordinal) ∈
      (freshAtoms (cursor := cursor)).zipIdx source.atoms.length :=
    List.mk_add_mem_zipIdx_iff_getElem?.mpr generated
  have particleHeld : (⟨.nucleus (source.atoms.length+ordinal),atom.descriptor,
      (Charged.atomicNumber atom.descriptor.source.element : Int)⟩ : Charged.Particle) ∈
      freshParticles source :=
    List.mem_flatMap.mpr ⟨(atom,source.atoms.length+ordinal),indexed,List.mem_cons_self⟩
  obtain ⟨particleOrdinal,found⟩ := List.getElem?_of_mem particleHeld
  exact ⟨particleOrdinal,List.mk_mem_zipIdx_iff_getElem?.mpr found⟩

theorem first_fresh_nuclei_present {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Classical.Source cursor) (x height : ℝ) :
    phosphorusNode source x height ∈ freshNodes source x height ∧
    leavingNode source x height ∈ freshNodes source x height ∧
    attackingNode source x height ∈ freshNodes source x height := by
  obtain ⟨pOrdinal,pHeld⟩ := fresh_nucleus_numbered source 28
    ⟨.fuel 0 .atp phosphorusDescriptor,phosphorusDescriptor⟩ selected_fresh_atoms.1
  obtain ⟨lOrdinal,lHeld⟩ := fresh_nucleus_numbered source 25
    ⟨.fuel 0 .atp leavingDescriptor,leavingDescriptor⟩ selected_fresh_atoms.2.1
  obtain ⟨aOrdinal,aHeld⟩ := fresh_nucleus_numbered source 88
    ⟨.fuel 2 .bicarbonate attackingDescriptor,attackingDescriptor⟩ selected_fresh_atoms.2.2
  have p := List.mem_map_of_mem (f := fun entry => (⟨entry.1,freshRow source x height entry⟩ : Body.Node)) pHeld
  have l := List.mem_map_of_mem (f := fun entry => (⟨entry.1,freshRow source x height entry⟩ : Body.Node)) lHeld
  have a := List.mem_map_of_mem (f := fun entry => (⟨entry.1,freshRow source x height entry⟩ : Body.Node)) aHeld
  simpa only [selected_descriptor_charges.1,selected_descriptor_charges.2.1,
    selected_descriptor_charges.2.2,freshRow,firstChannel,Charged.Address.nucleus.injEq,
    Nat.add_left_cancel_iff,show (25 : Nat) ≠ 28 by decide,show (88 : Nat) ≠ 28 by decide,
    show (88 : Nat) ≠ 25 by decide,if_true,if_false,phosphorusNode,leavingNode,attackingNode,freshNodes]
    using And.intro p (And.intro l a)

theorem node_at_unique (nodes : List Body.Node)
    (unique : (nodes.map (fun node => node.particle.address)).Nodup)
    (target : Body.Node) (held : target ∈ nodes) :
    nodeAt? nodes target.particle.address = some target := by
  let predicate := fun node : Body.Node => node.particle.address == target.particle.address
  have nonempty : (nodes.find? predicate).isSome :=
    List.find?_isSome.mpr ⟨target,held,by simp [predicate]⟩
  cases found : nodes.find? predicate with
  | none => rw [found] at nonempty; cases nonempty
  | some node =>
    have nodeHeld := List.mem_of_find?_eq_some found
    have address : node.particle.address = target.particle.address := by
      simpa only [predicate,beq_iff_eq] using List.find?_some (p := predicate) found
    have same := List.inj_on_of_nodup_map unique nodeHeld held address
    unfold nodeAt?
    change (nodes.find? predicate) = some target
    rw [found,same]

theorem base_addresses_unique {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} (before : Classical.Current cursor priorRaw)
    (step : Classical.NativeStep before priorRaw.time)
    (actual : Classical.fromCursor cursor priorRaw = .responded before step) (x height : ℝ) :
    ((baseNodes before step x height).map (fun node => node.particle.address)).Nodup := by
  change ((baseNodes before step x height).map (Charged.Particle.address ∘ Body.Node.particle)).Nodup
  rw [← List.map_map,base_particles before step actual x height]
  exact common_addresses_unique _ _

theorem first_base_nuclei_found {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} (before : Classical.Current cursor priorRaw)
    (step : Classical.NativeStep before priorRaw.time)
    (actual : Classical.fromCursor cursor priorRaw = .responded before step) (x height : ℝ) :
    nodeAt? (baseNodes before step x height) (firstChannel before.packet.source).phosphorus =
      some (phosphorusNode before.packet.source x height) ∧
    nodeAt? (baseNodes before step x height) (firstChannel before.packet.source).leavingOxygen =
      some (leavingNode before.packet.source x height) ∧
    nodeAt? (baseNodes before step x height) (firstChannel before.packet.source).attackingOxygen =
      some (attackingNode before.packet.source x height) := by
  have present := first_fresh_nuclei_present before.packet.source x height
  have unique := base_addresses_unique before step actual x height
  exact ⟨node_at_unique _ unique _ (List.mem_append_right _ present.1),
    node_at_unique _ unique _ (List.mem_append_right _ present.2.1),
    node_at_unique _ unique _ (List.mem_append_right _ present.2.2)⟩

private theorem fresh_atom_is_fuel {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (atom : Atom cursor) (held : atom ∈ freshAtoms (cursor := cursor)) :
    ∃ slot kind payload, atom.origin = .fuel slot kind payload := by
  obtain ⟨entry,_,present⟩ := List.mem_flatMap.mp held
  obtain ⟨payload,_,same⟩ := List.mem_map.mp present
  subst atom
  exact ⟨entry.2,entry.1,payload,rfl⟩

theorem fresh_node_outside_chain {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Classical.Source cursor) (x height : ℝ) (node : Body.Node)
    (held : node ∈ freshNodes source x height) :
    isChainNode (commonAtoms source firstFuel) node = false := by
  obtain ⟨numbered,numberedHeld,same⟩ := List.mem_map.mp held
  subst node
  have particleHeld := List.fst_mem_of_mem_zipIdx numberedHeld
  obtain ⟨atom,atomHeld,generated⟩ := List.mem_flatMap.mp particleHeld
  have slot := Charged.atom_particle_slot (atom.1.descriptor,atom.2) numbered.1 generated
  have low := List.le_snd_of_mem_zipIdx atomHeld
  have atomActual := (List.mk_mem_zipIdx_iff_le_and_getElem?_sub.mp atomHeld).2
  have commonActual : (commonAtoms source firstFuel)[atom.2]? = some atom.1 := by
    change (source.atoms.map (fun old => (⟨.prior old,old.descriptor⟩ : Atom cursor)) ++
      freshAtoms)[atom.2]? = some atom.1
    rw [List.getElem?_append_right (by simpa only [List.length_map] using low)]
    simpa only [List.length_map] using atomActual
  obtain ⟨occurrence,kind,payload,origin⟩ := fresh_atom_is_fuel atom.1
    (List.fst_mem_of_mem_zipIdx atomHeld)
  simp only [isChainNode,originAt?,slot,commonActual,Option.map_some,Option.any_some,origin]

theorem fresh_chain_nuclei_empty {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Classical.Source cursor) (x height : ℝ) :
    chainNuclei (commonAtoms source firstFuel) (freshNodes source x height) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro node held
  have outside := fresh_node_outside_chain source x height node (List.mem_filter.mp held).1
  simp only [outside,Bool.false_eq_true,not_false_eq_true]

theorem post_atom_slot_lt {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} (before : Classical.Current cursor priorRaw)
    (step : Classical.NativeStep before priorRaw.time)
    (actual : Classical.fromCursor cursor priorRaw = .responded before step)
    (node : Body.Node) (held : node ∈ step.next.nodes) :
    node.particle.address.slot < before.packet.source.atoms.length := by
  have generated : node.particle ∈ before.packet.source.particles.map Classical.Particle.readout := by
    rw [← (actual_responded_post_source before step actual).1]
    exact List.mem_map_of_mem held
  rw [Classical.source_particle_readout] at generated
  obtain ⟨entry,entryHeld,particleHeld⟩ := List.mem_flatMap.mp generated
  have slot := Charged.atom_particle_slot entry node.particle particleHeld
  have bound := List.snd_lt_of_mem_zipIdx entryHeld
  rw [slot]
  simpa only [Classical.Source.descriptorGraph,List.length_map,Nat.add_zero] using bound

theorem post_chain_role_exact {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} (before : Classical.Current cursor priorRaw)
    (step : Classical.NativeStep before priorRaw.time)
    (actual : Classical.fromCursor cursor priorRaw = .responded before step)
    (node : Body.Node) (held : node ∈ step.next.nodes) :
    isChainNode (commonAtoms before.packet.source firstFuel) node =
      isChainNode (before.packet.source.atoms.map (fun atom => ⟨.prior atom,atom.descriptor⟩)) node := by
  have bound := post_atom_slot_lt before step actual node held
  unfold isChainNode originAt? commonAtoms
  rw [List.getElem?_append_left (by simpa only [List.length_map] using bound)]

theorem base_chain_nuclei_exact {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} (before : Classical.Current cursor priorRaw)
    (step : Classical.NativeStep before priorRaw.time)
    (actual : Classical.fromCursor cursor priorRaw = .responded before step) (x height : ℝ) :
    chainNuclei (commonAtoms before.packet.source firstFuel) (baseNodes before step x height) =
      chainNuclei (before.packet.source.atoms.map (fun atom => ⟨.prior atom,atom.descriptor⟩))
        step.next.nodes := by
  unfold baseNodes chainNuclei nucleusNodes
  rw [List.filter_append,List.filter_append]
  change _ ++ chainNuclei (commonAtoms before.packet.source firstFuel)
    (freshNodes before.packet.source x height) = _
  rw [fresh_chain_nuclei_empty,List.append_nil]
  apply List.filter_congr
  intro node held
  exact post_chain_role_exact before step actual node (List.mem_filter.mp held).1

def firstDirection {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Classical.Source cursor) (node : Body.Node) : Body.Point :=
  if node.particle.address = (firstChannel source).phosphorus then transversePoint 0 2 0
  else if node.particle.address = (firstChannel source).leavingOxygen then transversePoint 0 2 0
  else if node.particle.address = (firstChannel source).attackingOxygen then transversePoint 0 (-4) 0
  else 0

theorem base_coordinate_direction {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} (before : Classical.Current cursor priorRaw)
    (step : Classical.NativeStep before priorRaw.time)
    (actual : Classical.fromCursor cursor priorRaw = .responded before step) (x height : ℝ)
    (node : Body.Node) :
    coordinateDirection (baseNodes before step x height) (firstChannel before.packet.source) node =
      firstDirection before.packet.source node := by
  have found := first_base_nuclei_found before step actual x height
  simp only [coordinateDirection,found.1,found.2.1,found.2.2,firstDirection,
    phosphorusNode,leavingNode,attackingNode]
  split_ifs
  all_goals ext axis; fin_cases axis <;>
    simp [transversePoint,PiLp.smul_apply,PiLp.sub_apply] <;> ring

def firstShiftedPosition {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Classical.Source cursor) (delta : ℝ) (node : Body.Node) : Body.Point :=
  node.row.position+delta • firstDirection source node

def firstShiftedNode {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Classical.Source cursor) (delta : ℝ) (node : Body.Node) : Body.Node :=
  {node with row := {node.row with position := firstShiftedPosition source delta node}}

theorem first_shifted_positions {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Classical.Source cursor) (x height delta : ℝ) :
    firstShiftedPosition source delta (phosphorusNode source x height) =
      transversePoint x (height+2*delta) 0 ∧
    firstShiftedPosition source delta (leavingNode source x height) =
      transversePoint x (height+1+2*delta) 0 ∧
    firstShiftedPosition source delta (attackingNode source x height) =
      transversePoint x (height+2-4*delta) 0 := by
  have different := first_channel_distinct source
  constructor
  · ext axis
    fin_cases axis <;> simp [firstShiftedPosition,firstDirection,phosphorusNode,transversePoint]
    all_goals ring
  constructor
  · ext axis
    fin_cases axis <;> simp [firstShiftedPosition,firstDirection,leavingNode,transversePoint,
      Ne.symm different.1]
    all_goals ring
  · ext axis
    fin_cases axis <;> simp [firstShiftedPosition,firstDirection,attackingNode,transversePoint,
      Ne.symm different.2.1,Ne.symm different.2.2]
    all_goals ring

theorem post_first_direction_zero {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} (before : Classical.Current cursor priorRaw)
    (step : Classical.NativeStep before priorRaw.time)
    (actual : Classical.fromCursor cursor priorRaw = .responded before step)
    (node : Body.Node) (held : node ∈ step.next.nodes) : firstDirection before.packet.source node = 0 := by
  have bound := post_atom_slot_lt before step actual node held
  have absent (offset : Nat) : node.particle.address ≠ .nucleus (before.packet.source.atoms.length+offset) := by
    intro same
    rw [same,Charged.Address.slot] at bound
    omega
  simp only [firstDirection,firstChannel]
  simp only [absent,if_false]

theorem post_first_shift_exact {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} (before : Classical.Current cursor priorRaw)
    (step : Classical.NativeStep before priorRaw.time)
    (actual : Classical.fromCursor cursor priorRaw = .responded before step) (delta : ℝ) :
    step.next.nodes.map (firstShiftedNode before.packet.source delta) = step.next.nodes := by
  calc
    _ = step.next.nodes.map id := by
      apply List.map_congr_left
      intro node held
      simp only [firstShiftedNode,firstShiftedPosition,post_first_direction_zero before step actual node held,
        smul_zero,add_zero,id_eq]
    _ = _ := List.map_id _

private theorem fresh_shifted_y {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Classical.Source cursor) (x height delta : ℝ) (entry : Charged.Particle × Nat) :
    firstShiftedPosition source delta (⟨entry.1,freshRow source x height entry⟩ : Body.Node) (1 : Fin 3) =
      if entry.1.address = (firstChannel source).phosphorus then height+2*delta
      else if entry.1.address = (firstChannel source).leavingOxygen then height+1+2*delta
      else if entry.1.address = (firstChannel source).attackingOxygen then height+2-4*delta
      else height+4+entry.2 := by
  simp only [firstShiftedPosition,firstDirection,freshRow,PiLp.add_apply,PiLp.smul_apply]
  split_ifs <;> simp_all [transversePoint] <;> ring

private theorem fresh_shifted_separated {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Classical.Source cursor) (x height delta : ℝ) (nonnegative : 0 ≤ delta)
    (small : delta ≤ 1/16) (first second : Charged.Particle × Nat)
    (addresses : first.1.address ≠ second.1.address) (ordinals : first.2 ≠ second.2) :
    firstShiftedPosition source delta ⟨first.1,freshRow source x height first⟩ ≠
      firstShiftedPosition source delta ⟨second.1,freshRow source x height second⟩ := by
  intro equal
  have read := congrArg (fun point : Body.Point => point (1 : Fin 3)) equal
  have firstNonnegative : 0 ≤ (first.2 : ℝ) := Nat.cast_nonneg _
  have secondNonnegative : 0 ≤ (second.2 : ℝ) := Nat.cast_nonneg _
  rw [fresh_shifted_y,fresh_shifted_y] at read
  split_ifs at read
  all_goals first
    | apply addresses; calc
        first.1.address = (firstChannel source).phosphorus := by assumption
        _ = second.1.address := by symm; assumption
    | apply addresses; calc
        first.1.address = (firstChannel source).leavingOxygen := by assumption
        _ = second.1.address := by symm; assumption
    | apply addresses; calc
        first.1.address = (firstChannel source).attackingOxygen := by assumption
        _ = second.1.address := by symm; assumption
    | linarith
    | apply ordinals; exact_mod_cast (by linarith : (first.2 : ℝ) = (second.2 : ℝ))

theorem fresh_first_shift_ready {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Classical.Source cursor) (x height delta : ℝ) (nonnegative : 0 ≤ delta)
    (small : delta ≤ 1/16) :
    Body.ready ((freshNodes source x height).map (firstShiftedNode source delta)) := by
  have addresses : ((freshParticles source).zipIdx.map (fun entry => entry.1.address)).Nodup := by
    change ((freshParticles source).zipIdx.map (Charged.Particle.address ∘ Prod.fst)).Nodup
    rw [← List.map_map,List.zipIdx_map_fst]
    exact fresh_particles_unique source
  have ordinals : ((freshParticles source).zipIdx.map Prod.snd).Nodup := by
    rw [List.zipIdx_map_snd]
    exact List.nodup_range' _
  simp only [freshNodes,List.map_map,Function.comp_def]
  apply List.pairwise_map.mpr
  exact ((List.pairwise_map.mp addresses).and (List.pairwise_map.mp ordinals)).imp
    (fun {first second} different => fresh_shifted_separated source x height delta nonnegative small
      first second different.1 different.2)

theorem fresh_first_shift_above {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Classical.Source cursor) (x height delta : ℝ) (nonnegative : 0 ≤ delta)
    (small : delta ≤ 1/16) (node : Body.Node) (held : node ∈ freshNodes source x height) :
    height ≤ firstShiftedPosition source delta node (1 : Fin 3) := by
  obtain ⟨entry,_,same⟩ := List.mem_map.mp held
  subst node
  have ordinalNonnegative : 0 ≤ (entry.2 : ℝ) := Nat.cast_nonneg _
  rw [fresh_shifted_y]
  split_ifs <;> linarith

theorem base_first_shift_ready {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} (before : Classical.Current cursor priorRaw)
    (step : Classical.NativeStep before priorRaw.time)
    (actual : Classical.fromCursor cursor priorRaw = .responded before step) (x height delta : ℝ)
    (above : ∀ node ∈ step.next.nodes, node.row.position (1 : Fin 3) < height)
    (nonnegative : 0 ≤ delta) (small : delta ≤ 1/16) :
    Body.ready ((baseNodes before step x height).map (firstShiftedNode before.packet.source delta)) := by
  rw [baseNodes,List.map_append,post_first_shift_exact before step actual delta]
  apply List.pairwise_append.mpr
  refine ⟨step.nextReady,fresh_first_shift_ready before.packet.source x height delta nonnegative small,?_⟩
  intro old oldHeld fresh freshHeld same
  obtain ⟨prior,priorHeld,identity⟩ := List.mem_map.mp freshHeld
  subst fresh
  have y := congrArg (fun point : Body.Point => point (1 : Fin 3)) same
  have high := fresh_first_shift_above before.packet.source x height delta nonnegative small prior priorHeld
  have low := above old oldHeld
  change old.row.position (1 : Fin 3) = firstShiftedPosition before.packet.source delta prior (1 : Fin 3) at y
  linarith

end
end CPS1PhosphorylExchange
