import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.NativeJointAtoms

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1MaterialIncidence.NativeJointRowsProbe
noncomputable section
open CPS1AtomicDynamics CPS1AtomicSource CPS1SameEventFunction CPS1PhosphorylExchange
open NativePaidEvent NativeGatherConsumers

variable {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
  {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
  {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}
  {source : Common before step raw} {current : NativeCurrent source}
  {paid : SourceGeneratedPaidReturn source current} {joint : CPS1EnzymeBath.Joint.State frame}

private def relabelAddress (slot : Nat) : Charged.Address → Charged.Address
  | .nucleus _ => .nucleus slot
  | .electron _ orbital => .electron slot orbital

private def relabelParticle (atom : Graph.Atom) (slot : Nat) (particle : Charged.Particle) : Charged.Particle :=
  {particle with address := relabelAddress slot particle.address,source := atom}

private theorem relabel_particle_held (native target : Graph.Atom) (nativeSlot targetSlot : Nat)
    (element : native.source.element = target.source.element)
    (charge : native.source.charge = target.source.charge)
    (particle : Charged.Particle) (held : particle ∈ Charged.atomParticles (target,targetSlot)) :
    relabelParticle native nativeSlot particle ∈ Charged.atomParticles (native,nativeSlot) := by
  rcases List.mem_cons.mp held with nucleus | electron
  · subst particle
    change (⟨.nucleus nativeSlot,native,(Charged.atomicNumber target.source.element : ℤ)⟩ : Charged.Particle) ∈
      Charged.atomParticles (native,nativeSlot)
    rw [← element]
    exact List.mem_cons_self
  · obtain ⟨orbital,bound,actual⟩ := List.mem_map.mp electron
    subst particle
    have sameElectrons : Charged.electrons target.source = Charged.electrons native.source := by
      unfold Charged.electrons
      rw [element,charge]
    apply List.mem_cons_of_mem
    exact List.mem_map.mpr ⟨orbital,sameElectrons ▸ bound,rfl⟩

namespace JointAtomProjection
variable (projection : JointAtomProjection paid joint)

private theorem particle_slot_lt (particle : Charged.Particle)
    (held : particle ∈ CPS1EnzymeBath.Joint.particles frame joint) :
    particle.address.slot < (CPS1EnzymeBath.Joint.atoms frame joint).length := by
  obtain ⟨row,indexed,member⟩ := List.mem_flatMap.mp held
  rw [Charged.atom_particle_slot row particle member]
  simpa only [CPS1EnzymeBath.Joint.descriptorGraph,List.length_map,Nat.add_zero] using
    List.snd_lt_of_mem_zipIdx indexed

abbrev TargetParticle := {particle : Charged.Particle // particle ∈ CPS1EnzymeBath.Joint.particles frame joint}

def atomSlot (particle : TargetParticle (joint := joint)) :
    Fin (CPS1EnzymeBath.Joint.atoms frame joint).length :=
  ⟨particle.val.address.slot,particle_slot_lt particle.val particle.property⟩

private theorem particle_at_atom (particle : TargetParticle (joint := joint)) :
    particle.val ∈ Charged.atomParticles
      (((CPS1EnzymeBath.Joint.atoms frame joint).get (atomSlot particle)).descriptor,(atomSlot particle).val) := by
  obtain ⟨row,indexed,member⟩ := List.mem_flatMap.mp particle.property
  have slot := Charged.atom_particle_slot row particle.val member
  have atom := List.mk_mem_zipIdx_iff_getElem?.mp indexed
  have descriptor : ((CPS1EnzymeBath.Joint.atoms frame joint).get (atomSlot particle)).descriptor = row.1 := by
    change ((CPS1EnzymeBath.Joint.atoms frame joint).map CPS1EnzymeBath.Joint.Atom.descriptor)[row.2]? = some row.1 at atom
    rw [← slot,List.getElem?_map] at atom
    have atSlot : (CPS1EnzymeBath.Joint.atoms frame joint)[(atomSlot particle).val]? =
        some ((CPS1EnzymeBath.Joint.atoms frame joint).get (atomSlot particle)) := by
      simpa only [List.get_eq_getElem] using List.getElem?_eq_getElem (atomSlot particle).isLt
    change ((CPS1EnzymeBath.Joint.atoms frame joint)[(atomSlot particle).val]?).map
      CPS1EnzymeBath.Joint.Atom.descriptor = some row.1 at atom
    rw [atSlot] at atom
    exact Option.some.inj atom
  have actual : row = (((CPS1EnzymeBath.Joint.atoms frame joint).get (atomSlot particle)).descriptor,
      (atomSlot particle).val) := by
    apply Prod.ext
    · exact descriptor.symm
    · exact slot.symm
  exact actual ▸ member

def nativeParticle (particle : TargetParticle (joint := joint)) : Charged.Particle :=
  relabelParticle (source.atoms.get (projection.nativeSlot (atomSlot particle))).descriptor
    (projection.nativeSlot (atomSlot particle)).val particle.val

private theorem native_particle_held (particle : TargetParticle (joint := joint)) :
    projection.nativeParticle particle ∈ commonParticles before.packet.source raw.fuel := by
  have indexed : (source.atoms.get (projection.nativeSlot (atomSlot particle)),
      (projection.nativeSlot (atomSlot particle)).val) ∈ source.atoms.zipIdx := by
    apply List.mk_mem_zipIdx_iff_getElem?.mpr
    simpa only [List.get_eq_getElem] using List.getElem?_eq_getElem (projection.nativeSlot (atomSlot particle)).isLt
  have table : commonParticles before.packet.source raw.fuel =
      source.atoms.zipIdx.flatMap (fun entry => Charged.atomParticles (entry.1.descriptor,entry.2)) := by
    rw [source.atomSource]
    rfl
  rw [table]
  apply List.mem_flatMap.mpr
  refine ⟨_,indexed,?_⟩
  exact relabel_particle_held _ _ _ _ (projection.element (atomSlot particle))
    (projection.charge (atomSlot particle)) _ (particle_at_atom particle)

private theorem native_node_found (particle : TargetParticle (joint := joint)) :
    (paid.physical.pose.find? (fun node => decide (node.particle = projection.nativeParticle particle))).isSome := by
  have held := projection.native_particle_held particle
  have whole := paid.physical.particles.trans (current_particles_source source current)
  rw [← whole] at held
  obtain ⟨node,member,actual⟩ := List.mem_map.mp held
  exact List.find?_isSome.mpr ⟨node,member,by simp only [actual,decide_true]⟩

def nativeNode (particle : TargetParticle (joint := joint)) : Body.Node :=
  (paid.physical.pose.find? (fun node => decide (node.particle = projection.nativeParticle particle))).get
    (projection.native_node_found particle)

theorem native_node_actual (particle : TargetParticle (joint := joint)) :
    projection.nativeNode particle ∈ paid.physical.pose ∧
      (projection.nativeNode particle).particle = projection.nativeParticle particle := by
  have found : paid.physical.pose.find? (fun node => decide (node.particle = projection.nativeParticle particle)) =
      some (projection.nativeNode particle) := (Option.some_get _).symm
  exact ⟨List.mem_of_find?_eq_some found,of_decide_eq_true
    (List.find?_some (p := fun node : Body.Node => decide (node.particle = projection.nativeParticle particle)) found)⟩

private theorem relabel_address_slot (slot : Nat) (address : Charged.Address) :
    (relabelAddress slot address).slot = slot := by cases address <;> rfl

private theorem relabel_address_inj (slot : Nat) (first second : Charged.Address)
    (sameSlot : first.slot = second.slot)
    (same : relabelAddress slot first = relabelAddress slot second) : first = second := by
  cases first with
  | nucleus first =>
    cases second with
    | nucleus second => exact congrArg Charged.Address.nucleus sameSlot
    | electron second orbital => cases same
  | electron first orbital =>
    cases second with
    | nucleus second => cases same
    | electron second other =>
      exact congrArg₂ Charged.Address.electron sameSlot (Charged.Address.electron.inj same).2

theorem native_address_injective (first second : TargetParticle (joint := joint))
    (same : (projection.nativeParticle first).address = (projection.nativeParticle second).address) :
    first.val.address = second.val.address := by
  have slots := congrArg Charged.Address.slot same
  simp only [nativeParticle,relabelParticle,relabel_address_slot] at slots
  have indices := projection.injective (Fin.ext slots)
  have originalSlots : first.val.address.slot = second.val.address.slot := congrArg Fin.val indices
  change relabelAddress (projection.nativeSlot (atomSlot first)).val first.val.address =
    relabelAddress (projection.nativeSlot (atomSlot second)).val second.val.address at same
  rw [slots] at same
  exact relabel_address_inj _ _ _ originalSlots same

theorem native_node_injective : Function.Injective projection.nativeNode := by
  intro first second same
  apply Subtype.ext
  apply List.inj_on_of_nodup_map (Charged.particles_unique (CPS1EnzymeBath.Joint.descriptorGraph frame joint))
    first.property second.property
  apply projection.native_address_injective
  have particles := congrArg Body.Node.particle same
  rw [(projection.native_node_actual first).2,(projection.native_node_actual second).2] at particles
  exact congrArg Charged.Particle.address particles

def projectedNode (particle : TargetParticle (joint := joint)) : Body.Node :=
  ⟨particle.val,(projection.nativeNode particle).row⟩

def nodes : List Body.Node :=
  (CPS1EnzymeBath.Joint.particles frame joint).attach.map projection.projectedNode

def rows : List (Charged.Address × Body.Row) :=
  projection.nodes.map (fun node => (node.particle.address,node.row))

theorem nodes_particles : projection.nodes.map Body.Node.particle = CPS1EnzymeBath.Joint.particles frame joint := by
  simp only [nodes,List.map_map,projectedNode,Function.comp_def]
  exact List.attach_map_subtype_val _

theorem nodes_addresses_unique : (projection.nodes.map (fun node => node.particle.address)).Nodup := by
  have actual := congrArg (List.map Charged.Particle.address) projection.nodes_particles
  simp only [List.map_map,Function.comp_def] at actual
  rw [actual]
  exact Charged.particles_unique _

theorem nodes_inertia (node : Body.Node) (held : node ∈ projection.nodes) : 0 < node.row.inertia := by
  obtain ⟨particle,_member,actual⟩ := List.mem_map.mp held
  subst node
  change 0 < (projection.nativeNode particle).row.inertia
  exact paid.physical.inertia _ (projection.native_node_actual particle).1

theorem nodes_ready : Body.ready projection.nodes := by
  let : Std.Symm (fun first second : Body.Node => first.row.position ≠ second.row.position) :=
    ⟨fun _ _ different => different.symm⟩
  have unique : (CPS1EnzymeBath.Joint.particles frame joint).attach.Nodup :=
    (List.Nodup.of_map _ (Charged.particles_unique (CPS1EnzymeBath.Joint.descriptorGraph frame joint))).attach
  apply List.pairwise_map.mpr
  change (CPS1EnzymeBath.Joint.particles frame joint).attach.Pairwise
    (fun first second => (projection.nativeNode first).row.position ≠ (projection.nativeNode second).row.position)
  exact unique.imp (fun {first second} different =>
    paid.physical.ready.forall (projection.native_node_actual first).1 (projection.native_node_actual second).1
      (fun same => different (projection.native_node_injective same)))

theorem nodes_uniform (node : Body.Node) (held : node ∈ projection.nodes) :
    match node.particle.address with
    | .nucleus _ => True
    | .electron .. => node.row.inertia = source.electronInertia := by
  obtain ⟨particle,_member,actual⟩ := List.mem_map.mp held
  subst node
  have uniform := paid_uniform_electrons paid _ (projection.native_node_actual particle).1
  rw [(projection.native_node_actual particle).2] at uniform
  cases address : particle.val.address with
  | nucleus slot => simp only [projectedNode,address]
  | electron slot orbital =>
    simpa only [projectedNode,nativeParticle,relabelParticle,relabelAddress,address] using uniform

theorem gather_actual :
    Body.gather (CPS1EnzymeBath.Joint.particles frame joint) projection.rows = .ok projection.nodes :=
  Body.gather_exact _ _ projection.nodes_particles _
    (Body.row_at_source _ projection.nodes_addresses_unique) projection.nodes_inertia

def selectedNativeNodes : List Body.Node :=
  (CPS1EnzymeBath.Joint.particles frame joint).attach.map projection.nativeNode

def remainingNativeNodes : List Body.Node :=
  eraseParents paid.physical.pose projection.selectedNativeNodes

theorem native_pose_partition :
    paid.physical.pose.Perm (projection.selectedNativeNodes ++ projection.remainingNativeNodes) := by
  have unique : (CPS1EnzymeBath.Joint.particles frame joint).attach.Nodup :=
    (List.Nodup.of_map _ (Charged.particles_unique (CPS1EnzymeBath.Joint.descriptorGraph frame joint))).attach
  apply select_parents_perm _ _ (unique.map projection.native_node_injective)
  intro node held
  obtain ⟨particle,_member,actual⟩ := List.mem_map.mp held
  subst node
  exact (projection.native_node_actual particle).1

end JointAtomProjection
end
end CPS1MaterialIncidence.NativeJointRowsProbe
