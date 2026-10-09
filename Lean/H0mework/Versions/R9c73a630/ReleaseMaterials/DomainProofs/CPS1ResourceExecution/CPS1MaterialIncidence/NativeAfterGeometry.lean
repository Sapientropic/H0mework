import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.NativeJointWhole

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1MaterialIncidence.NativeAfterGeometry
noncomputable section
open CPS1AtomicDynamics CPS1AtomicSource CPS1SameEventFunction CPS1PhosphorylExchange
open NativePaidEvent NativeAmmoniaDynamics NativeJointRowsProbe

variable {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
  {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
  {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}
  {source : Common before step raw} {current : NativeCurrent source}
  {paid : SourceGeneratedPaidReturn source current} {joint : CPS1EnzymeBath.Joint.State frame}

private theorem full_kick_particle (state : PostState current) (node : Body.Node) :
    (fullKick state node).particle = node.particle := by
  cases address : node.particle.address <;> simp only [fullKick,address]

private theorem full_kick_inertia (state : PostState current) (node : Body.Node) :
    (fullKick state node).row.inertia = node.row.inertia := by
  cases address : node.particle.address <;> simp only [fullKick,address]

variable (whole : NativeJointWhole paid joint)

def afterNativeNode (particle : JointAtomProjection.TargetParticle (joint := joint)) : Body.Node :=
  fullKick paid.physical (whole.measurement.atoms.nativeNode particle)

def afterNode (particle : JointAtomProjection.TargetParticle (joint := joint)) : Body.Node :=
  ⟨particle.val,(afterNativeNode whole particle).row⟩

def afterNodes : List Body.Node :=
  (CPS1EnzymeBath.Joint.particles frame joint).attach.map (afterNode whole)

def afterRows : List (Charged.Address × Body.Row) :=
  (afterNodes whole).map (fun node => (node.particle.address,node.row))

def afterJoint : CPS1EnzymeBath.Joint.State frame :=
  {whole.measurement.atoms.measuredJoint with rows := afterRows whole}

def afterGeometry : CPS1ElectronicSource.Geometry frame := ⟨afterJoint whole,afterNodes whole⟩

def selectedAfter : List Body.Node :=
  whole.measurement.atoms.selectedNativeNodes.map (fullKick paid.physical)

def remainingAfter : List Body.Node :=
  whole.measurement.atoms.remainingNativeNodes.map (fullKick paid.physical)

theorem after_joint_source : (afterJoint whole).originBody = whole.measurement.atoms.measuredJoint.originBody ∧
    (afterJoint whole).components = whole.measurement.atoms.measuredJoint.components ∧
    (afterJoint whole).nextOccurrence = whole.measurement.atoms.measuredJoint.nextOccurrence ∧
    (afterJoint whole).reserve = whole.measurement.atoms.measuredJoint.reserve ∧
    (afterJoint whole).rows = afterRows whole := ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem after_native_node_actual (event : PaidStep paid.physical)
    (particle : JointAtomProjection.TargetParticle (joint := joint)) :
    afterNativeNode whole particle ∈ event.after.pose ∧
      (afterNativeNode whole particle).particle = whole.measurement.atoms.nativeParticle particle := by
  refine ⟨?_,(full_kick_particle _ _).trans (whole.measurement.atoms.native_node_actual particle).2⟩
  change fullKick paid.physical (whole.measurement.atoms.nativeNode particle) ∈
    paid.physical.pose.map (fullKick paid.physical)
  exact List.mem_map_of_mem (whole.measurement.atoms.native_node_actual particle).1

theorem after_native_node_injective : Function.Injective (afterNativeNode whole) := by
  intro first second same
  apply Subtype.ext
  apply List.inj_on_of_nodup_map (Charged.particles_unique (CPS1EnzymeBath.Joint.descriptorGraph frame joint))
    first.property second.property
  apply whole.measurement.atoms.native_address_injective
  have actual := congrArg (fun node : Body.Node => node.particle.address) same
  simp only [afterNativeNode,full_kick_particle] at actual
  rw [(whole.measurement.atoms.native_node_actual first).2,
    (whole.measurement.atoms.native_node_actual second).2] at actual
  exact actual

theorem after_nodes_particles : (afterNodes whole).map Body.Node.particle = CPS1EnzymeBath.Joint.particles frame joint := by
  simp only [afterNodes,List.map_map,afterNode,Function.comp_def]
  exact List.attach_map_subtype_val _

theorem after_nodes_addresses_unique : ((afterNodes whole).map (fun node => node.particle.address)).Nodup := by
  have actual := congrArg (List.map Charged.Particle.address) (after_nodes_particles whole)
  simp only [List.map_map,Function.comp_def] at actual
  rw [actual]
  exact Charged.particles_unique _

theorem after_nodes_inertia (event : PaidStep paid.physical) (node : Body.Node)
    (held : node ∈ afterNodes whole) : 0 < node.row.inertia := by
  obtain ⟨particle,_member,actual⟩ := List.mem_map.mp held
  subst node
  change 0 < (afterNativeNode whole particle).row.inertia
  exact event.after.inertia _ (after_native_node_actual whole event particle).1

theorem after_nodes_ready (event : PaidStep paid.physical) : Body.ready (afterNodes whole) := by
  let : Std.Symm (fun first second : Body.Node => first.row.position ≠ second.row.position) :=
    ⟨fun _ _ different => different.symm⟩
  have unique : (CPS1EnzymeBath.Joint.particles frame joint).attach.Nodup :=
    (List.Nodup.of_map _ (Charged.particles_unique (CPS1EnzymeBath.Joint.descriptorGraph frame joint))).attach
  apply List.pairwise_map.mpr
  change (CPS1EnzymeBath.Joint.particles frame joint).attach.Pairwise
    (fun first second => (afterNativeNode whole first).row.position ≠ (afterNativeNode whole second).row.position)
  exact unique.imp (fun {first second} different =>
    event.after.ready.forall (after_native_node_actual whole event first).1 (after_native_node_actual whole event second).1
      (fun same => different (after_native_node_injective whole same)))

theorem after_nodes_uniform (node : Body.Node) (held : node ∈ afterNodes whole) :
    match node.particle.address with
    | .nucleus _ => True
    | .electron .. => node.row.inertia = source.electronInertia := by
  obtain ⟨particle,_member,actual⟩ := List.mem_map.mp held
  subst node
  have oldHeld : whole.measurement.atoms.projectedNode particle ∈ whole.measurement.atoms.nodes :=
    List.mem_map.mpr ⟨particle,List.mem_attach _ _,rfl⟩
  have uniform := whole.measurement.atoms.nodes_uniform _ oldHeld
  cases address : particle.val.address with
  | nucleus slot => simp only [afterNode,address]
  | electron slot orbital =>
    simp only [afterNode,address]
    change (fullKick paid.physical (whole.measurement.atoms.nativeNode particle)).row.inertia = source.electronInertia
    rw [full_kick_inertia]
    simpa only [JointAtomProjection.projectedNode,address] using uniform

theorem gather_after (event : PaidStep paid.physical) :
    Body.gather (CPS1EnzymeBath.Joint.particles frame joint) (afterRows whole) = .ok (afterNodes whole) :=
  Body.gather_exact _ _ (after_nodes_particles whole) _
    (Body.row_at_source _ (after_nodes_addresses_unique whole)) (after_nodes_inertia whole event)

theorem geometry_after_uniform : (afterNodes whole).all (fun node =>
    !CPS1ElectronicSource.isElectron node || node.row.inertia = (afterGeometry whole).electronInertia) = true := by
  apply List.all_eq_true.mpr
  intro node member
  cases address : node.particle.address with
  | nucleus slot => simp only [CPS1ElectronicSource.isElectron,CPS1ElectronicSource.isNucleus,address,Bool.not_true,
      Bool.not_false,Bool.true_or]
  | electron slot orbital =>
    have mass := after_nodes_uniform whole node member
    rw [address] at mass
    have electron : ((afterNodes whole).find? CPS1ElectronicSource.isElectron).isSome :=
      List.find?_isSome.mpr ⟨node,member,by simp only [CPS1ElectronicSource.isElectron,CPS1ElectronicSource.isNucleus,
        address,Bool.not_false]⟩
    cases found : (afterNodes whole).find? CPS1ElectronicSource.isElectron with
    | none => rw [found] at electron; cases electron
    | some selected =>
      have selectedMass := after_nodes_uniform whole selected (List.mem_of_find?_eq_some found)
      have selectedElectron := List.find?_some found
      cases selectedAddress : selected.particle.address with
      | nucleus selectedSlot =>
        simp only [CPS1ElectronicSource.isElectron,CPS1ElectronicSource.isNucleus,selectedAddress,Bool.not_true,
          Bool.false_eq_true] at selectedElectron
      | electron selectedSlot selectedOrbital =>
        rw [selectedAddress] at selectedMass
        have inertia : (afterGeometry whole).electronInertia = source.electronInertia := by
          change (((afterNodes whole).find? CPS1ElectronicSource.isElectron).map (fun item => item.row.inertia)).getD 1 = _
          rw [found]
          exact selectedMass
        simp only [CPS1ElectronicSource.isElectron,CPS1ElectronicSource.isNucleus,address,Bool.not_false,
          Bool.not_true,Bool.false_or,inertia,mass,decide_true]

theorem geometry_after_actual (event : PaidStep paid.physical) :
    CPS1ElectronicSource.Geometry.fromJoint? frame (afterJoint whole) = .ok (afterGeometry whole) := by
  classical
  have particles : CPS1EnzymeBath.Joint.particles frame (afterJoint whole) =
      CPS1EnzymeBath.Joint.particles frame joint := rfl
  unfold CPS1ElectronicSource.Geometry.fromJoint?
  rw [particles]
  change ((match Body.gather (CPS1EnzymeBath.Joint.particles frame joint) (afterRows whole) with
    | .error failure => .error (.body failure)
    | .ok nodes =>
      let geometry : CPS1ElectronicSource.Geometry frame := ⟨afterJoint whole,nodes⟩
      if ¬ Body.ready nodes then .error (.body .collision)
      else if nodes.all (fun node => !CPS1ElectronicSource.isElectron node || node.row.inertia = geometry.electronInertia)
        then .ok geometry else .error .unequalElectronInertia) :
      Except CPS1ElectronicSource.Failure (CPS1ElectronicSource.Geometry frame)) = _
  rw [gather_after whole event]
  simp only [if_neg (not_not_intro (after_nodes_ready whole event))]
  change ((if (afterNodes whole).all (fun node => !CPS1ElectronicSource.isElectron node ||
    node.row.inertia = (afterGeometry whole).electronInertia) then .ok (afterGeometry whole) else .error .unequalElectronInertia) :
      Except CPS1ElectronicSource.Failure (CPS1ElectronicSource.Geometry frame)) = _
  rw [geometry_after_uniform whole]
  rfl

theorem after_pose_partition (event : PaidStep paid.physical) :
    event.after.pose.Perm (selectedAfter whole ++ remainingAfter whole) := by
  change (paid.physical.pose.map (fullKick paid.physical)).Perm
    (whole.measurement.atoms.selectedNativeNodes.map (fullKick paid.physical) ++
      whole.measurement.atoms.remainingNativeNodes.map (fullKick paid.physical))
  simpa only [List.map_append] using whole.posePartition.map (fullKick paid.physical)

structure AfterGeometry (whole : NativeJointWhole paid joint) (event : PaidStep paid.physical) where
  physical : PostState current
  physicalActual : physical = event.after
  geometry : CPS1ElectronicSource.Geometry frame
  geometryActual : CPS1ElectronicSource.Geometry.fromJoint? frame (afterJoint whole) = .ok geometry
  rowsActual : geometry.nodes = afterNodes whole
  atomPartition : source.atoms.Perm (whole.measurement.atoms.nativeAtoms ++ whole.measurement.atoms.complementAtoms)
  posePartition : physical.pose.Perm (selectedAfter whole ++ remainingAfter whole)
  fullCIncrement : physical.rawC = paid.physical.rawC + sourceCoefficient current * (physical.occupied - paid.physical.occupied)
  electronNumber : Matrix.trace (physical.occupied * physical.occupied.conjTranspose) = (electronCount source.nodes : ℂ)
  energyAccount : physical.energy + physical.reserve = paid.physical.energy + paid.physical.reserve

/-- This transports an already generated paid event; it does not select its physical branch. -/
def transport_after_geometry (whole : NativeJointWhole paid joint) (event : PaidStep paid.physical) :
    AfterGeometry whole event :=
  ⟨event.after,rfl,afterGeometry whole,geometry_after_actual whole event,rfl,whole.atomPartition,
    after_pose_partition whole event,paid_fullC_increment event,post_electron_number event.after,paid_account event⟩

end
end CPS1MaterialIncidence.NativeAfterGeometry
