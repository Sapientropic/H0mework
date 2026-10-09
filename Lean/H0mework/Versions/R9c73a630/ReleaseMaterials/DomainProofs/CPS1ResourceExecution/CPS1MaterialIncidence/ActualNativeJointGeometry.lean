import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.NativeJointRows

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1MaterialIncidence.NativeJointRowsProbe
noncomputable section
open CPS1AtomicDynamics CPS1AtomicSource CPS1SameEventFunction CPS1PhosphorylExchange
open CPS1BiologicalUpdate CPS1LiveEditing NativePaidEvent

variable {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
  {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
  {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}
  {source : Common before step raw} {current : NativeCurrent source}
  {paid : SourceGeneratedPaidReturn source current} {joint : CPS1EnzymeBath.Joint.State frame}

namespace JointAtomProjection
variable (projection : JointAtomProjection paid joint)

def measuredJoint : CPS1EnzymeBath.Joint.State frame :=
  {joint with rows := projection.rows}

def geometry : CPS1ElectronicSource.Geometry frame := ⟨projection.measuredJoint,projection.nodes⟩

theorem measured_joint_source : projection.measuredJoint.originBody = joint.originBody ∧
    projection.measuredJoint.components = joint.components ∧
    projection.measuredJoint.nextOccurrence = joint.nextOccurrence ∧
    projection.measuredJoint.reserve = joint.reserve ∧
    projection.measuredJoint.rows = projection.rows := ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem geometry_uniform : projection.nodes.all (fun node =>
    !CPS1ElectronicSource.isElectron node || node.row.inertia = projection.geometry.electronInertia) = true := by
  apply List.all_eq_true.mpr
  intro node member
  cases address : node.particle.address with
  | nucleus slot => simp only [CPS1ElectronicSource.isElectron,CPS1ElectronicSource.isNucleus,address,Bool.not_true,
      Bool.not_false,Bool.true_or]
  | electron slot orbital =>
    have mass := projection.nodes_uniform node member
    rw [address] at mass
    have electron : (projection.nodes.find? CPS1ElectronicSource.isElectron).isSome :=
      List.find?_isSome.mpr ⟨node,member,by simp only [CPS1ElectronicSource.isElectron,CPS1ElectronicSource.isNucleus,
        address,Bool.not_false]⟩
    cases found : projection.nodes.find? CPS1ElectronicSource.isElectron with
    | none => rw [found] at electron; cases electron
    | some selected =>
      have selectedMass := projection.nodes_uniform selected (List.mem_of_find?_eq_some found)
      have selectedElectron := List.find?_some found
      cases selectedAddress : selected.particle.address with
      | nucleus selectedSlot =>
        simp only [CPS1ElectronicSource.isElectron,CPS1ElectronicSource.isNucleus,selectedAddress,Bool.not_true,
          Bool.false_eq_true] at selectedElectron
      | electron selectedSlot selectedOrbital =>
        rw [selectedAddress] at selectedMass
        have inertia : projection.geometry.electronInertia = source.electronInertia := by
          change ((projection.nodes.find? CPS1ElectronicSource.isElectron).map (fun item => item.row.inertia)).getD 1 = _
          rw [found]
          exact selectedMass
        simp only [CPS1ElectronicSource.isElectron,CPS1ElectronicSource.isNucleus,address,Bool.not_false,
          Bool.not_true,Bool.false_or,inertia,mass,decide_true]

theorem geometry_actual : CPS1ElectronicSource.Geometry.fromJoint? frame projection.measuredJoint = .ok projection.geometry := by
  classical
  have particles : CPS1EnzymeBath.Joint.particles frame projection.measuredJoint =
      CPS1EnzymeBath.Joint.particles frame joint := rfl
  unfold CPS1ElectronicSource.Geometry.fromJoint?
  rw [particles]
  change ((match Body.gather (CPS1EnzymeBath.Joint.particles frame joint) projection.rows with
    | .error failure => .error (.body failure)
    | .ok nodes =>
      let geometry : CPS1ElectronicSource.Geometry frame := ⟨projection.measuredJoint,nodes⟩
      if ¬ Body.ready nodes then .error (.body .collision)
      else if nodes.all (fun node => !CPS1ElectronicSource.isElectron node || node.row.inertia = geometry.electronInertia)
        then .ok geometry else .error .unequalElectronInertia) :
      Except CPS1ElectronicSource.Failure (CPS1ElectronicSource.Geometry frame)) = _
  rw [projection.gather_actual]
  simp only [if_neg (not_not_intro projection.nodes_ready)]
  change ((if projection.nodes.all (fun node => !CPS1ElectronicSource.isElectron node ||
    node.row.inertia = projection.geometry.electronInertia) then .ok projection.geometry else .error .unequalElectronInertia) :
      Except CPS1ElectronicSource.Failure (CPS1ElectronicSource.Geometry frame)) = _
  rw [projection.geometry_uniform]
  rfl

end JointAtomProjection

structure NativeJointGeometry (paid : SourceGeneratedPaidReturn source current)
    (joint : CPS1EnzymeBath.Joint.State frame) where
  atoms : JointAtomProjection paid joint
  actual : CPS1ElectronicSource.Geometry.fromJoint? frame atoms.measuredJoint = .ok atoms.geometry

section Actual
variable {origin : CPS1ReactiveNuclear.SourceCursor frame} {water : Nat} {material : List RawSupply}
  {path : CPS1Recycling.SplitSite} {events : List CPS1Recycling.RawEvent}
  {feed : List CPS1Recycling.RawMaterial} {physical : PhysicalRaw} {depth : Nat}

def source_joint_geometry
    (whole : WholeRun origin water material path events feed physical depth) (supply : ContinuationRaw)
    (profile : supply.recycling = [] ∧ supply.recycleFeed = [] ∧ supply.physical = noPhysicalSupply)
    (receipt : LocalRepairReceipt (initialBody ⟨frame,origin⟩))
    (repaired : repairWhole whole supply = .repaired receipt)
    {priorRaw : Classical.Raw} {before : Classical.Current receipt.nextBody.current.2 priorRaw}
    {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}
    (source : Common before step raw) {current : NativeCurrent source}
    (paid : SourceGeneratedPaidReturn source current) :
    NativeJointGeometry paid (targetJoint receipt.nextBody.current.1) :=
  ⟨source_atom_projection whole supply profile receipt repaired source paid,
    JointAtomProjection.geometry_actual (source_atom_projection whole supply profile receipt repaired source paid)⟩

end Actual

end
end CPS1MaterialIncidence.NativeJointRowsProbe
