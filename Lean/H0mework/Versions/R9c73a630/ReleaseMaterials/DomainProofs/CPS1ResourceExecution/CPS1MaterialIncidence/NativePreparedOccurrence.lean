import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.ActualNativeCPContinuation
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.NativeAfterGeometry

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1MaterialIncidence.NativePrepareNextProbe
noncomputable section
open CPS1AtomicDynamics CPS1SameEventFunction CPS1PhosphorylExchange
open CPS1BiologicalUpdate CPS1LiveEditing NativePaidEvent NativeAmmoniaDynamics
open NativeJointRowsProbe NativeAfterGeometry NativeCPContinuationProbe

variable {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
  {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
  {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}
  {source : Common before step raw} {current : NativeCurrent source}
  {paid : SourceGeneratedPaidReturn source current}

/-- The measured joint is a restriction of the full physical mother, including
the actual rows; its complement remains in that same mother. -/
structure NativeMeasurement (whole : NativeJointWhole paid (targetJoint frame))
    (physical : PostState current) where
  geometry : CPS1ElectronicSource.Geometry frame
  actual : CPS1ElectronicSource.Geometry.fromJoint? frame geometry.originJoint = .ok geometry
  selected : List Body.Node
  complement : List Body.Node
  partition : physical.pose.Perm (selected ++ complement)
  rows : geometry.nodes.map Body.Node.row = selected.map Body.Node.row
  ready : Body.ready geometry.nodes
  uniform : geometry.nodes.all (fun node =>
    !CPS1ElectronicSource.isElectron node || node.row.inertia = geometry.electronInertia) = true
  sourceJoint : geometry.originJoint.originBody = (targetJoint frame).originBody ∧
    geometry.originJoint.components = (targetJoint frame).components ∧
    geometry.originJoint.nextOccurrence = (targetJoint frame).nextOccurrence

def before_measurement (whole : NativeJointWhole paid (targetJoint frame)) :
    NativeMeasurement whole paid.physical := by
  refine ⟨whole.measurement.atoms.geometry,whole.measurement.actual,
    whole.measurement.atoms.selectedNativeNodes,whole.measurement.atoms.remainingNativeNodes,
    whole.posePartition,?_,whole.measurement.atoms.nodes_ready,
    whole.measurement.atoms.geometry_uniform,⟨rfl,rfl,rfl⟩⟩
  simp only [JointAtomProjection.geometry,JointAtomProjection.nodes,
    JointAtomProjection.projectedNode,JointAtomProjection.selectedNativeNodes,List.map_map,Function.comp_def]

def after_measurement (whole : NativeJointWhole paid (targetJoint frame)) (event : PaidStep paid.physical) :
    NativeMeasurement whole event.after := by
  refine ⟨afterGeometry whole,geometry_after_actual whole event,selectedAfter whole,remainingAfter whole,
    after_pose_partition whole event,?_,after_nodes_ready whole event,
    geometry_after_uniform whole,⟨rfl,rfl,rfl⟩⟩
  simp only [afterGeometry,afterNodes,afterNode,selectedAfter,
    JointAtomProjection.selectedNativeNodes,afterNativeNode,List.map_map,Function.comp_def]

def refine_measurement {whole : NativeJointWhole paid (targetJoint frame)} {physical : PostState current}
    (measurement : NativeMeasurement whole physical) : NativeMeasurement whole (refineState physical) :=
  ⟨measurement.geometry,measurement.actual,measurement.selected,measurement.complement,
    measurement.partition,measurement.rows,measurement.ready,measurement.uniform,measurement.sourceJoint⟩

structure NativeOccurrence (paid : SourceGeneratedPaidReturn source current)
    (continuation : CPNativeContinuation paid) where
  whole : NativeJointWhole paid (targetJoint frame)
  measurement : NativeMeasurement whole continuation.after

namespace NativeOccurrence
variable {continuation : CPNativeContinuation paid} (occurrence : NativeOccurrence paid continuation)

def physical (_occurrence : NativeOccurrence paid continuation) : PostState current := continuation.after
def charged (_occurrence : NativeOccurrence paid continuation) : ChargedState source current := continuation.chargedAnchor
def remaining (_occurrence : NativeOccurrence paid continuation) : List (CPS1ReactiveField.LiveMaterial frame) := current.remaining

theorem full_account : occurrence.physical.energy + occurrence.physical.reserve =
    paid.physical.energy + paid.physical.reserve := continuation_account continuation

theorem full_electrons : Matrix.trace (occurrence.physical.occupied * occurrence.physical.occupied.conjTranspose) =
    (electronCount source.nodes : ℂ) := continuation_ne continuation

theorem full_inventory : occurrence.charged = paid.parent.products.serial.after ∧
    occurrence.charged.spent = paid.parent.products.serial.after.spent ∧
    occurrence.remaining = current.remaining := ⟨rfl,rfl,rfl⟩

end NativeOccurrence

/-- Preparation exposes the existing full field and its measured joint.  It
does not recapture electrons or change the physical account. -/
structure NativePrepared {continuation : CPNativeContinuation paid}
    (occurrence : NativeOccurrence paid continuation) : Type where
  ready : Body.ready occurrence.measurement.geometry.nodes
  uniform : occurrence.measurement.geometry.nodes.all (fun node =>
    !CPS1ElectronicSource.isElectron node ||
      node.row.inertia = occurrence.measurement.geometry.electronInertia) = true
  gram : occurrence.physical.occupied.conjTranspose * occurrence.physical.occupied = 1
  electronNumber : Matrix.trace (occurrence.physical.occupied * occurrence.physical.occupied.conjTranspose) =
    (electronCount source.nodes : ℂ)

def native_prepared {continuation : CPNativeContinuation paid}
    (occurrence : NativeOccurrence paid continuation) : NativePrepared occurrence :=
  ⟨occurrence.measurement.ready,occurrence.measurement.uniform,occurrence.physical.gram,
    occurrence.full_electrons⟩

def occurrence_of_whole (whole : NativeJointWhole paid (targetJoint frame))
    (continuation : CPNativeContinuation paid) : NativeOccurrence paid continuation := by
  refine ⟨whole,?_⟩
  rcases continuation with ⟨focus,result,actual⟩
  cases result with
  | positive event direction => exact after_measurement whole event
  | wrongDirection event failed => exact after_measurement whole event
  | nondifferentiable failed => exact refine_measurement (before_measurement whole)
  | collision smooth failed => exact refine_measurement (before_measurement whole)
  | energyShortage smooth ready failed => exact refine_measurement (before_measurement whole)

section Source
variable {origin : CPS1ReactiveNuclear.SourceCursor frame} {water : Nat} {material : List RawSupply}
  {path : CPS1Recycling.SplitSite} {events : List CPS1Recycling.RawEvent}
  {feed : List CPS1Recycling.RawMaterial} {physical : PhysicalRaw} {depth : Nat}

def source_native_occurrence
    (whole : WholeRun origin water material path events feed physical depth) (supply : ContinuationRaw)
    (profile : supply.recycling = [] ∧ supply.recycleFeed = [] ∧ supply.physical = noPhysicalSupply)
    (receipt : LocalRepairReceipt (initialBody ⟨frame,origin⟩))
    (repaired : repairWhole whole supply = .repaired receipt)
    {priorRaw : Classical.Raw} {before : Classical.Current receipt.nextBody.current.2 priorRaw}
    {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}
    (source : Common before step raw) {current : NativeCurrent source}
    (paid : SourceGeneratedPaidReturn source current) (continuation : CPNativeContinuation paid) :
    NativeOccurrence paid continuation :=
  occurrence_of_whole (source_joint_whole whole supply profile receipt repaired source paid) continuation

end Source
end
end CPS1MaterialIncidence.NativePrepareNextProbe
