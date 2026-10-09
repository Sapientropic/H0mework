import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.ActualNativeJointGeometry

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

def nativeAtoms : List (Atom cursor) :=
  (List.finRange (CPS1EnzymeBath.Joint.atoms frame joint).length).map
    (fun i => source.atoms.get (projection.nativeSlot i))

def complementAtoms : List (Atom cursor) := eraseParents source.atoms projection.nativeAtoms

theorem native_atoms_unique : projection.nativeAtoms.Nodup := by
  have sourceUnique : source.atoms.Nodup := List.Nodup.of_map Atom.origin (source_vertices_unique source)
  exact List.Nodup.map (sourceUnique.injective_get.comp projection.injective) (List.nodup_finRange _)

theorem native_atom_held (atom : Atom cursor) (held : atom ∈ projection.nativeAtoms) : atom ∈ source.atoms := by
  obtain ⟨i,_member,actual⟩ := List.mem_map.mp held
  subst atom
  exact List.get_mem _ _

theorem atom_partition : source.atoms.Perm (projection.nativeAtoms ++ projection.complementAtoms) :=
  select_parents_perm _ _ projection.native_atoms_unique projection.native_atom_held

theorem complement_atoms_disjoint : ∀ atom ∈ projection.nativeAtoms, atom ∉ projection.complementAtoms := by
  have unique : (projection.nativeAtoms ++ projection.complementAtoms).Nodup :=
    (projection.atom_partition.nodup_iff).mp (List.Nodup.of_map Atom.origin (source_vertices_unique source))
  intro atom member complement
  exact (List.nodup_append.mp unique).2.2 atom member atom complement rfl

end JointAtomProjection

structure NativeJointWhole (paid : SourceGeneratedPaidReturn source current)
    (joint : CPS1EnzymeBath.Joint.State frame) where
  measurement : NativeJointGeometry paid joint
  atomPartition : source.atoms.Perm (measurement.atoms.nativeAtoms ++ measurement.atoms.complementAtoms)
  posePartition : paid.physical.pose.Perm (measurement.atoms.selectedNativeNodes ++ measurement.atoms.remainingNativeNodes)

section Actual
variable {origin : CPS1ReactiveNuclear.SourceCursor frame} {water : Nat} {material : List RawSupply}
  {path : CPS1Recycling.SplitSite} {events : List CPS1Recycling.RawEvent}
  {feed : List CPS1Recycling.RawMaterial} {physical : PhysicalRaw} {depth : Nat}

def source_joint_whole
    (whole : WholeRun origin water material path events feed physical depth) (supply : ContinuationRaw)
    (profile : supply.recycling = [] ∧ supply.recycleFeed = [] ∧ supply.physical = noPhysicalSupply)
    (receipt : LocalRepairReceipt (initialBody ⟨frame,origin⟩))
    (repaired : repairWhole whole supply = .repaired receipt)
    {priorRaw : Classical.Raw} {before : Classical.Current receipt.nextBody.current.2 priorRaw}
    {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}
    (source : Common before step raw) {current : NativeCurrent source}
    (paid : SourceGeneratedPaidReturn source current) : NativeJointWhole paid (targetJoint receipt.nextBody.current.1) :=
  let measurement := source_joint_geometry whole supply profile receipt repaired source paid
  ⟨measurement,measurement.atoms.atom_partition,measurement.atoms.native_pose_partition⟩

end Actual
end
end CPS1MaterialIncidence.NativeJointRowsProbe
