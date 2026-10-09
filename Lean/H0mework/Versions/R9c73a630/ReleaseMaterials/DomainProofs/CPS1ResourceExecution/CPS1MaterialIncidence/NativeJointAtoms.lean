import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.ActualRootPaidDisposition
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.NativeGatherSource
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.NativeCPProjection

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1MaterialIncidence.NativeJointRowsProbe
noncomputable section
open CPS1AtomicDynamics CPS1AtomicSource CPS1SameEventFunction CPS1PhosphorylExchange
open CPS1BiologicalUpdate CPS1LiveEditing NativePaidEvent NativePaidPositive NativeGatherConsumers

variable {frame : CPS1Recycling.Frame}

def targetJoint (frame : CPS1Recycling.Frame) : CPS1EnzymeBath.Joint.State frame :=
  CPS1EnzymeBath.Joint.attach frame (sourceJoint frame) .carbamoylPhosphate

def chainGraph (frame : CPS1Recycling.Frame) : Graph.Molecule :=
  Body.graph frame (sourceJoint frame).originBody

theorem target_atoms (frame : CPS1Recycling.Frame) :
    CPS1EnzymeBath.Joint.atoms frame (targetJoint frame) =
      (chainGraph frame).atoms.map (fun atom => (⟨.enzyme atom,atom⟩ : CPS1EnzymeBath.Joint.Atom)) ++
      CPS1EnzymeBath.Primary.carbamoylPhosphate.atoms.map
        (CPS1EnzymeBath.Joint.bathAtom ⟨0,.carbamoylPhosphate⟩) := rfl

theorem target_length (frame : CPS1Recycling.Frame) :
    (CPS1EnzymeBath.Joint.atoms frame (targetJoint frame)).length = (chainGraph frame).atoms.length + 10 := by
  rw [target_atoms,List.length_append,List.length_map,List.length_map]
  rfl

def targetCPOrdinal (i : Fin (CPS1EnzymeBath.Joint.atoms frame (targetJoint frame)).length)
    (outside : ¬ i.val < (chainGraph frame).atoms.length) : Fin 10 :=
  ⟨i.val - (chainGraph frame).atoms.length,by
    have bound : i.val < (chainGraph frame).atoms.length + 10 := by
      simpa only [target_length] using i.isLt
    omega⟩

theorem target_chain_at (i : Fin (CPS1EnzymeBath.Joint.atoms frame (targetJoint frame)).length)
    (inside : i.val < (chainGraph frame).atoms.length) :
    (CPS1EnzymeBath.Joint.atoms frame (targetJoint frame)).get i =
      ⟨.enzyme ((chainGraph frame).atoms.get ⟨i.val,inside⟩),(chainGraph frame).atoms.get ⟨i.val,inside⟩⟩ := by
  have found : (CPS1EnzymeBath.Joint.atoms frame (targetJoint frame))[i.val]? =
      some ⟨.enzyme ((chainGraph frame).atoms.get ⟨i.val,inside⟩),(chainGraph frame).atoms.get ⟨i.val,inside⟩⟩ := by
    have read := congrArg (fun atoms : List CPS1EnzymeBath.Joint.Atom => atoms[i.val]?) (target_atoms frame)
    rw [read,List.getElem?_append_left (by simpa only [List.length_map] using inside),
      List.getElem?_map,List.getElem?_eq_getElem inside]
    rfl
  exact (List.getElem?_eq_some_iff.mp found).2

theorem target_cp_at (i : Fin (CPS1EnzymeBath.Joint.atoms frame (targetJoint frame)).length)
    (outside : ¬ i.val < (chainGraph frame).atoms.length) :
    (CPS1EnzymeBath.Joint.atoms frame (targetJoint frame)).get i =
      CPS1EnzymeBath.Joint.bathAtom ⟨0,.carbamoylPhosphate⟩ (NativeCPProjection.templateAtom (targetCPOrdinal i outside)) := by
  have found : (CPS1EnzymeBath.Joint.atoms frame (targetJoint frame))[i.val]? =
      some (CPS1EnzymeBath.Joint.bathAtom ⟨0,.carbamoylPhosphate⟩ (NativeCPProjection.templateAtom (targetCPOrdinal i outside))) := by
    have read := congrArg (fun atoms : List CPS1EnzymeBath.Joint.Atom => atoms[i.val]?) (target_atoms frame)
    rw [read,List.getElem?_append_right (by simpa only [List.length_map] using Nat.le_of_not_gt outside),
      List.length_map,List.getElem?_map,List.getElem?_eq_getElem (targetCPOrdinal i outside).isLt]
    rfl
  exact (List.getElem?_eq_some_iff.mp found).2

section Generic
variable {cursor : CPS1ReactiveNuclear.SourceCursor frame}
  {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
  {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}
  {source : Common before step raw} {current : NativeCurrent source}

/-- The atom slot map is between two restrictions of this exact paid occurrence.
Only descriptor fields used by the charged calculus are relabelled. -/
structure JointAtomProjection (paid : SourceGeneratedPaidReturn source current)
    (joint : CPS1EnzymeBath.Joint.State frame) where
  nativeSlot : Fin (CPS1EnzymeBath.Joint.atoms frame joint).length → Fin source.atoms.length
  injective : Function.Injective nativeSlot
  element : ∀ i, (source.atoms.get (nativeSlot i)).descriptor.source.element =
    ((CPS1EnzymeBath.Joint.atoms frame joint).get i).descriptor.source.element
  charge : ∀ i, (source.atoms.get (nativeSlot i)).descriptor.source.charge =
    ((CPS1EnzymeBath.Joint.atoms frame joint).get i).descriptor.source.charge

end Generic

section Actual
variable {origin : CPS1ReactiveNuclear.SourceCursor frame} {water : Nat} {material : List RawSupply}
  {path : CPS1Recycling.SplitSite} {events : List CPS1Recycling.RawEvent}
  {feed : List CPS1Recycling.RawMaterial} {physical : PhysicalRaw} {depth : Nat}
  (whole : WholeRun origin water material path events feed physical depth) (supply : ContinuationRaw)
  (profile : supply.recycling = [] ∧ supply.recycleFeed = [] ∧ supply.physical = noPhysicalSupply)
  (receipt : LocalRepairReceipt (initialBody ⟨frame,origin⟩))
  (repaired : repairWhole whole supply = .repaired receipt)
  {priorRaw : Classical.Raw} {before : Classical.Current receipt.nextBody.current.2 priorRaw}
  {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}
  (source : Common before step raw)

include whole supply profile repaired

theorem chain_graph_exact : before.packet.source.graph = chainGraph receipt.nextBody.current.1 := by
  have owned := actual_chain_owner whole supply profile receipt repaired before.packet.source
  change Graph.fromChain _ before.packet.source.owned.chain = _
  rw [owned]
  rfl

theorem chain_prefix_exact :
    ∃ tail, source.atoms =
      (chainGraph receipt.nextBody.current.1).atoms.map
        (fun atom => (⟨.prior (.chain atom),atom⟩ : Atom receipt.nextBody.current.2)) ++ tail := by
  rw [source.atomSource,commonAtoms,Classical.Source.atoms,
    chain_graph_exact whole supply profile receipt repaired (before := before),List.map_append,List.append_assoc]
  simp only [List.map_map,Function.comp_def,Classical.AtomOrigin.descriptor]
  exact ⟨_,rfl⟩

theorem chain_length_le : (chainGraph receipt.nextBody.current.1).atoms.length ≤ source.atoms.length := by
  obtain ⟨tail,actual⟩ := chain_prefix_exact whole supply profile receipt repaired source
  rw [actual,List.length_append,List.length_map]
  omega

def chainSlot (i : Fin (chainGraph receipt.nextBody.current.1).atoms.length) : Fin source.atoms.length :=
  ⟨i.val,lt_of_lt_of_le i.isLt (chain_length_le whole supply profile receipt repaired source)⟩

theorem chain_slot_actual (i : Fin (chainGraph receipt.nextBody.current.1).atoms.length) :
    source.atoms.get (chainSlot whole supply profile receipt repaired source i) =
      ⟨.prior (.chain ((chainGraph receipt.nextBody.current.1).atoms.get i)),
        (chainGraph receipt.nextBody.current.1).atoms.get i⟩ := by
  obtain ⟨tail,actual⟩ := chain_prefix_exact whole supply profile receipt repaired source
  have found : source.atoms[i.val]? = some
      (⟨.prior (.chain ((chainGraph receipt.nextBody.current.1).atoms.get i)),
        (chainGraph receipt.nextBody.current.1).atoms.get i⟩ : Atom receipt.nextBody.current.2) := by
    rw [actual,List.getElem?_append_left (by simpa only [List.length_map] using i.isLt),
      List.getElem?_map,List.getElem?_eq_getElem i.isLt]
    rfl
  exact (List.getElem?_eq_some_iff.mp found).2

theorem chain_slot_injective :
    Function.Injective (chainSlot whole supply profile receipt repaired source) := by
  intro first second same
  apply Fin.ext
  exact congrArg (fun i : Fin source.atoms.length => i.val) same

variable {current : NativeCurrent source} (paid : SourceGeneratedPaidReturn source current)

def jointSlot (i : Fin (CPS1EnzymeBath.Joint.atoms receipt.nextBody.current.1 (targetJoint receipt.nextBody.current.1)).length) :
    Fin source.atoms.length :=
  if inside : i.val < (chainGraph receipt.nextBody.current.1).atoms.length
  then chainSlot whole supply profile receipt repaired source ⟨i.val,inside⟩
  else NativeCPProjection.cpSlot paid (targetCPOrdinal i inside)

theorem joint_slot_injective : Function.Injective (jointSlot whole supply profile receipt repaired source paid) := by
  intro first second same
  by_cases left : first.val < (chainGraph receipt.nextBody.current.1).atoms.length
  · by_cases right : second.val < (chainGraph receipt.nextBody.current.1).atoms.length
    · apply Fin.ext
      simpa only [jointSlot,dif_pos left,dif_pos right,chainSlot] using congrArg Fin.val same
    · have origins := congrArg (fun slot => (source.atoms.get slot).origin) same
      rw [jointSlot,dif_pos left,jointSlot,dif_neg right,chain_slot_actual,NativeCPProjection.cp_slot_actual] at origins
      have index := congrArg NativeCarbamoyl.cpIndex origins
      rw [NativeCPProjection.cp_index] at index
      change 10 = (targetCPOrdinal second right).val at index
      exact (Nat.ne_of_lt (targetCPOrdinal second right).isLt) index.symm |>.elim
  · by_cases right : second.val < (chainGraph receipt.nextBody.current.1).atoms.length
    · have origins := congrArg (fun slot => (source.atoms.get slot).origin) same
      rw [jointSlot,dif_neg left,jointSlot,dif_pos right,NativeCPProjection.cp_slot_actual,chain_slot_actual] at origins
      have index := congrArg NativeCarbamoyl.cpIndex origins
      rw [NativeCPProjection.cp_index] at index
      change (targetCPOrdinal first left).val = 10 at index
      exact (Nat.ne_of_lt (targetCPOrdinal first left).isLt) index |>.elim
    · simp only [jointSlot,dif_neg left,dif_neg right] at same
      have indices := congrArg Fin.val (NativeCPProjection.cp_slot_injective paid same)
      apply Fin.ext
      change first.val - (chainGraph receipt.nextBody.current.1).atoms.length =
        second.val - (chainGraph receipt.nextBody.current.1).atoms.length at indices
      omega

def source_atom_projection : JointAtomProjection paid (targetJoint receipt.nextBody.current.1) where
  nativeSlot := jointSlot whole supply profile receipt repaired source paid
  injective := joint_slot_injective whole supply profile receipt repaired source paid
  element := by
    intro i
    by_cases inside : i.val < (chainGraph receipt.nextBody.current.1).atoms.length
    · rw [jointSlot,dif_pos inside,chain_slot_actual,target_chain_at i inside]
    · rw [jointSlot,dif_neg inside,NativeCPProjection.cp_slot_actual,target_cp_at i inside]
      exact NativeCPProjection.cp_element paid (targetCPOrdinal i inside)
  charge := by
    intro i
    by_cases inside : i.val < (chainGraph receipt.nextBody.current.1).atoms.length
    · rw [jointSlot,dif_pos inside,chain_slot_actual,target_chain_at i inside]
    · rw [jointSlot,dif_neg inside,NativeCPProjection.cp_slot_actual,target_cp_at i inside]
      exact NativeCPProjection.cp_charge paid (targetCPOrdinal i inside)

end Actual
end
end CPS1MaterialIncidence.NativeJointRowsProbe
