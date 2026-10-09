import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.NativePreparedOccurrence

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1MaterialIncidence.NativePrepareBinding
noncomputable section
open CPS1AtomicDynamics CPS1SameEventFunction CPS1PhosphorylExchange
open NativePaidEvent NativeAmmoniaDynamics NativePrepareNextProbe

variable {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
  {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
  {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}
  {source : Common before step raw} {current : NativeCurrent source}
  {paid : SourceGeneratedPaidReturn source current} {continuation : NativeCPContinuationProbe.CPNativeContinuation paid}

private theorem pose_addresses_unique (physical : PostState current) :
    (physical.pose.map (fun node => node.particle.address)).Nodup := by
  have particles := physical.particles.trans (current_particles_source source current)
  have addresses := congrArg (List.map Charged.Particle.address) particles
  simp only [List.map_map,Function.comp_def] at addresses
  rw [addresses]
  exact common_addresses_unique _ _

private theorem pose_slot_bound (physical : PostState current) (node : Body.Node) (held : node ∈ physical.pose) :
    node.particle.address.slot < source.atoms.length := by
  have particles := physical.particles.trans (current_particles_source source current)
  have present : node.particle ∈ commonParticles before.packet.source raw.fuel :=
    particles ▸ List.mem_map_of_mem held
  obtain ⟨row,indexed,member⟩ := List.mem_flatMap.mp present
  rw [Charged.atom_particle_slot (row.1.descriptor,row.2) node.particle member,source.atomSource]
  simpa only [Nat.add_zero] using List.snd_lt_of_mem_zipIdx indexed

private theorem nucleus_complete (physical : PostState current) (node : Body.Node)
    (held : node ∈ nucleusNodes physical.pose) : ∃ index : AtomSector source, postNucleus physical index = node := by
  have member := (List.mem_filter.mp held).1
  let index : AtomSector source := ⟨node.particle.address.slot,pose_slot_bound physical node member⟩
  have address : node.particle.address = .nucleus index.val := by
    have nuclear := (List.mem_filter.mp held).2
    cases actual : node.particle.address with
    | nucleus slot =>
      change Charged.Address.nucleus slot = .nucleus node.particle.address.slot
      rw [actual]
      rfl
    | electron slot orbital => simp only [actual,Bool.false_eq_true] at nuclear
  refine ⟨index,?_⟩
  exact List.inj_on_of_nodup_map (pose_addresses_unique physical)
    (post_nucleus_actual physical index).1 member ((post_nucleus_actual physical index).2.trans address.symm)

/-- Global stored modes retain their source identity; local directions retain
source atom identities. Neither is reinterpreted as a moved legacy nucleus. -/
structure NativeOriginGerm (occurrence : NativeOccurrence paid continuation) where
  nucleus : AtomSector source → Body.Node
  nucleusActual : ∀ index, nucleus index ∈ occurrence.physical.pose ∧
    (nucleus index).particle.address = .nucleus index.val
  nuclearComplete : ∀ node ∈ nucleusNodes occurrence.physical.pose, ∃ index, nucleus index = node
  nuclearInjective : Function.Injective nucleus
  nuclearOrigin : AtomSector source → AtomOrigin cursor
  originActual : nuclearOrigin = originAt source
  originUnique : Function.Injective nuclearOrigin
  primitiveOrigin : RawIndex current → FieldOrigin cursor source.nodes
  primitiveActual : primitiveOrigin = rawOrigin current
  fieldsActual : CPS1ElectronicEvolution.fields (rawField current) occurrence.physical.rawC =
    CPS1ElectronicEvolution.fields (basis current) occurrence.physical.occupied
  sourceRestriction : CPS1ReactiveNuclear.SourceCursor frame
  sourceActual : sourceRestriction = cursor
  legacyGerm : CPS1ReactiveNuclear.GermAt sourceRestriction.native
  legacyGermActual : HEq legacyGerm sourceRestriction.germ
  legacyActiveActual : match sourceRestriction.native.active with
    | none => True
    | some active => CPS1AddressedReactiveJoint.admission active.source.ingress = .ok active.body

def native_origin_germ (occurrence : NativeOccurrence paid continuation) : NativeOriginGerm occurrence := by
  refine ⟨postNucleus occurrence.physical,post_nucleus_actual occurrence.physical,
    nucleus_complete occurrence.physical,?_,originAt source,rfl,source_origin_injective source,
    rawOrigin current,rfl,post_fields occurrence.physical,
    cursor,rfl,cursor.germ,HEq.rfl,?_⟩
  · intro first second same
    apply Fin.ext
    have addresses := congrArg (fun node : Body.Node => node.particle.address) same
    rw [(post_nucleus_actual occurrence.physical first).2,
      (post_nucleus_actual occurrence.physical second).2] at addresses
    exact Charged.Address.nucleus.inj addresses
  · cases selected : cursor.native.active with
    | none => trivial
    | some active => exact active.actual

/-- The legacy next is a restriction consumer. Its old source is not the new
native prepared ledger. -/
theorem legacy_next_old (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial)
    (rows : List CPS1AddressedReactiveJoint.Rows.RawAction) :
    (CPS1ReactiveNuclear.SourceCursor.next cursor actions feed rows).native.current.old = cursor.native.current.old := rfl

end
end CPS1MaterialIncidence.NativePrepareBinding
