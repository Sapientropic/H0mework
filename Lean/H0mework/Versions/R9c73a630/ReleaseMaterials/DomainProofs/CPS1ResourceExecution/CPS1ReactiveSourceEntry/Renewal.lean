import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveSourceEntry.Entry

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace CPS1ReactiveSourceEntry
noncomputable section
open CPS1ElectronicSource CPS1ReactiveNuclear CPS1ReactiveJointNuclear CPS1ReactiveSourceEntry
open CPS1ReactiveField CPS1ReactiveField.Carried
variable {frame : CPS1Recycling.Frame}

-- Every born origin, including a report absent from this event's body, moves with its stored Id.
theorem motion_birth_rows {root : CPS1Deformation.Source.Occurrence frame} {state : Snapshot}
    (before : Germ root state) (rows : CPS1AddressedReactiveJoint.Rows.Stock)
    (oldRows : BirthRows before rows) (time : ℝ)
    (after : Germ root (paidResponse before time))
    (actual : motionGerm before time = .ok after) :
    BirthRows after (originRows before time rows) := by
  intro origin id named
  have afterRow : originRow? after 0 origin = some (after.node id).row := by
    simp only [originRow?, named, Option.map_some, live_row_zero]
  have movingRow : originRow? before time origin = some (after.node id).row :=
    (origin_row_after_motion before time after actual origin).symm.trans afterRow
  cases selected : originId? before origin with
  | none => simp only [originRow?, selected, Option.map_none] at movingRow; cases movingRow
  | some oldId =>
    have original := oldRows origin oldId selected
    have live : liveRow before time oldId = (after.node id).row := by
      exact Option.some.inj (by
        simpa only [originRow?, selected, Option.map_some] using movingRow)
    rw [origin_row_read_map, original, Option.map_some,
      moved_row_full before time origin (before.node oldId).row oldId selected
        (live_row_zero before oldId)]
    exact congrArg Option.some live

def retainedSlot {current : Occurrence frame} (prior : Snapshot) (good : prior.Good)
    (source : Inlet current) (slot : Fin prior.nuclei.length) :
    Fin (renewed prior good source).nuclei.length :=
  ⟨slot.val, by
    change slot.val < (prior.nuclei ++ (freshNodes prior source).filter isNucleus).length
    rw [List.length_append]
    omega⟩

def freshSlot {current : Occurrence frame} (prior : Snapshot) (good : prior.Good)
    (source : Inlet current) (slot : Fin ((freshNodes prior source).filter isNucleus).length) :
    Fin (renewed prior good source).nuclei.length :=
  ⟨prior.nuclei.length + slot.val, by
    change prior.nuclei.length + slot.val <
      (prior.nuclei ++ (freshNodes prior source).filter isNucleus).length
    rw [List.length_append]; omega⟩

-- This slot comes from the prior Birth equivalence, never from a later body's atom order.
theorem renewed_retained_node {current : Occurrence frame} {prior : Snapshot}
    (before : Germ current.old prior) (good : prior.Good) (source : Inlet current)
    (after : Germ current.old (renewed prior good source))
    (actual : renewedGerm before good source = .ok after)
    (oldId : before.Id) (newId : after.Id) (sameKey : newId.val = oldId.val) :
    after.node newId = before.node oldId := by
  classical
  rcases renewed_binding_generated before good source after actual with
    ⟨_, _, freshKeys, _, append⟩
  let slot := (before.birth.slotEquiv before.unique).symm oldId
  have oldNamed : before.nuclearId slot = oldId :=
    (before.birth.slotEquiv before.unique).apply_symm_apply oldId
  have key : (after.nuclearId (retainedSlot prior good source slot)).val = oldId.val := by
    apply Option.some.inj
    rw [← nuclear_key_lookup, append]
    change (before.birth.nuclearKeys ++ freshKeys)[slot.val]? = some oldId.val
    rw [List.getElem?_append_left (by
      rw [before.birth.nuclearLength]; exact slot.isLt)]
    simpa only [oldNamed] using nuclear_key_lookup before slot
  have named : after.nuclearId (retainedSlot prior good source slot) = newId :=
    Subtype.ext (key.trans sameKey.symm)
  rw [← named, Germ.node, Germ.nuclearId, Birth.node_nuclearId]
  change (prior.nuclei ++ (freshNodes prior source).filter isNucleus).get
      ⟨slot.val, _⟩ = prior.nuclei.get slot
  simp only [List.get_eq_getElem]
  rw [List.getElem_append_left (by exact slot.isLt)]

theorem renewed_fresh_node {current : Occurrence frame} {prior : Snapshot}
    (good : prior.Good) (source : Inlet current)
    (after : Germ current.old (renewed prior good source))
    (slot : Fin ((freshNodes prior source).filter isNucleus).length) :
    after.node (after.nuclearId (freshSlot prior good source slot)) =
      ((freshNodes prior source).filter isNucleus).get slot := by
  rw [Germ.node, Germ.nuclearId, Birth.node_nuclearId]
  change (prior.nuclei ++ (freshNodes prior source).filter isNucleus).get
      ⟨prior.nuclei.length + slot.val, _⟩ = _
  simp only [List.get_eq_getElem]
  rw [List.getElem_append_right (as := prior.nuclei) (by omega)]
  simp only [Nat.add_sub_cancel_left]

private theorem origin_key_water {root : CPS1Deformation.Source.Occurrence frame} {state : Snapshot}
    (germ : Germ root state) (origin : CPS1AddressedHydrolysis.Origin)
    (water : CPS1AddressedHydrolysis.Water) (part : CPS1AddressedHydrolysis.WaterAtom)
    (actual : originKey? germ origin = some (Key.water water part)) : origin = .water water part := by
  cases origin with
  | old slot =>
    cases selected : (CPS1AtomicSource.Graph.fromChain frame
        germ.birth.owner.currentJoint.originBody.source).atoms[slot]? with
    | none => simp only [originKey?, selected, Option.map_none] at actual; cases actual
    | some atom => simp only [originKey?, selected, Option.map_some] at actual; cases actual
  | water nativeWater nativePart =>
    rcases Key.water.inj (Option.some.inj actual) with ⟨rfl, rfl⟩
    rfl

-- `oldRows` is the prior producer invariant. Report transport is proved from this exact raw next.
theorem renewed_birth_rows {prior : Snapshot}
    (current : Occurrence frame) (before : Germ current.old prior) (good : prior.Good)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial)
    (raw : List CPS1AddressedReactiveJoint.Rows.RawAction)
    (source : Inlet (CPS1ReactiveField.next current actions feed raw))
    (after : Germ current.old (renewed prior good source))
    (actual : renewedGerm (current := CPS1ReactiveField.next current actions feed raw) before good source = .ok after)
    (oldRows : BirthRows before current.ingress.measurements.rows) :
    BirthRows after source.body.sourceRows := by
  classical
  rcases renewed_binding_generated (current := CPS1ReactiveField.next current actions feed raw) before good source after actual with
    ⟨_, owner, freshKeys, pairs, append⟩
  have bodyRows := (CPS1AddressedReactiveJoint.admitted_body _ _ _ source.actual).2.2.1
  have preserved : ∀ address row,
      CPS1AddressedReactiveJoint.Rows.row? current.ingress.measurements.rows address = some row →
      CPS1AddressedReactiveJoint.Rows.row? source.body.sourceRows address = some row := by
    intro address row known
    rw [bodyRows]
    exact (CPS1AddressedReactiveJoint.source_generated_reactive_next
      current.ingress actions feed raw).2.2.2.2.2.1 address row known
  intro origin id named
  have read := origin_id_key after origin id named
  have held : id.val ∈ before.birth.nuclearKeys ++ (show List (Key current.old) from freshKeys) :=
    Eq.mp (congrArg (fun keys : List (Key current.old) => id.val ∈ keys) append) id.property
  rw [List.mem_append] at held
  rcases held with retained | fresh
  · let oldId : before.Id := ⟨id.val, retained⟩
    have oldKey : originKey? before origin = some id.val := by
      simpa only [originKey?, owner] using read
    have oldNamed : originId? before origin = some oldId := by
      simp only [originId?, oldKey, dif_pos retained]
      rfl
    have node := renewed_retained_node (current := CPS1ReactiveField.next current actions feed raw) before good source after actual oldId id rfl
    rw [node]
    exact preserved _ _ (oldRows origin oldId oldNamed)
  · obtain ⟨keySlot, keySame⟩ := List.mem_iff_get.mp fresh
    let slot : Fin ((freshNodes prior source).filter isNucleus).length :=
      ⟨keySlot.val, by simpa only [pairs.length_eq] using keySlot.isLt⟩
    have paired := pairs.get slot.isLt keySlot.isLt
    have member : ((freshNodes prior source).filter isNucleus).get slot ∈ source.body.nodes :=
      List.mem_of_mem_filter (List.mem_of_mem_filter (List.get_mem _ _))
    obtain ⟨water, part, binding, row⟩ := water_binding_row source _ member _ paired
    have namedWater : originKey? after origin = some (Key.water water part) :=
      read.trans (congrArg Option.some (keySame.symm.trans binding))
    have originSame := origin_key_water after origin water part namedWater
    subst origin
    have idKey : (after.nuclearId (freshSlot prior good source slot)).val = freshKeys.get keySlot := by
      apply Option.some.inj
      rw [← nuclear_key_lookup, append]
      change (before.birth.nuclearKeys ++ (show List (Key current.old) from freshKeys))[prior.nuclei.length + slot.val]? = _
      rw [List.getElem?_append_right (l₁ := before.birth.nuclearKeys) (by
        rw [before.birth.nuclearLength]; omega)]
      have offset : prior.nuclei.length + slot.val - before.birth.nuclearKeys.length = keySlot.val := by
        have length := before.birth.nuclearLength
        dsimp only [slot]
        omega
      rw [offset, List.getElem?_eq_getElem keySlot.isLt]
      rfl
    have newNamed : after.nuclearId (freshSlot prior good source slot) = id :=
      Subtype.ext (idKey.trans keySame)
    have node : after.node id = ((freshNodes prior source).filter isNucleus).get slot := by
      rw [← newNamed]
      exact renewed_fresh_node good source after slot
    exact row.trans (congrArg (fun node : CPS1AtomicDynamics.Body.Node => some node.row) node.symm)

theorem birth_rows_reprice {root : CPS1Deformation.Source.Occurrence frame} {state : Snapshot}
    (germ : Germ root state) (rows : CPS1AddressedReactiveJoint.Rows.Stock) (reserve : ℝ)
    (generated : BirthRows germ rows) : BirthRows (germ.reprice reserve) rows := by
  exact generated

theorem renewed_body_origin_bound {current : Occurrence frame} {prior : Snapshot}
    (before : Germ current.old prior) (good : prior.Good) (source : Inlet current)
    (after : Germ current.old (renewed prior good source))
    (actual : renewedGerm before good source = .ok after)
    (particle : CPS1AddressedReactiveJoint.Particle)
    (member : particle ∈ CPS1AddressedReactiveJoint.particles source.body.atoms)
    (origin : CPS1AddressedHydrolysis.Origin) (address : particle.address = .nucleus origin) :
    ∃ id, originId? after origin = some id := by
  classical
  obtain ⟨index, sourceOrigin⟩ := source_nucleus_at_origin source particle member origin address
  obtain ⟨birth, born, same⟩ := (renewed_germ_generated before good source after actual).1
  have generated := renewed_birth_generated before.birth good source birth born
  have owner := (congrArg Birth.owner same).trans generated.2.1
  let primitive : RenewalPrimitive prior source :=
    ((index,⟨0,by unfold renewalModes; omega⟩),false)
  have decoder := generated.2.2.2.2 primitive
  change (match bodyOrigin source index with
    | .old slot => match (CPS1AtomicSource.Graph.fromChain frame
        before.birth.owner.currentJoint.originBody.source).atoms[slot]? with
      | none => Except.error (IdentityFailure.unknownSeededOld slot)
      | some atom => .ok (Key.enzyme atom)
    | .water water part => .ok (Key.water water part)) =
      .ok (birth.primitiveKey (.inr primitive)) at decoder
  have recognized : (match origin with
    | .old slot => match (CPS1AtomicSource.Graph.fromChain frame
        before.birth.owner.currentJoint.originBody.source).atoms[slot]? with
      | none => Except.error (IdentityFailure.unknownSeededOld slot)
      | some atom => .ok (Key.enzyme atom)
    | .water water part => .ok (Key.water water part)) =
      .ok (after.birth.primitiveKey (.inr primitive)) := by
    simpa only [sourceOrigin, ← same] using decoder
  have named : originKey? after origin = some (after.birth.primitiveKey (.inr primitive)) := by
    cases origin with
    | old slot =>
      cases selected : (CPS1AtomicSource.Graph.fromChain frame
          before.birth.owner.currentJoint.originBody.source).atoms[slot]? with
      | none => simp only [selected] at recognized; cases recognized
      | some atom =>
        simp only [selected] at recognized
        simpa only [originKey?, owner, selected, Option.map_some] using
          congrArg Option.some (Except.ok.inj recognized)
    | water water part => exact congrArg Option.some (Except.ok.inj recognized)
  let id : after.Id := ⟨after.birth.primitiveKey (.inr primitive), after.covered (.inr primitive)⟩
  refine ⟨id, ?_⟩
  simp only [originId?, named, dif_pos (after.covered (.inr primitive))]
  rfl

theorem renewed_body_origin_aligned {current : Occurrence frame} {prior : Snapshot}
    (before : Germ current.old prior) (good : prior.Good) (source : Inlet current)
    (after : Germ current.old (renewed prior good source))
    (actual : renewedGerm before good source = .ok after)
    (generated : BirthRows after source.body.sourceRows) : BodyOriginAligned source.body after := by
  intro particle member origin address
  obtain ⟨id, named⟩ := renewed_body_origin_bound before good source after actual particle member origin address
  have row := generated origin id named
  rw [address]
  simp only [originRow?, named, Option.map_some, live_row_zero]
  exact row.symm

end
end CPS1ReactiveSourceEntry
