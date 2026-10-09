import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveJointNuclear.Contract

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

namespace CPS1ReactiveSourceEntry
noncomputable section
open CPS1ElectronicSource CPS1ReactiveNuclear CPS1ReactiveJointNuclear
open CPS1ReactiveField CPS1ReactiveField.Carried
variable {frame : CPS1Recycling.Frame}

/-- Transparent normal form of an actually successful source-owned binding. -/
def LegacyBinding {root : CPS1Deformation.Source.Occurrence frame}
    (owner : CPS1Deformation.Material frame) (node : CPS1AtomicDynamics.Body.Node) (key : Key root) : Prop :=
  ∃ slot, node.particle.address = .nucleus slot ∧
    ∃ atom : CPS1EnzymeBath.Joint.Atom,
      (CPS1EnzymeBath.Joint.atoms frame owner.currentJoint)[slot]? = some atom ∧
      node.particle.source = atom.descriptor ∧
      key = (match atom.origin with | .enzyme source => .enzyme source | .bath component source => .bath component source)

def WaterBinding {current : Occurrence frame} (source : Inlet current)
    (node : CPS1AtomicDynamics.Body.Node) (key : Key current.old) : Prop :=
  ∃ slot, node.particle.address = .nucleus slot ∧
    ∃ atom : CPS1AddressedHydrolysis.Atom, source.body.atoms[slot]? = some atom ∧
      node.particle.source = atom.descriptor ∧
      ∃ water part, atom.origin = .water water part ∧ key = .water water part

private theorem legacy_success {root : CPS1Deformation.Source.Occurrence frame}
    (owner : CPS1Deformation.Material frame) (node : CPS1AtomicDynamics.Body.Node) (key : Key root)
    (actual : (match node.particle.address with
      | .electron .. => Except.error (IdentityFailure.unknownLegacy node.particle.address)
      | .nucleus slot => match (CPS1EnzymeBath.Joint.atoms frame owner.currentJoint)[slot]? with
        | none => .error (.unknownLegacy node.particle.address)
        | some atom => if node.particle.source = atom.descriptor then
            .ok (match atom.origin with | .enzyme source => Key.enzyme source | .bath component source => .bath component source)
          else .error (.legacyDescriptor node.particle.address)) = .ok key) :
    LegacyBinding owner node key := by
  classical
  cases address : node.particle.address with
  | electron slot orbital => simp only [address] at actual; cases actual
  | nucleus slot =>
    simp only [address] at actual
    cases selected : (CPS1EnzymeBath.Joint.atoms frame owner.currentJoint)[slot]? with
    | none => simp only [selected] at actual; cases actual
    | some atom =>
      simp only [selected] at actual
      split at actual
      · rename_i descriptor
        exact ⟨slot,address,atom,selected,descriptor,(Except.ok.inj actual).symm⟩
      · cases actual

private theorem water_success {current : Occurrence frame} (source : Inlet current)
    (node : CPS1AtomicDynamics.Body.Node) (key : Key current.old)
    (actual : (match node.particle.address with
      | .electron .. => Except.error (IdentityFailure.unknownReactiveNucleus node.particle.address)
      | .nucleus slot => match source.body.atoms[slot]? with
        | none => .error (.unknownReactiveNucleus node.particle.address)
        | some atom => if node.particle.source ≠ atom.descriptor then
            .error (.reactiveDescriptor node.particle.address)
          else match atom.origin with
            | .old _ => .error (.expectedWater atom.origin)
            | .water water part => .ok (Key.water water part)) = .ok key) :
    WaterBinding source node key := by
  classical
  cases address : node.particle.address with
  | electron slot orbital => simp only [address] at actual; cases actual
  | nucleus slot =>
    simp only [address] at actual
    cases selected : source.body.atoms[slot]? with
    | none => simp only [selected] at actual; cases actual
    | some atom =>
      simp only [selected] at actual
      split at actual
      · cases actual
      · rename_i descriptor
        cases origin : atom.origin with
        | old prior => simp only [origin] at actual; cases actual
        | water water part =>
          simp only [origin] at actual
          exact ⟨slot,address,atom,selected,not_not.mp descriptor,water,part,origin,
            (Except.ok.inj actual).symm⟩

theorem initial_binding_generated {current : Occurrence frame} (material : Material current)
    (germ : Germ current.old (initial material)) (actual : initialGerm material = .ok germ) :
    germ.birth.owner = material.source.old ∧ ∃ oldKeys waterKeys,
      List.Forall₂ (LegacyBinding material.source.old)
        (List.ofFn (oldNuclearNode material.source)) oldKeys ∧
      List.Forall₂ (WaterBinding material.source)
        ((waterNodes material.source).filter isNucleus) waterKeys ∧
      germ.birth.nuclearKeys = oldKeys ++ waterKeys := by
  obtain ⟨birth,born,same⟩ := (initial_germ_generated material germ actual).1
  rcases initial_birth_generated material birth born with ⟨owner,⟨oldKeys,waterKeys,oldPairs,waterPairs,append⟩,_⟩
  refine ⟨(congrArg Birth.owner same).trans owner,oldKeys,waterKeys,?_,?_,(congrArg Birth.nuclearKeys same).trans append⟩
  · apply oldPairs.imp
    intro node key paid
    apply legacy_success material.source.old node key
    exact paid
  · apply waterPairs.imp
    intro node key paid
    apply water_success material.source node key
    exact paid

theorem renewed_binding_generated {current : Occurrence frame} {prior : Snapshot}
    (old : Germ current.old prior) (good : prior.Good) (source : Inlet current)
    (germ : Germ current.old (renewed prior good source))
    (actual : renewedGerm old good source = .ok germ) :
    source.old = old.birth.owner ∧ germ.birth.owner = old.birth.owner ∧ ∃ freshKeys,
      List.Forall₂ (WaterBinding source) ((freshNodes prior source).filter isNucleus) freshKeys ∧
      germ.birth.nuclearKeys = old.birth.nuclearKeys ++ freshKeys := by
  obtain ⟨birth,born,same⟩ := (renewed_germ_generated old good source germ actual).1
  rcases renewed_birth_generated old.birth good source birth born with ⟨sourceSame,owner,⟨freshKeys,pairs,append⟩,_,_⟩
  refine ⟨sourceSame,(congrArg Birth.owner same).trans owner,freshKeys,?_,(congrArg Birth.nuclearKeys same).trans append⟩
  apply pairs.imp
  intro node key paid
  apply water_success source node key
  exact paid

theorem origin_row_at_birth_slot {root : CPS1Deformation.Source.Occurrence frame}
    {state : Snapshot} (germ : Germ root state) (origin : CPS1AddressedHydrolysis.Origin)
    (slot : Fin state.nuclei.length)
    (selected : originKey? germ origin = some (germ.nuclearId slot).val) :
    originRow? germ 0 origin = some (state.nuclei.get slot).row := by
  classical
  simp only [originRow?,originId?,selected,dif_pos (germ.nuclearId slot).property,
    Option.map_some,live_row_zero]
  exact congrArg (fun node : CPS1AtomicDynamics.Body.Node => some node.row)
    (germ.birth.node_nuclearId germ.unique slot)

theorem nuclear_key_lookup {root : CPS1Deformation.Source.Occurrence frame}
    {state : Snapshot} (germ : Germ root state) (slot : Fin state.nuclei.length) :
    germ.birth.nuclearKeys[slot.val]? = some (germ.nuclearId slot).val := by
  have bound : slot.val < germ.birth.nuclearKeys.length := by
    rw [germ.birth.nuclearLength]
    exact slot.isLt
  rw [List.getElem?_eq_getElem bound]
  rfl

def initialWaterSlot {current : Occurrence frame} (material : Material current)
    (slot : Fin ((waterNodes material.source).filter isNucleus).length) :
    Fin (initial material).nuclei.length :=
  ⟨(List.ofFn (oldNuclearNode material.source)).length + slot.val,by
    change _ < ((List.ofFn (oldNuclearNode material.source)) ++
      (waterNodes material.source).filter isNucleus).length
    rw [List.length_append]
    omega⟩

theorem initial_water_id_node {current : Occurrence frame} (material : Material current)
    (germ : Germ current.old (initial material))
    (slot : Fin ((waterNodes material.source).filter isNucleus).length) :
    germ.node (germ.nuclearId (initialWaterSlot material slot)) =
      ((waterNodes material.source).filter isNucleus).get slot := by
  rw [Germ.node,Germ.nuclearId,Birth.node_nuclearId]
  change ((List.ofFn (oldNuclearNode material.source)) ++
    (waterNodes material.source).filter isNucleus).get
      ⟨(List.ofFn (oldNuclearNode material.source)).length+slot.val,_⟩ = _
  simp only [List.get_eq_getElem]
  rw [List.getElem_append_right (as := List.ofFn (oldNuclearNode material.source)) (by omega)]
  simp only [Nat.add_sub_cancel_left]

theorem native_particle_nucleus (atoms : List CPS1AddressedHydrolysis.Atom)
    (particle : CPS1AddressedReactiveJoint.Particle)
    (member : particle ∈ CPS1AddressedReactiveJoint.particles atoms) (slot : Nat)
    (address : particle.readout.address = .nucleus slot) :
    atoms[slot]? = some particle.atom ∧
      particle.address = .nucleus particle.atom.origin := by
  rcases List.mem_flatMap.mp member with ⟨item,listed,generated⟩
  rcases List.mem_cons.mp generated with first | rest
  · subst particle
    change CPS1AtomicDynamics.Charged.Address.nucleus item.2 = .nucleus slot at address
    have same := CPS1AtomicDynamics.Charged.Address.nucleus.inj address
    exact ⟨same ▸ List.mem_zipIdx_iff_getElem?.mp listed,rfl⟩
  · rcases List.mem_map.mp rest with ⟨orbital,_,rfl⟩
    cases address

theorem water_binding_row {current : Occurrence frame} (source : Inlet current)
    (node : CPS1AtomicDynamics.Body.Node) (member : node ∈ source.body.nodes)
    (key : Key current.old) (binding : WaterBinding source node key) :
    ∃ water part, key = .water water part ∧
      CPS1AddressedReactiveJoint.Rows.row? source.body.sourceRows (.nucleus (.water water part)) = some node.row := by
  rcases binding with ⟨slot,address,atom,selected,_,water,part,origin,keySame⟩
  rcases CPS1AddressedReactiveJoint.admitted_body _ _ _ source.actual with ⟨_,_,_,_,_,_,_,_,_,rows⟩
  rcases rows node member with ⟨_,particle,present,identity,row⟩
  have named := native_particle_nucleus source.body.atoms particle present slot
    ((congrArg CPS1AtomicDynamics.Charged.Particle.address identity).symm.trans address)
  have atomSame : particle.atom = atom := Option.some.inj (named.1.symm.trans selected)
  have stable : particle.address = .nucleus (.water water part) :=
    named.2.trans (congrArg CPS1AddressedReactiveJoint.Address.nucleus
      ((congrArg CPS1AddressedHydrolysis.Atom.origin atomSame).trans origin))
  exact ⟨water,part,keySame,stable ▸ row⟩

theorem initial_water_origin_row {current : Occurrence frame} (material : Material current)
    (germ : Germ current.old (initial material)) (actual : initialGerm material = .ok germ)
    (water : CPS1AddressedHydrolysis.Water) (part : CPS1AddressedHydrolysis.WaterAtom)
    (held : Key.water water part ∈ germ.birth.nuclearKeys) :
    originRow? germ 0 (.water water part) =
      CPS1AddressedReactiveJoint.Rows.row? material.source.body.sourceRows (.nucleus (.water water part)) := by
  classical
  rcases initial_binding_generated material germ actual with ⟨_,oldKeys,waterKeys,oldPairs,waterPairs,append⟩
  rw [append,List.mem_append] at held
  rcases held with prior | fresh
  · obtain ⟨keySlot,keySame⟩ := List.mem_iff_get.mp prior
    have pair := oldPairs.get (by simpa only [oldPairs.length_eq] using keySlot.isLt) keySlot.isLt
    rcases pair with ⟨slot,address,atom,_,_,key⟩
    rw [keySame] at key
    cases origin : atom.origin <;> simp only [origin] at key <;> cases key
  · obtain ⟨keySlot,keySame⟩ := List.mem_iff_get.mp fresh
    let slot : Fin ((waterNodes material.source).filter isNucleus).length :=
      ⟨keySlot.val,by simpa only [waterPairs.length_eq] using keySlot.isLt⟩
    have paired := waterPairs.get slot.isLt keySlot.isLt
    have member : ((waterNodes material.source).filter isNucleus).get slot ∈ material.source.body.nodes :=
      List.mem_of_mem_filter (List.mem_of_mem_filter (List.get_mem _ _))
    obtain ⟨water',part',key,row⟩ := water_binding_row material.source _ member _ paired
    have identities : water' = water ∧ part' = part := Key.water.inj (key.symm.trans keySame)
    have waterSame := identities.1
    have partSame := identities.2
    subst water'
    subst part'
    have idKey : (germ.nuclearId (initialWaterSlot material slot)).val = waterKeys.get keySlot := by
      apply Option.some.inj
      rw [← nuclear_key_lookup,append]
      change (oldKeys ++ waterKeys)[(List.ofFn (oldNuclearNode material.source)).length+slot.val]? = _
      have oldLength := oldPairs.length_eq
      rw [List.getElem?_append_right (l₁ := oldKeys) (by omega)]
      have offset : (List.ofFn (oldNuclearNode material.source)).length+slot.val-oldKeys.length = keySlot.val := by
        have lengths := oldPairs.length_eq
        dsimp only [slot]
        omega
      rw [offset,List.getElem?_eq_getElem keySlot.isLt]
      rfl
    have selected : originKey? germ (.water water part) =
        some (germ.nuclearId (initialWaterSlot material slot)).val := by
      rw [idKey,keySame]
      rfl
    have read := origin_row_at_birth_slot germ _ (initialWaterSlot material slot) selected
    have node := initial_water_id_node material germ slot
    have bodyRow : some ((initial material).nuclei.get (initialWaterSlot material slot)).row =
        CPS1AddressedReactiveJoint.Rows.row? material.source.body.sourceRows (.nucleus (.water water part)) := by
      rw [← germ.birth.node_nuclearId germ.unique (initialWaterSlot material slot)]
      exact (congrArg (fun node : CPS1AtomicDynamics.Body.Node => some node.row) node).trans row.symm
    exact read.trans bodyRow

theorem joint_enzyme_native_seed_lookup
    (owner : CPS1Deformation.Material frame) (nativeSlot : Nat)
    (jointAtom : CPS1EnzymeBath.Joint.Atom) (sourceAtom : CPS1AtomicSource.Graph.Atom)
    (selected : (CPS1EnzymeBath.Joint.atoms frame owner.currentJoint)[nativeSlot]? = some jointAtom)
    (origin : jointAtom.origin = .enzyme sourceAtom) :
    (CPS1AtomicSource.Graph.fromChain frame owner.currentJoint.originBody.source).atoms[nativeSlot]? = some sourceAtom := by
  let seed := (CPS1AtomicSource.Graph.fromChain frame owner.currentJoint.originBody.source).atoms
  let bath := owner.currentJoint.components.flatMap (fun component =>
    (CPS1EnzymeBath.Primary.template component.kind).atoms.map (CPS1EnzymeBath.Joint.bathAtom component))
  have normal : (seed.map (fun atom => (⟨.enzyme atom,atom⟩ : CPS1EnzymeBath.Joint.Atom)) ++ bath)[nativeSlot]? = some jointAtom := by
    simpa only [seed,bath,CPS1EnzymeBath.Joint.atoms,CPS1AtomicDynamics.Body.graph,CPS1AtomicSource.Current.graph] using selected
  have bound : nativeSlot < seed.length := by
    by_contra outside
    have suffix : bath[nativeSlot-seed.length]? = some jointAtom := by
      simpa only [List.getElem?_append_right (l₁ := seed.map (fun atom => (⟨.enzyme atom,atom⟩ : CPS1EnzymeBath.Joint.Atom)))
        (by simpa only [List.length_map] using Nat.le_of_not_gt outside),List.length_map] using normal
    have held := List.mem_of_getElem? suffix
    rcases List.mem_flatMap.mp held with ⟨component,_,member⟩
    rcases List.mem_map.mp member with ⟨atom,_,same⟩
    cases same
    cases origin
  have sourcePrefix : (seed.map (fun atom => (⟨.enzyme atom,atom⟩ : CPS1EnzymeBath.Joint.Atom)))[nativeSlot]? = some jointAtom := by
    simpa only [List.getElem?_append_left (l₁ := seed.map (fun atom => (⟨.enzyme atom,atom⟩ : CPS1EnzymeBath.Joint.Atom)))
      (by simpa only [List.length_map] using bound)] using normal
  rw [List.getElem?_map] at sourcePrefix
  cases native : seed[nativeSlot]? with
  | none => simp only [native,Option.map_none] at sourcePrefix; cases sourcePrefix
  | some atom =>
    simp only [native,Option.map_some,Option.some.injEq] at sourcePrefix
    have identity := congrArg CPS1EnzymeBath.Joint.Atom.origin sourcePrefix
    rw [origin] at identity
    have same := CPS1EnzymeBath.Joint.AtomOrigin.enzyme.inj identity
    exact congrArg Option.some same

theorem joint_enzyme_native_slot
    (owner : CPS1Deformation.Material frame) (nativeSlot originSlot : Nat)
    (jointAtom : CPS1EnzymeBath.Joint.Atom) (sourceAtom : CPS1AtomicSource.Graph.Atom)
    (selected : (CPS1EnzymeBath.Joint.atoms frame owner.currentJoint)[nativeSlot]? = some jointAtom)
    (origin : jointAtom.origin = .enzyme sourceAtom)
    (seeded : (CPS1AtomicSource.Graph.fromChain frame owner.currentJoint.originBody.source).atoms[originSlot]? = some sourceAtom) :
    nativeSlot = originSlot := by
  let seed := (CPS1AtomicSource.Graph.fromChain frame owner.currentJoint.originBody.source).atoms
  change seed[originSlot]? = some sourceAtom at seeded
  have native : seed[nativeSlot]? = some sourceAtom := joint_enzyme_native_seed_lookup owner nativeSlot jointAtom sourceAtom selected origin
  have seedBound : originSlot < seed.length := by
    by_contra outside
    rw [List.getElem?_eq_none (Nat.le_of_not_gt outside)] at seeded
    cases seeded
  have nativeBound : nativeSlot < seed.length := by
    by_contra outside
    rw [List.getElem?_eq_none (Nat.le_of_not_gt outside)] at native
    cases native
  have same : seed.get ⟨nativeSlot,nativeBound⟩ = seed.get ⟨originSlot,seedBound⟩ := by
    apply Option.some.inj
    simpa only [List.getElem?_eq_getElem nativeBound,List.getElem?_eq_getElem seedBound,List.get_eq_getElem]
      using native.trans seeded.symm
  have unique : seed.Nodup := List.Nodup.of_map CPS1AtomicSource.Graph.Atom.address
    (CPS1AddressedHydrolysis.graph_addresses_unique _ _)
  exact congrArg Fin.val (unique.injective_get same)

theorem legacy_rows_lookup (count : Nat)
    (rows : List (CPS1AtomicDynamics.Charged.Address × CPS1AtomicDynamics.Body.Row))
    (slot : Nat) (bound : slot < count) :
    CPS1AddressedReactiveJoint.Rows.row?
      (rows.filterMap (fun item => (legacyAddress count item.1).map (fun address => (address,item.2))))
      (.nucleus (.old slot)) = CPS1AtomicDynamics.Body.row? rows (.nucleus slot) := by
  classical
  induction rows with
  | nil => rfl
  | cons item rest ih =>
    rcases item with ⟨native,row⟩
    cases native with
    | nucleus other =>
      by_cases inside : other < count
      · by_cases same : other = slot
        · subst other
          simp [legacyAddress,bound,CPS1AddressedReactiveJoint.Rows.row?,CPS1AtomicDynamics.Body.row?]
        · have different : CPS1AddressedReactiveJoint.Address.nucleus (.old other) ≠ .nucleus (.old slot) := by
            intro equal
            exact same (CPS1AddressedHydrolysis.Origin.old.inj (CPS1AddressedReactiveJoint.Address.nucleus.inj equal))
          simpa only [List.filterMap_cons,legacyAddress,if_pos inside,Option.map_some,
            CPS1AddressedReactiveJoint.Rows.row?,CPS1AtomicDynamics.Body.row?,List.find?_cons,
            decide_eq_false_iff_not.mpr different,decide_eq_false_iff_not.mpr (by
              intro equal; exact same (CPS1AtomicDynamics.Charged.Address.nucleus.inj equal)),Option.map_none] using ih
      · have different : CPS1AtomicDynamics.Charged.Address.nucleus other ≠ .nucleus slot := by
          intro equal
          have same := CPS1AtomicDynamics.Charged.Address.nucleus.inj equal
          exact inside (same.symm ▸ bound)
        simpa only [List.filterMap_cons,legacyAddress,if_neg inside,Option.map_none,
          CPS1AtomicDynamics.Body.row?,List.find?_cons,decide_eq_false_iff_not.mpr different] using ih
    | electron other orbital =>
      by_cases inside : other < count
      · simpa only [List.filterMap_cons,legacyAddress,if_pos inside,Option.map_some,
          CPS1AddressedReactiveJoint.Rows.row?,CPS1AtomicDynamics.Body.row?,List.find?_cons,
          reduceCtorEq,decide_false,Option.map_none] using ih
      · simpa only [List.filterMap_cons,legacyAddress,if_neg inside,Option.map_none,
          CPS1AtomicDynamics.Body.row?,List.find?_cons,reduceCtorEq,decide_false] using ih

/-- A law of this original stored source, generated by its actual native gather. -/
def OriginalRows {current : Occurrence frame} (material : Material current) : Prop :=
  ∀ index : CPS1MolecularFrame.NuclearIndex material.source.old.reference,
    CPS1AtomicDynamics.Body.row? material.source.old.currentJoint.rows
      (CPS1MolecularFrame.address material.source.old.reference index) = some (material.source.old.nuclearRow index)

/-- Every currently born origin reads this same full stored nuclear row. -/
def BirthRows {root : CPS1Deformation.Source.Occurrence frame} {state : Snapshot}
    (germ : Germ root state) (rows : CPS1AddressedReactiveJoint.Rows.Stock) : Prop :=
  ∀ origin id, originId? germ origin = some id →
    CPS1AddressedReactiveJoint.Rows.row? rows (.nucleus origin) = some (germ.node id).row

theorem origin_id_key {root : CPS1Deformation.Source.Occurrence frame} {state : Snapshot}
    (germ : Germ root state) (origin : CPS1AddressedHydrolysis.Origin) (id : germ.Id)
    (actual : originId? germ origin = some id) : originKey? germ origin = some id.val := by
  classical
  unfold originId? at actual
  cases selected : originKey? germ origin with
  | none => simp only [selected] at actual; cases actual
  | some key =>
    simp only [selected] at actual
    split at actual
    · cases Option.some.inj actual
      rfl
    · cases actual

theorem initial_old_origin_row
    (old : CPS1Deformation.Source.Occurrence frame)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial)
    (raw : List CPS1AddressedReactiveJoint.Rows.RawAction)
    (material : Material (CPS1ReactiveField.next (CPS1ReactiveField.start old) actions feed raw))
    (selected : heldDeformed old.current.stock = some material.source.old)
    (germ : Germ old (initial material)) (actual : initialGerm material = .ok germ)
    (original : OriginalRows material) (originSlot : Nat) (id : germ.Id)
    (named : originId? germ (.old originSlot) = some id) :
    CPS1AddressedReactiveJoint.Rows.row? material.source.body.sourceRows (.nucleus (.old originSlot)) = some (germ.node id).row := by
  classical
  rcases initial_binding_generated material germ actual with ⟨owner,oldKeys,waterKeys,oldPairs,waterPairs,append⟩
  have keyRead := origin_id_key germ (.old originSlot) id named
  have seedRead : ((CPS1AtomicSource.Graph.fromChain frame material.source.old.currentJoint.originBody.source).atoms[originSlot]?).map
      (fun atom => (Key.enzyme atom : Key old)) = some id.val := by
    simpa only [originKey?,owner] using keyRead
  cases seeded : (CPS1AtomicSource.Graph.fromChain frame material.source.old.currentJoint.originBody.source).atoms[originSlot]? with
  | none => simp only [seeded,Option.map_none] at seedRead; cases seedRead
  | some sourceAtom =>
    simp only [seeded,Option.map_some,Option.some.injEq] at seedRead
    have held : Key.enzyme sourceAtom ∈ oldKeys ++ waterKeys := append ▸ (seedRead.symm ▸ id.property)
    rcases List.mem_append.mp held with prior | fresh
    · obtain ⟨keySlot,keySame⟩ := List.mem_iff_get.mp prior
      let index : CPS1MolecularFrame.NuclearIndex material.source.old.reference :=
        ⟨keySlot.val,by
          have lengths := oldPairs.length_eq
          rw [List.length_ofFn] at lengths
          exact lengths.symm ▸ keySlot.isLt⟩
      have paired := oldPairs.get (by simpa only [List.length_ofFn] using index.isLt) keySlot.isLt
      have bound : LegacyBinding (root := old) material.source.old (oldNuclearNode material.source index) (Key.enzyme sourceAtom) := by
        have sameKey : oldKeys[keySlot.val] = (Key.enzyme sourceAtom : Key old) := keySame
        simpa only [List.get_eq_getElem,List.getElem_ofFn,index,sameKey] using paired
      rcases bound with ⟨nativeSlot,nodeAddress,jointAtom,jointSelected,_,jointKey⟩
      have origin : jointAtom.origin = .enzyme sourceAtom := by
        cases tag : jointAtom.origin with
        | enzyme atom =>
          simp only [tag,Key.enzyme.injEq] at jointKey
          exact congrArg CPS1EnzymeBath.Joint.AtomOrigin.enzyme jointKey.symm
        | bath component atom => simp only [tag] at jointKey; cases jointKey
      have slots := joint_enzyme_native_slot material.source.old nativeSlot originSlot jointAtom sourceAtom jointSelected origin seeded
      subst nativeSlot
      let birthSlot : Fin (initial material).nuclei.length := ⟨index.val,by
        change index.val < (List.ofFn (oldNuclearNode material.source) ++ (waterNodes material.source).filter isNucleus).length
        rw [List.length_append,List.length_ofFn]
        omega⟩
      have key : (germ.nuclearId birthSlot).val = id.val := by
        have lookup : germ.birth.nuclearKeys[birthSlot.val]? = some (Key.enzyme sourceAtom : Key old) := by
          refine (congrArg (fun keys : List (Key old) => keys[birthSlot.val]?) append).trans ?_
          change (oldKeys ++ waterKeys)[keySlot.val]? = _
          rw [List.getElem?_append_left keySlot.isLt,List.getElem?_eq_getElem keySlot.isLt]
          exact congrArg Option.some keySame
        exact Option.some.inj ((nuclear_key_lookup germ birthSlot).symm.trans
          (lookup.trans (congrArg Option.some seedRead)))
      have idSame : germ.nuclearId birthSlot = id := Subtype.ext key
      have nodeSame : germ.node id = oldNuclearNode material.source index := by
        rw [← idSame,Germ.node,Germ.nuclearId,Birth.node_nuclearId]
        change (List.ofFn (oldNuclearNode material.source) ++ (waterNodes material.source).filter isNucleus).get birthSlot = _
        simp only [List.get_eq_getElem]
        rw [List.getElem_append_left (as := List.ofFn (oldNuclearNode material.source)) (by simpa only [List.length_ofFn] using index.isLt)]
        simp only [List.getElem_ofFn]
        apply congrArg (oldNuclearNode material.source)
        exact Fin.ext rfl
      have bound : originSlot < (CPS1AtomicSource.Graph.fromChain frame material.source.old.currentJoint.originBody.source).atoms.length := by
        exact (List.getElem?_eq_some_iff.mp seeded).1
      have legacy : CPS1AddressedReactiveJoint.Rows.row? (legacyRows old) (.nucleus (.old originSlot)) =
          some (oldNuclearNode material.source index).row := by
        simp only [legacyRows,selected]
        rw [legacy_rows_lookup _ _ originSlot bound]
        have originalRow := original index
        change CPS1AtomicDynamics.Body.row? material.source.old.currentJoint.rows
          (oldNuclearNode material.source index).particle.address = some (oldNuclearNode material.source index).row at originalRow
        rw [nodeAddress] at originalRow
        exact originalRow
      have preserved := actual_legacy_rows_preserved old actions feed raw _ _ legacy
      have admitted := CPS1AddressedReactiveJoint.admitted_body _ _ _ material.source.actual
      rw [admitted.2.2.1,nodeSame]
      exact preserved
    · obtain ⟨keySlot,keySame⟩ := List.mem_iff_get.mp fresh
      have pair := waterPairs.get (by simpa only [waterPairs.length_eq] using keySlot.isLt) keySlot.isLt
      rcases pair with ⟨_,_,_,_,_,water,part,_,key⟩
      rw [keySame] at key
      cases key

theorem initial_birth_rows
    (old : CPS1Deformation.Source.Occurrence frame)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial)
    (raw : List CPS1AddressedReactiveJoint.Rows.RawAction)
    (material : Material (CPS1ReactiveField.next (CPS1ReactiveField.start old) actions feed raw))
    (selected : heldDeformed old.current.stock = some material.source.old)
    (germ : Germ old (initial material)) (actual : initialGerm material = .ok germ)
    (original : OriginalRows material) : BirthRows germ material.source.body.sourceRows := by
  intro origin id named
  cases origin with
  | old slot => exact initial_old_origin_row old actions feed raw material selected germ actual original slot id named
  | water water part =>
    have key := origin_id_key germ (.water water part) id named
    change some (Key.water water part) = some id.val at key
    have held : Key.water water part ∈ germ.birth.nuclearKeys := (Option.some.inj key).symm ▸ id.property
    have read := initial_water_origin_row material germ actual water part held
    have current : originRow? germ 0 (.water water part) = some (germ.node id).row := by
      simp only [originRow?,named,Option.map_some,live_row_zero]
    exact read.symm.trans current

theorem particle_origin_nucleus (atoms : List CPS1AddressedHydrolysis.Atom)
    (particle : CPS1AddressedReactiveJoint.Particle)
    (member : particle ∈ CPS1AddressedReactiveJoint.particles atoms)
    (origin : CPS1AddressedHydrolysis.Origin) (address : particle.address = .nucleus origin) :
    ∃ slot, particle.readout.address = .nucleus slot := by
  rcases List.mem_flatMap.mp member with ⟨item,_,generated⟩
  rcases List.mem_cons.mp generated with first | rest
  · subst particle
    exact ⟨item.2,rfl⟩
  · rcases List.mem_map.mp rest with ⟨orbital,_,rfl⟩
    cases address

theorem source_nucleus_at_origin {current : Occurrence frame} (source : Inlet current)
    (particle : CPS1AddressedReactiveJoint.Particle)
    (member : particle ∈ CPS1AddressedReactiveJoint.particles source.body.atoms)
    (origin : CPS1AddressedHydrolysis.Origin) (address : particle.address = .nucleus origin) :
    ∃ index : NuclearIndex source.body, bodyOrigin source index = origin := by
  rcases CPS1AddressedReactiveJoint.admitted_body _ _ _ source.actual with ⟨_,_,_,_,_,_,_,mapped,_,_⟩
  have present : particle.readout ∈ source.body.nodes.map CPS1AtomicDynamics.Body.Node.particle := by
    rw [mapped]
    exact List.mem_map.mpr ⟨particle,member,rfl⟩
  obtain ⟨node,listed,identity⟩ := List.mem_map.mp present
  obtain ⟨slot,nativeAddress⟩ := particle_origin_nucleus source.body.atoms particle member origin address
  have nodeAddress := (congrArg CPS1AtomicDynamics.Charged.Particle.address identity).trans nativeAddress
  have filtered : node ∈ nuclei source.body := List.mem_filter.mpr ⟨listed,by
    simp only [isNucleus,nodeAddress]⟩
  obtain ⟨index,nodeIdentity⟩ := List.mem_iff_get.mp filtered
  have born := source_nuclear_particle source index
  have readout : (sourceNuclearParticle source index).readout = particle.readout :=
    born.2.1.symm.trans ((congrArg CPS1AtomicDynamics.Body.Node.particle nodeIdentity).trans identity)
  have same : sourceNuclearParticle source index = particle := List.inj_on_of_nodup_map
    (CPS1AddressedReactiveJoint.particle_readout_unique source.body.atoms) born.1 member
      (congrArg CPS1AtomicDynamics.Charged.Particle.address readout)
  exact ⟨index,by rw [bodyOrigin,same,address]; rfl⟩

private theorem reactive_key_read {root : CPS1Deformation.Source.Occurrence frame} {state : Snapshot}
    (germ : Germ root state) (owner : CPS1Deformation.Material frame) (same : germ.birth.owner = owner)
    (origin : CPS1AddressedHydrolysis.Origin) (key : Key root)
    (actual : (match origin with
      | .old slot => match (CPS1AtomicSource.Graph.fromChain frame owner.currentJoint.originBody.source).atoms[slot]? with
        | none => Except.error (IdentityFailure.unknownSeededOld slot)
        | some source => .ok (Key.enzyme source)
      | .water water part => .ok (Key.water water part)) = .ok key) :
    originKey? germ origin = some key := by
  cases origin with
  | old slot =>
    cases selected : (CPS1AtomicSource.Graph.fromChain frame owner.currentJoint.originBody.source).atoms[slot]? with
    | none => simp only [selected] at actual; cases actual
    | some source =>
      simp only [selected] at actual
      simpa only [originKey?,same,selected,Option.map_some] using congrArg Option.some (Except.ok.inj actual)
  | water water part =>
    exact congrArg Option.some (Except.ok.inj actual)

theorem initial_body_origin_bound {current : Occurrence frame} (material : Material current)
    (germ : Germ current.old (initial material)) (actual : initialGerm material = .ok germ)
    (particle : CPS1AddressedReactiveJoint.Particle)
    (member : particle ∈ CPS1AddressedReactiveJoint.particles material.source.body.atoms)
    (origin : CPS1AddressedHydrolysis.Origin) (address : particle.address = .nucleus origin) :
    ∃ id, originId? germ origin = some id := by
  classical
  obtain ⟨index,sourceOrigin⟩ := source_nucleus_at_origin material.source particle member origin address
  obtain ⟨birth,born,same⟩ := (initial_germ_generated material germ actual).1
  have generated := initial_birth_generated material birth born
  have owner := (congrArg Birth.owner same).trans generated.1
  let primitive : CommonPrimitive material.source := .inr ((index,⟨0,by unfold addedModes; omega⟩),false)
  have named := reactive_key_read germ material.source.old owner (bodyOrigin material.source index)
    (birth.primitiveKey primitive) (by exact generated.2.2 primitive)
  have read : originKey? germ origin = some (germ.birth.primitiveKey primitive) := by
    simpa only [sourceOrigin,← same] using named
  let id : germ.Id := ⟨germ.birth.primitiveKey primitive,germ.covered primitive⟩
  refine ⟨id,?_⟩
  simp only [originId?,read,dif_pos (germ.covered primitive)]
  rfl

/-- Source-local row presence is tested before admission; it supplies no physical endpoint. -/
def LegacyComplete {current : Occurrence frame} (material : Material current) : Prop := OriginalRows material

 theorem initial_source_origin_aligned
    (old : CPS1Deformation.Source.Occurrence frame)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial)
    (raw : List CPS1AddressedReactiveJoint.Rows.RawAction)
    (material : Material (CPS1ReactiveField.next (CPS1ReactiveField.start old) actions feed raw))
    (selected : heldDeformed old.current.stock = some material.source.old)
    (germ : Germ old (initial material)) (actual : initialGerm material = .ok germ)
    (complete : LegacyComplete material) :
    BodyOriginAligned material.source.body germ := by
  intro particle member origin address
  obtain ⟨id,named⟩ := initial_body_origin_bound material germ actual particle member origin address
  have rows := initial_birth_rows old actions feed raw material selected germ actual complete
  rw [address]
  have read : originRow? germ 0 origin = some (germ.node id).row := by
    change (originId? germ origin).map (liveRow germ 0) = _
    rw [named,Option.map_some,live_row_zero]
  exact read.trans (rows origin id named).symm

 theorem initial_actual_step
    (old : CPS1Deformation.Source.Occurrence frame)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial)
    (raw : List CPS1AddressedReactiveJoint.Rows.RawAction)
    (material : Material (CPS1ReactiveField.next (CPS1ReactiveField.start old) actions feed raw))
    (selected : heldDeformed old.current.stock = some material.source.old)
    (germ : Germ old (initial material)) (actual : initialGerm material = .ok germ)
    (complete : LegacyComplete material) (margin : 0 < material.reserve) :
    let active : Active frame := ⟨CPS1ReactiveField.next (CPS1ReactiveField.start old) actions feed raw,
      initial material,initial_good material,material.source.body,material.source.actual,
      material.source.body.reserve⟩
    let cursor : SourceCursor frame := ⟨⟨active.source,some active,[]⟩,.ok germ⟩
    ∃ next pulse, step cursor = .ok (next,pulse) ∧ pulse.Valid ∧ Ready next := by
  dsimp only
  apply step_ready
  refine ⟨_,rfl,rfl,margin,germ,rfl,?_⟩
  exact initial_source_origin_aligned old actions feed raw material selected germ actual complete

end
end CPS1ReactiveSourceEntry
