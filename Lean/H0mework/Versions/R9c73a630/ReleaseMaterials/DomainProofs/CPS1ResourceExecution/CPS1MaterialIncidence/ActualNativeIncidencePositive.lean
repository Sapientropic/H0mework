import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.ActualNativeSelection
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1PhosphorylExchange.Roles

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1MaterialIncidence
noncomputable section
open CPS1PhosphorylExchange CPS1ElectronicSource CPS1AtomicDynamics CPS1AtomicSource
open CPS1SameEventFunction
open scoped BigOperators InnerProductSpace Matrix
variable {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
  {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
  {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}

private theorem fuel_payload_mem (source : Common before step raw) (atom : Atom cursor)
    (held : atom ∈ source.atoms) (slot : Nat) (kind : FuelKind) (payload : Graph.Atom)
    (origin : atom.origin = .fuel slot kind payload) : payload ∈ (fuelGraph kind).atoms := by
  rw [source.atomSource] at held
  rcases List.mem_append.mp held with priorHeld | fuelHeld
  · obtain ⟨prior,_,same⟩ := List.mem_map.mp priorHeld
    have impossible := (congrArg Atom.origin same).trans origin
    cases impossible
  · obtain ⟨entry,_,entryHeld⟩ := List.mem_flatMap.mp fuelHeld
    obtain ⟨original,originalHeld,same⟩ := List.mem_map.mp entryHeld
    have identity := (congrArg Atom.origin same).trans origin
    have components := AtomOrigin.fuel.inj identity
    rw [components.2.1] at originalHeld
    rwa [components.2.2] at originalHeld

private theorem selected_payload_unique (kind : FuelKind) (name : String) (payload : Graph.Atom)
    (filtered : (fuelGraph kind).atoms.filter (fun atom => atom.address.atom == name) = [payload])
    (atom : Graph.Atom) (held : atom ∈ (fuelGraph kind).atoms) (named : atom.address.atom = name) :
    atom = payload := by
  have member : atom ∈ (fuelGraph kind).atoms.filter (fun atom => atom.address.atom == name) :=
    List.mem_filter.mpr ⟨held,by simpa only [beq_iff_eq] using named⟩
  rw [filtered] at member
  exact List.mem_singleton.mp member

private theorem selected_role_origin (source : Common before step raw)
    (occurrence : Nat) (kind : FuelKind) (name : String) (payload : Graph.Atom) (slot : Nat)
    (filtered : (fuelGraph kind).atoms.filter (fun atom => atom.address.atom == name) = [payload])
    (selected : ((source.atoms.zipIdx).find? (fun entry => match entry.1.origin with
      | .fuel index source atom => index == occurrence && source == kind && atom.address.atom == name
      | _ => false)).map Prod.snd = some slot) :
    originAt? source.atoms (.nucleus slot) = some (.fuel occurrence kind payload) := by
  obtain ⟨entry,found,index⟩ := Option.map_eq_some_iff.mp selected
  have held : entry ∈ source.atoms.zipIdx := List.mem_of_find?_eq_some found
  have measured := List.mk_mem_zipIdx_iff_getElem?.mp held
  have role := List.find?_some (p := fun entry : Atom cursor × Nat => match entry.1.origin with
    | .fuel atp source atom => atp == occurrence && source == kind && atom.address.atom == name
    | _ => false) found
  cases origin : entry.1.origin with
  | prior old => simp only [origin,Bool.false_eq_true] at role
  | fuel actualSlot actualKind original =>
    simp only [origin,Bool.and_eq_true,beq_iff_eq] at role
    obtain ⟨⟨sameSlot,sameKind⟩,sameName⟩ := role
    subst actualSlot
    subst actualKind
    have generated := fuel_payload_mem source entry.1 (List.fst_mem_of_mem_zipIdx held)
      occurrence kind original origin
    have same := selected_payload_unique kind name payload filtered original generated sameName
    rw [← index]
    simp only [originAt?,Charged.Address.slot,measured,Option.map_some,origin,same]

private theorem phosphorus_filter :
    (fuelGraph .atp).atoms.filter (fun atom => atom.address.atom == "28") = [phosphorusDescriptor] := by
  decide +kernel
private theorem leaving_filter :
    (fuelGraph .atp).atoms.filter (fun atom => atom.address.atom == "25") = [leavingDescriptor] := by
  decide +kernel
private theorem attacking_filter :
    (fuelGraph .bicarbonate).atoms.filter (fun atom => atom.address.atom == "O2") = [attackingDescriptor] := by
  decide +kernel

private def phosphorylSourceDebit (occurrence : Nat) : SourceBond cursor :=
  ⟨.fuel occurrence .atp leavingDescriptor,.fuel occurrence .atp phosphorusDescriptor,
    "SING",false,"STEREONONE"⟩

private def phosphorylGraphDebit : Graph.Bond :=
  ⟨⟨0,"25"⟩,⟨0,"28"⟩,"SING",false,"STEREONONE",.component⟩

private theorem source_debit_mem (source : Common before step raw) (occurrence : Nat)
    (indexed : (FuelKind.atp,occurrence) ∈ raw.fuel.zipIdx) :
    phosphorylSourceDebit (cursor := cursor) occurrence ∈ source.bonds := by
  rw [source.bondSource]
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨(.atp,occurrence),indexed,?_⟩
  change phosphorylSourceDebit occurrence ∈ atpGraph.bonds.filterMap (fun bond => do
    let first ← atpGraph.atoms.find? (fun atom => atom.address == bond.left)
    let second ← atpGraph.atoms.find? (fun atom => atom.address == bond.right)
    pure ⟨.fuel occurrence .atp first,.fuel occurrence .atp second,bond.order,bond.aromatic,bond.stereo⟩)
  have held : phosphorylGraphDebit ∈ atpGraph.bonds := by decide +kernel
  have left : atpGraph.atoms.find? (fun atom => atom.address == phosphorylGraphDebit.left) =
      some leavingDescriptor := by decide +kernel
  have right : atpGraph.atoms.find? (fun atom => atom.address == phosphorylGraphDebit.right) =
      some phosphorusDescriptor := by decide +kernel
  refine List.mem_filterMap.mpr ⟨phosphorylGraphDebit,held,?_⟩
  simp only [left,right,Bind.bind,Option.bind_some,Pure.pure]
  rfl

theorem native_incidence_channel_source_origins (source : Common before step raw)
    (current : NativeCurrent source) :
    ∃ atp bct, (FuelKind.atp,atp) ∈ raw.fuel.zipIdx ∧
      originAt? source.atoms current.channel.phosphorus = some (.fuel atp .atp phosphorusDescriptor) ∧
      originAt? source.atoms current.channel.leavingOxygen = some (.fuel atp .atp leavingDescriptor) ∧
      originAt? source.atoms current.channel.attackingOxygen = some (.fuel bct .bicarbonate attackingDescriptor) := by
  have selected := current.channelActual
  simp only [channel?,Bind.bind,Option.bind_eq_some_iff,Pure.pure,Option.some.injEq] at selected
  obtain ⟨atp,atpFound,bct,_,p,pFound,leave,leaveFound,attack,attackFound,same⟩ := selected
  change (raw.fuel.zipIdx.find? (fun entry => entry.1 == .atp)).map Prod.snd = some atp at atpFound
  obtain ⟨entry,found,index⟩ := Option.map_eq_some_iff.mp atpFound
  have entryHeld := List.mem_of_find?_eq_some found
  have kind : entry.1 = .atp := by simpa only [beq_iff_eq] using List.find?_some found
  have indexed : (FuelKind.atp,atp) ∈ raw.fuel.zipIdx := by
    rw [← kind,← index]
    exact entryHeld
  change ((source.atoms.zipIdx).find? (fun entry => match entry.1.origin with
      | .fuel slot source atom => slot == atp && source == .atp && atom.address.atom == "28"
      | _ => false)).map Prod.snd = some p at pFound
  change ((source.atoms.zipIdx).find? (fun entry => match entry.1.origin with
      | .fuel slot source atom => slot == atp && source == .atp && atom.address.atom == "25"
      | _ => false)).map Prod.snd = some leave at leaveFound
  change ((source.atoms.zipIdx).find? (fun entry => match entry.1.origin with
      | .fuel slot source atom => slot == bct && source == .bicarbonate && atom.address.atom == "O2"
      | _ => false)).map Prod.snd = some attack at attackFound
  rw [← same]
  exact ⟨atp,bct,indexed,
    selected_role_origin source atp .atp "28" phosphorusDescriptor p phosphorus_filter pFound,
    selected_role_origin source atp .atp "25" leavingDescriptor leave leaving_filter leaveFound,
    selected_role_origin source bct .bicarbonate "O2" attackingDescriptor attack attacking_filter attackFound⟩

theorem native_incidence_source_token (source : Common before step raw) (current : NativeCurrent source) :
    ∃ token, sourceToken? source current = some token := by
  obtain ⟨atp,bct,indexed,p,leaving,attacking⟩ := native_incidence_channel_source_origins source current
  have held := source_debit_mem source atp indexed
  have present : (source.bonds.find? (fun bond =>
      ((bond.left == .fuel atp .atp phosphorusDescriptor && bond.right == .fuel atp .atp leavingDescriptor) ||
       (bond.left == .fuel atp .atp leavingDescriptor && bond.right == .fuel atp .atp phosphorusDescriptor)) &&
        bond.order == "SING")).isSome := by
    apply List.find?_isSome.mpr
    exact ⟨phosphorylSourceDebit atp,held,by simp [phosphorylSourceDebit]⟩
  unfold sourceToken?
  simp only [p,leaving,attacking,Bind.bind,Option.bind_some]
  cases found : source.bonds.find? (fun bond =>
      ((bond.left == .fuel atp .atp phosphorusDescriptor && bond.right == .fuel atp .atp leavingDescriptor) ||
       (bond.left == .fuel atp .atp leavingDescriptor && bond.right == .fuel atp .atp phosphorusDescriptor)) &&
        bond.order == "SING") with
  | none => rw [found] at present; cases present
  | some old => exact ⟨_,rfl⟩

theorem native_incidence_source_selection (source : Common before step raw) (current : NativeCurrent source) :
    ∃ selection, selectIncidence? source current = .ok selection := by
  obtain ⟨centre,leaving,attacking,p,l,a⟩ := native_incidence_channel_nuclear_selection source current
  obtain ⟨bond,selected⟩ := native_incidence_source_token source current
  refine ⟨⟨centre,leaving,attacking,p,l,a,bond,selected⟩,?_⟩
  unfold selectIncidence?
  split
  · rename_i missing
    have impossible := missing.symm.trans p
    cases impossible
  · rename_i actualCentre found
    have same := Option.some.inj (found.symm.trans p)
    subst actualCentre
    split
    · rename_i missing
      have impossible := missing.symm.trans l
      cases impossible
    · rename_i actualLeaving found
      have same := Option.some.inj (found.symm.trans l)
      subst actualLeaving
      split
      · rename_i missing
        have impossible := missing.symm.trans a
        cases impossible
      · rename_i actualAttacking found
        have same := Option.some.inj (found.symm.trans a)
        subst actualAttacking
        split
        · rename_i missing
          have impossible := missing.symm.trans selected
          cases impossible
        · rename_i actualBond found
          have same := Option.some.inj (found.symm.trans selected)
          subst actualBond
          rfl

private theorem prior_descriptor_electron_valid (source : Classical.Source cursor)
    (atom : Classical.AtomOrigin cursor) (held : atom ∈ source.atoms) :
    atom.descriptor.source.charge ≤ (Charged.atomicNumber atom.descriptor.source.element : ℤ) := by
  rcases List.mem_append.mp held with chainHeld | ammoniaHeld
  · obtain ⟨original,originalHeld,same⟩ := List.mem_map.mp chainHeld
    subst atom
    exact Charged.graph_atom_valid _ _ original originalHeld
  · obtain ⟨original,originalHeld,same⟩ := List.mem_map.mp ammoniaHeld
    subst atom
    have valid : ∀ atom ∈ ammoniaGraph.atoms,
        atom.source.charge ≤ (Charged.atomicNumber atom.source.element : ℤ) := by decide +kernel
    exact valid original originalHeld

private theorem fuel_descriptor_electron_valid (kind : FuelKind)
    (atom : Graph.Atom) (held : atom ∈ (fuelGraph kind).atoms) :
    atom.source.charge ≤ (Charged.atomicNumber atom.source.element : ℤ) := by
  cases kind with
  | atp =>
    obtain ⟨original,originalHeld,same⟩ := List.mem_map.mp held
    subst atom
    exact CPS1EnzymeBath.Primary.original_electron_count .atp original originalHeld
  | bicarbonate =>
    have valid : ∀ atom ∈ bicarbonateGraph.atoms,
        atom.source.charge ≤ (Charged.atomicNumber atom.source.element : ℤ) := by decide +kernel
    exact valid atom held

theorem source_descriptor_electron_valid (source : Common before step raw)
    (atom : Atom cursor) (held : atom ∈ source.atoms) :
    atom.descriptor.source.charge ≤ (Charged.atomicNumber atom.descriptor.source.element : ℤ) := by
  rw [source.atomSource] at held
  rcases List.mem_append.mp held with priorHeld | fuelHeld
  · obtain ⟨original,originalHeld,same⟩ := List.mem_map.mp priorHeld
    subst atom
    exact prior_descriptor_electron_valid before.packet.source original originalHeld
  · obtain ⟨entry,_,entryHeld⟩ := List.mem_flatMap.mp fuelHeld
    obtain ⟨original,originalHeld,same⟩ := List.mem_map.mp entryHeld
    subst atom
    exact fuel_descriptor_electron_valid entry.1 original originalHeld

private theorem inventory_nonnegative (atoms : List (Atom cursor))
    (valid : ∀ atom ∈ atoms,
      atom.descriptor.source.charge ≤ (Charged.atomicNumber atom.descriptor.source.element : ℤ))
    (origin : AtomOrigin cursor) :
    0 ≤ nuclearInventory atoms origin-chargeInventory atoms origin := by
  classical
  induction atoms with
  | nil => simp [nuclearInventory,chargeInventory]
  | cons atom rest ih =>
    have head := valid atom List.mem_cons_self
    have tail := ih (fun other held => valid other (List.mem_cons_of_mem _ held))
    change 0 ≤
      ((Finsupp.single atom.origin (Charged.atomicNumber atom.descriptor.source.element : ℤ) : Charges cursor) origin+
        nuclearInventory rest origin)-
      ((Finsupp.single atom.origin atom.descriptor.source.charge : Charges cursor) origin+
        chargeInventory rest origin)
    by_cases same : atom.origin = origin
    · simp only [same,Finsupp.single_eq_same]
      omega
    · simp only [Finsupp.single_apply,if_neg same,zero_add]
      exact tail

theorem initial_electron_ready (source : Common before step raw) :
    electronReady source (sourceGraph source) := by
  intro origin _
  exact inventory_nonnegative source.atoms (source_descriptor_electron_valid source) origin

private theorem origin_sum_absent (atoms : List (Atom cursor)) (weight : Atom cursor → ℤ)
    (origin : AtomOrigin cursor) (absent : origin ∉ atoms.map Atom.origin) :
    ((atoms.map (fun atom => Finsupp.single atom.origin (weight atom))).sum : Charges cursor) origin = 0 := by
  classical
  induction atoms with
  | nil => simp
  | cons atom rest ih =>
    simp only [List.map_cons,List.mem_cons,not_or] at absent
    simp only [List.map_cons,List.sum_cons,Finsupp.add_apply,Finsupp.single_apply,
      if_neg (Ne.symm absent.1),ih absent.2,add_zero]

private theorem origin_sum_selected (atoms : List (Atom cursor)) (weight : Atom cursor → ℤ)
    (unique : (atoms.map Atom.origin).Nodup) (atom : Atom cursor) (held : atom ∈ atoms) :
    ((atoms.map (fun other => Finsupp.single other.origin (weight other))).sum : Charges cursor) atom.origin =
      weight atom := by
  classical
  induction atoms with
  | nil => simp only [List.not_mem_nil] at held
  | cons first rest ih =>
    have nodup := List.nodup_cons.mp unique
    rcases List.mem_cons.mp held with same | restHeld
    · subst atom
      simp only [List.map_cons,List.sum_cons,Finsupp.add_apply,Finsupp.single_eq_same,
        origin_sum_absent rest weight first.origin nodup.1,add_zero]
    · have different : first.origin ≠ atom.origin := by
        intro same
        apply nodup.1
        rw [same]
        exact List.mem_map_of_mem restHeld
      simp only [List.map_cons,List.sum_cons,Finsupp.add_apply,Finsupp.single_apply,
        if_neg different,zero_add]
      exact ih nodup.2 restHeld

theorem initial_source_atom_electrons (source : Common before step raw)
    (atom : Atom cursor) (held : atom ∈ source.atoms) :
    electronInventory source (sourceGraph source) atom.origin =
      (Charged.atomicNumber atom.descriptor.source.element : ℤ)-atom.descriptor.source.charge := by
  have unique := source_vertices_unique source
  change (source.atoms.map Atom.origin).Nodup at unique
  change nuclearInventory source.atoms atom.origin-chargeInventory source.atoms atom.origin = _
  unfold nuclearInventory chargeInventory
  rw [origin_sum_selected source.atoms _ unique atom held,
    origin_sum_selected source.atoms _ unique atom held]

private theorem source_fuel_descriptor (source : Common before step raw)
    (atom : Atom cursor) (held : atom ∈ source.atoms)
    (occurrence : Nat) (kind : FuelKind) (payload : Graph.Atom)
    (origin : atom.origin = .fuel occurrence kind payload) : atom.descriptor = payload := by
  rw [source.atomSource] at held
  rcases List.mem_append.mp held with priorHeld | fuelHeld
  · obtain ⟨original,_,same⟩ := List.mem_map.mp priorHeld
    subst atom
    cases origin
  · obtain ⟨entry,_,entryHeld⟩ := List.mem_flatMap.mp fuelHeld
    obtain ⟨original,_,same⟩ := List.mem_map.mp entryHeld
    subst atom
    exact (AtomOrigin.fuel.inj origin).2.2

theorem initial_source_fuel_electrons (source : Common before step raw)
    (occurrence : Nat) (kind : FuelKind) (payload : Graph.Atom)
    (held : AtomOrigin.fuel occurrence kind payload ∈ vertices source) :
    electronInventory source (sourceGraph source) (.fuel occurrence kind payload) =
      (Charged.atomicNumber payload.source.element : ℤ)-payload.source.charge := by
  obtain ⟨atom,atomHeld,origin⟩ := List.mem_map.mp held
  have descriptor := source_fuel_descriptor source atom atomHeld occurrence kind payload origin
  have inventory := initial_source_atom_electrons source atom atomHeld
  simpa only [origin,descriptor] using inventory

private def fuelComponent : AtomOrigin cursor → Option (Nat × FuelKind)
  | .prior _ => none
  | .fuel slot kind _ => some (slot,kind)

private def resolvedSourceBonds (graph : Graph.Molecule) (origin : Graph.Atom → AtomOrigin cursor) :
    List (SourceBond cursor) :=
  graph.bonds.filterMap (fun bond => do
    let first ← graph.atoms.find? (fun atom => atom.address == bond.left)
    let second ← graph.atoms.find? (fun atom => atom.address == bond.right)
    pure ⟨origin first,origin second,bond.order,bond.aromatic,bond.stereo⟩)

private theorem resolved_bond_component (graph : Graph.Molecule) (origin : Graph.Atom → AtomOrigin cursor)
    (tag : Option (Nat × FuelKind)) (same : ∀ atom, fuelComponent (origin atom) = tag)
    (bond : SourceBond cursor) (held : bond ∈ resolvedSourceBonds graph origin) :
    fuelComponent bond.left = fuelComponent bond.right := by
  obtain ⟨original,_,found⟩ := List.mem_filterMap.mp held
  simp only [Bind.bind,Option.bind_eq_some_iff,Pure.pure,Option.some.injEq] at found
  obtain ⟨left,_,right,_,identity⟩ := found
  subst bond
  exact (same left).trans (same right).symm

private theorem source_bond_component (source : Common before step raw)
    (bond : SourceBond cursor) (held : bond ∈ source.bonds) :
    fuelComponent bond.left = fuelComponent bond.right := by
  rw [source.bondSource] at held
  change bond ∈ (resolvedSourceBonds before.packet.source.graph (fun atom => .prior (.chain atom)) ++
    resolvedSourceBonds ammoniaGraph (fun atom => .prior (.ammonia before.packet.source.ammonia.slot atom))) ++
    raw.fuel.zipIdx.flatMap (fun entry => resolvedSourceBonds (fuelGraph entry.1) (.fuel entry.2 entry.1)) at held
  rcases List.mem_append.mp held with priorHeld | fuelHeld
  · rcases List.mem_append.mp priorHeld with chainHeld | ammoniaHeld
    · exact resolved_bond_component _ _ none (fun _ => rfl) bond chainHeld
    · exact resolved_bond_component _ _ none (fun _ => rfl) bond ammoniaHeld
  · obtain ⟨entry,_,entryHeld⟩ := List.mem_flatMap.mp fuelHeld
    exact resolved_bond_component _ _ (some (entry.2,entry.1)) (fun _ => rfl) bond entryHeld

private theorem bond_inventory_nonnegative (bonds : List (SourceBond cursor)) (bond : SourceBond cursor) :
    0 ≤ bondInventory bonds bond := by
  classical
  induction bonds with
  | nil => simp [bondInventory]
  | cons first rest ih =>
    change 0 ≤ (Finsupp.single first 1 : Incidence cursor) bond+bondInventory rest bond
    by_cases same : first = bond
    · simp only [same,Finsupp.single_eq_same]
      omega
    · simp only [Finsupp.single_apply,if_neg same,zero_add]
      exact ih

private theorem bond_inventory_paid (bonds : List (SourceBond cursor)) (bond : SourceBond cursor)
    (held : bond ∈ bonds) : 1 ≤ bondInventory bonds bond := by
  classical
  induction bonds with
  | nil => simp only [List.not_mem_nil] at held
  | cons first rest ih =>
    change 1 ≤ (Finsupp.single first 1 : Incidence cursor) bond+bondInventory rest bond
    rcases List.mem_cons.mp held with same | restHeld
    · subst bond
      simp only [Finsupp.single_eq_same]
      have nonnegative := bond_inventory_nonnegative rest first
      omega
    · have tail := ih restHeld
      by_cases same : first = bond
      · simp only [same,Finsupp.single_eq_same]
        omega
      · simp only [Finsupp.single_apply,if_neg same,zero_add]
        exact tail

private theorem bond_inventory_absent (bonds : List (SourceBond cursor)) (bond : SourceBond cursor)
    (absent : bond ∉ bonds) : bondInventory bonds bond = 0 := by
  classical
  induction bonds with
  | nil => simp [bondInventory]
  | cons first rest ih =>
    have conditions : bond ≠ first ∧ bond ∉ rest := by
      simpa only [List.mem_cons,not_or] using absent
    change (Finsupp.single first 1 : Incidence cursor) bond+bondInventory rest bond = 0
    simp only [Finsupp.single_apply,if_neg (Ne.symm conditions.1),ih conditions.2,add_zero]

private theorem native_selection_origins (source : Common before step raw) (current : NativeCurrent source)
    (selection : IncidenceSelection source current) :
    ∃ atp bct,
      sectorOrigin current selection.centre = .fuel atp .atp phosphorusDescriptor ∧
      sectorOrigin current selection.leaving = .fuel atp .atp leavingDescriptor ∧
      sectorOrigin current selection.attacking = .fuel bct .bicarbonate attackingDescriptor := by
  obtain ⟨atp,bct,_,p,l,a⟩ := native_incidence_channel_source_origins source current
  exact ⟨atp,bct,
    Option.some.inj ((nuclear_sector_actual source current _ _ selection.centreActual).2.symm.trans p),
    Option.some.inj ((nuclear_sector_actual source current _ _ selection.leavingActual).2.symm.trans l),
    Option.some.inj ((nuclear_sector_actual source current _ _ selection.attackingActual).2.symm.trans a)⟩

private theorem native_selection_pair_absent (source : Common before step raw) (current : NativeCurrent source)
    (selection : IncidenceSelection source current) (bond : SourceBond cursor) (held : bond ∈ source.bonds) :
    ¬ ((bond.left = selection.bond.credit.left ∧ bond.right = selection.bond.credit.right) ∨
       (bond.left = selection.bond.credit.right ∧ bond.right = selection.bond.credit.left)) := by
  have component := source_bond_component source bond held
  obtain ⟨atp,bct,p,l,a⟩ := native_selection_origins source current selection
  obtain ⟨creditLeft,creditRight,_,_,_⟩ := selected_source_bond_shape selection
  intro pair
  rw [creditLeft,creditRight,p,a] at pair
  rcases pair with ⟨left,right⟩ | ⟨left,right⟩
  · simp only [left,right,fuelComponent,Option.some.injEq,Prod.mk.injEq] at component
    cases component.2
  · simp only [left,right,fuelComponent,Option.some.injEq,Prod.mk.injEq] at component
    cases component.2

theorem native_incidence_source_initial_guards (source : Common before step raw) (current : NativeCurrent source)
    (selection : IncidenceSelection source current) :
    selection.token.safe source ∧
      electronReady source (sourceGraph source) ∧
      1 ≤ electronInventory source (sourceGraph source) selection.token.chargeDonor ∧
      (∀ bond ∈ selection.token.debits, bond ∉ (chargedInitial source current).spent) ∧
      (∀ bond ∈ selection.token.debits, 1 ≤ (sourceGraph source).incidence bond) ∧
      (∀ bond ∈ selection.token.credits, (sourceGraph source).incidence bond = 0) ∧
      (∀ bond ∈ selection.token.credits, adjacent (sourceGraph source) bond.left bond.right = false) := by
  classical
  obtain ⟨atp,bct,p,l,a⟩ := native_selection_origins source current selection
  have vertices := source_token_vertices source current selection.bond selection.bondActual
  obtain ⟨creditLeft,creditRight,_,_,_⟩ := selected_source_bond_shape selection
  have donorHeld : sectorOrigin current selection.attacking ∈ CPS1MaterialIncidence.vertices source :=
    List.mem_map_of_mem (List.get_mem _ _)
  have receiverHeld : sectorOrigin current selection.leaving ∈ CPS1MaterialIncidence.vertices source :=
    List.mem_map_of_mem (List.get_mem _ _)
  have donorDistinct : sectorOrigin current selection.attacking ≠ sectorOrigin current selection.leaving := by
    rw [a,l]
    intro same
    cases (AtomOrigin.fuel.inj same).2.1
  have creditDistinct : selection.bond.credit.left ≠ selection.bond.credit.right := by
    rw [creditLeft,creditRight,p,a]
    intro same
    cases (AtomOrigin.fuel.inj same).2.1
  have safe : selection.token.safe source := by
    refine ⟨donorHeld,receiverHeld,donorDistinct,?_,?_⟩
    · intro bond held
      have same : bond = selection.bond.debit := by simpa [IncidenceSelection.token,ChargedToken.debits] using held
      subst bond
      exact ⟨vertices.1,vertices.2.1,vertices.2.2.1⟩
    · intro bond held
      have same : bond = selection.bond.credit := by simpa [IncidenceSelection.token,ChargedToken.credits] using held
      subst bond
      exact ⟨vertices.2.2.2.1,vertices.2.2.2.2,creditDistinct⟩
  have donorInventory : electronInventory source (sourceGraph source) selection.token.chargeDonor = 9 := by
    change electronInventory source (sourceGraph source) (sectorOrigin current selection.attacking) = 9
    rw [a] at donorHeld ⊢
    rw [initial_source_fuel_electrons source bct .bicarbonate attackingDescriptor donorHeld]
    decide +kernel
  have creditAbsent : selection.bond.credit ∉ source.bonds := by
    intro held
    exact native_selection_pair_absent source current selection selection.bond.credit held (Or.inl ⟨rfl,rfl⟩)
  refine ⟨safe,initial_electron_ready source,by rw [donorInventory]; norm_num,?_,?_,?_,?_⟩
  · intro bond _
    simp [chargedInitial,ChargedState.spent]
  · intro bond held
    have same : bond = selection.bond.debit := by simpa [IncidenceSelection.token,ChargedToken.debits] using held
    subst bond
    exact bond_inventory_paid source.bonds selection.bond.debit vertices.1
  · intro bond held
    have same : bond = selection.bond.credit := by simpa [IncidenceSelection.token,ChargedToken.credits] using held
    subst bond
    exact bond_inventory_absent source.bonds selection.bond.credit creditAbsent
  · intro credit held
    have same : credit = selection.bond.credit := by simpa [IncidenceSelection.token,ChargedToken.credits] using held
    subst credit
    apply Bool.eq_false_iff.mpr
    intro occupied
    obtain ⟨bond,bondHeld,checked⟩ := List.any_eq_true.mp occupied
    have checkedParts : decide (0 < (sourceGraph source).incidence bond) = true ∧
        ((bond.left == selection.bond.credit.left && bond.right == selection.bond.credit.right) ||
          (bond.left == selection.bond.credit.right && bond.right == selection.bond.credit.left)) = true := by
      simpa only [Bool.and_eq_true] using checked
    have pair := checkedParts.2
    have supported : (sourceGraph source).incidence bond ≠ 0 := by
      exact Finsupp.mem_support_iff.mp (Finset.mem_toList.mp bondHeld)
    have sourceHeld : bond ∈ source.bonds := by
      by_contra absent
      exact supported (bond_inventory_absent source.bonds bond absent)
    apply native_selection_pair_absent source current selection bond sourceHeld
    simpa only [Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] using pair

theorem native_incidence_source_positive (source : Common before step raw) (current : NativeCurrent source) :
    ∃ trace, nativeIncidence? source current = .ok trace := by
  classical
  obtain ⟨selection,selected⟩ := native_incidence_source_selection source current
  obtain ⟨safe,ready,paid,unused,debit,credit,pair⟩ :=
    native_incidence_source_initial_guards source current selection
  let state := chargedInitial source current
  have readyState : electronReady source state.graph := ready
  have paidState : 1 ≤ electronInventory source state.graph selection.token.chargeDonor := paid
  have unusedState : ∀ bond ∈ selection.token.debits, bond ∉ state.spent := unused
  have debitState : ∀ bond ∈ selection.token.debits, 1 ≤ state.graph.incidence bond := debit
  have creditState : ∀ bond ∈ selection.token.credits, state.graph.incidence bond = 0 := credit
  have pairState : ∀ bond ∈ selection.token.credits, adjacent state.graph bond.left bond.right = false := pair
  let trace : NativeIncidenceTrace source current :=
    ⟨selection,state,safe,readyState,paidState,unusedState,debitState,creditState,pairState⟩
  refine ⟨trace,?_⟩
  unfold nativeIncidence?
  rw [selected]
  change ((if safe : selection.token.safe source then
    if ready : electronReady source state.graph then
      if paid : 1 ≤ electronInventory source state.graph selection.token.chargeDonor then
        if unused : ∀ bond ∈ selection.token.debits, bond ∉ state.spent then
          if debit : ∀ bond ∈ selection.token.debits, 1 ≤ state.graph.incidence bond then
            if credit : ∀ bond ∈ selection.token.credits, state.graph.incidence bond = 0 then
              if pairFree : ∀ bond ∈ selection.token.credits, adjacent state.graph bond.left bond.right = false then
                .ok (⟨selection,state,safe,ready,paid,unused,debit,credit,pairFree⟩ : NativeIncidenceTrace source current)
              else .error .occupiedAtomPair
            else .error .occupiedBond
          else .error .bondShortage
        else .error .reusedSourceBond
      else .error (.electronShortage selection.token.chargeDonor (electronInventory source state.graph selection.token.chargeDonor))
    else .error .negativeElectronResource
  else .error .unsafeSourceToken) : Except (NativeIncidenceResidual cursor) (NativeIncidenceTrace source current)) = .ok trace
  simp only [dif_pos safe,dif_pos readyState,dif_pos paidState,dif_pos unusedState,
    dif_pos debitState,dif_pos creditState,dif_pos pairState]
  rfl

end
end CPS1MaterialIncidence
