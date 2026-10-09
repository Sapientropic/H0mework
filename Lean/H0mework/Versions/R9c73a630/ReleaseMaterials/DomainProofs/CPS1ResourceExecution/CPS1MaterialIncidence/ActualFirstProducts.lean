import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.ActualNativeIncidencePositive
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.ActualSourceChargedContinuation

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1MaterialIncidence.NativeProducts
noncomputable section
open CPS1AtomicSource CPS1AtomicDynamics CPS1SameEventFunction CPS1PhosphorylExchange
open scoped BigOperators

variable {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
  {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
  {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}

structure DescriptorBond where
  left : Graph.Atom
  right : Graph.Atom
  order : String
  aromatic : Bool
  stereo : String
  deriving DecidableEq

def descriptorBonds (graph : Graph.Molecule) : List DescriptorBond :=
  graph.bonds.filterMap (fun bond => do
    let first ← graph.atoms.find? (fun atom => atom.address == bond.left)
    let second ← graph.atoms.find? (fun atom => atom.address == bond.right)
    pure ⟨first,second,bond.order,bond.aromatic,bond.stereo⟩)

def DescriptorBond.lift (origin : Graph.Atom → AtomOrigin cursor) (bond : DescriptorBond) : SourceBond cursor :=
  ⟨origin bond.left,origin bond.right,bond.order,bond.aromatic,bond.stereo⟩

def resolvedBonds (graph : Graph.Molecule) (origin : Graph.Atom → AtomOrigin cursor) :
    List (SourceBond cursor) := (descriptorBonds graph).map (DescriptorBond.lift origin)

private theorem resolved_bonds_source (graph : Graph.Molecule) (origin : Graph.Atom → AtomOrigin cursor) :
    resolvedBonds graph origin = graph.bonds.filterMap (fun bond => do
      let first ← graph.atoms.find? (fun atom => atom.address == bond.left)
      let second ← graph.atoms.find? (fun atom => atom.address == bond.right)
      pure (⟨origin first,origin second,bond.order,bond.aromatic,bond.stereo⟩ : SourceBond cursor)) := by
  unfold resolvedBonds descriptorBonds
  rw [List.map_filterMap]
  apply List.filterMap_congr
  intro bond _
  cases left : graph.atoms.find? (fun atom => atom.address == bond.left) <;>
    cases right : graph.atoms.find? (fun atom => atom.address == bond.right) <;>
    simp [DescriptorBond.lift]

theorem common_bonds_resolved (source : Common before step raw) :
    source.bonds =
      resolvedBonds before.packet.source.graph (fun atom => .prior (.chain atom)) ++
      resolvedBonds ammoniaGraph (fun atom => .prior (.ammonia before.packet.source.ammonia.slot atom)) ++
      raw.fuel.zipIdx.flatMap (fun entry => resolvedBonds (fuelGraph entry.1) (.fuel entry.2 entry.1)) := by
  rw [source.bondSource]
  simp only [resolved_bonds_source]
  rfl

def gammaAtom (atom : Graph.Atom) : Bool :=
  atom.address.atom == "26" || atom.address.atom == "27" ||
    atom.address.atom == "28" || atom.address.atom == "29"

def atpDebit : DescriptorBond :=
  ⟨leavingDescriptor,phosphorusDescriptor,"SING",false,"STEREONONE"⟩

private theorem atp_cross_gamma :
    ∀ bond ∈ descriptorBonds atpGraph,
      gammaAtom bond.left ≠ gammaAtom bond.right ↔ bond = atpDebit := by
  decide +kernel

private theorem atp_debit_unique :
    (descriptorBonds atpGraph).filter (fun bond =>
      ((bond.left == phosphorusDescriptor && bond.right == leavingDescriptor) ||
       (bond.left == leavingDescriptor && bond.right == phosphorusDescriptor)) && bond.order == "SING") =
      [atpDebit] := by
  decide +kernel

def sourceDebit (atp : Nat) : SourceBond cursor :=
  atpDebit.lift (.fuel atp .atp)

def sourceCredit (atp bct : Nat) : SourceBond cursor :=
  ⟨.fuel atp .atp phosphorusDescriptor,.fuel bct .bicarbonate attackingDescriptor,
    "SING",false,"STEREONONE"⟩

private theorem source_debit_identity (source : Common before step raw) (atp : Nat)
    (bond : SourceBond cursor) (held : bond ∈ source.bonds)
    (ends : (bond.left = .fuel atp .atp phosphorusDescriptor ∧
        bond.right = .fuel atp .atp leavingDescriptor) ∨
      (bond.left = .fuel atp .atp leavingDescriptor ∧
        bond.right = .fuel atp .atp phosphorusDescriptor))
    (order : bond.order = "SING") : bond = sourceDebit atp := by
  rw [common_bonds_resolved source] at held
  rcases List.mem_append.mp held with priorHeld | fuelHeld
  · rcases List.mem_append.mp priorHeld with chainHeld | ammoniaHeld
    · obtain ⟨descriptor,_,same⟩ := List.mem_map.mp chainHeld
      subst bond
      rcases ends with ⟨left,_⟩ | ⟨left,_⟩ <;> cases left
    · obtain ⟨descriptor,_,same⟩ := List.mem_map.mp ammoniaHeld
      subst bond
      rcases ends with ⟨left,_⟩ | ⟨left,_⟩ <;> cases left
  · obtain ⟨entry,_,entryHeld⟩ := List.mem_flatMap.mp fuelHeld
    obtain ⟨descriptor,descriptorHeld,same⟩ := List.mem_map.mp entryHeld
    subst bond
    rcases entry with ⟨kind,index⟩
    have indexSame : index = atp := by
      rcases ends with ⟨left,_⟩ | ⟨left,_⟩ <;>
        exact (AtomOrigin.fuel.inj left).1
    have kindSame : kind = .atp := by
      rcases ends with ⟨left,_⟩ | ⟨left,_⟩ <;>
        exact (AtomOrigin.fuel.inj left).2.1
    subst index
    subst kind
    have payloadEnds : (descriptor.left = phosphorusDescriptor ∧ descriptor.right = leavingDescriptor) ∨
        (descriptor.left = leavingDescriptor ∧ descriptor.right = phosphorusDescriptor) := by
      rcases ends with ⟨left,right⟩ | ⟨left,right⟩
      · exact Or.inl ⟨(AtomOrigin.fuel.inj left).2.2,(AtomOrigin.fuel.inj right).2.2⟩
      · exact Or.inr ⟨(AtomOrigin.fuel.inj left).2.2,(AtomOrigin.fuel.inj right).2.2⟩
    have filtered : descriptor ∈ (descriptorBonds atpGraph).filter (fun candidate =>
        ((candidate.left == phosphorusDescriptor && candidate.right == leavingDescriptor) ||
         (candidate.left == leavingDescriptor && candidate.right == phosphorusDescriptor)) &&
          candidate.order == "SING") := by
      apply List.mem_filter.mpr
      refine ⟨descriptorHeld,?_⟩
      simpa only [Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq,DescriptorBond.lift] using And.intro payloadEnds order
    rw [atp_debit_unique] at filtered
    have descriptorSame := List.mem_singleton.mp filtered
    rw [descriptorSame]
    rfl

theorem selected_product_token (source : Common before step raw) (current : NativeCurrent source)
    (selection : IncidenceSelection source current) :
    ∃ atp bct,
      selection.bond = ⟨sourceDebit atp,sourceCredit atp bct⟩ ∧
      selection.token.chargeDonor = .fuel bct .bicarbonate attackingDescriptor ∧
      selection.token.chargeReceiver = .fuel atp .atp leavingDescriptor := by
  obtain ⟨atp,bct,_,p,l,a⟩ := native_incidence_channel_source_origins source current
  have selected := selection.bondActual
  unfold sourceToken? at selected
  simp only [p,l,a,Bind.bind,Option.bind_some,Pure.pure,Option.bind_eq_some_iff,Option.some.injEq] at selected
  obtain ⟨old,found,same⟩ := selected
  have oldHeld := List.mem_of_find?_eq_some found
  have shape : ((old.left = .fuel atp .atp phosphorusDescriptor ∧ old.right = .fuel atp .atp leavingDescriptor) ∨
      (old.left = .fuel atp .atp leavingDescriptor ∧ old.right = .fuel atp .atp phosphorusDescriptor)) ∧
      old.order = "SING" := by
    simpa only [Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] using List.find?_some found
  have oldSame := source_debit_identity source atp old oldHeld shape.1 shape.2
  have donor : sectorOrigin current selection.attacking = .fuel bct .bicarbonate attackingDescriptor :=
    Option.some.inj ((nuclear_sector_actual source current _ _ selection.attackingActual).2.symm.trans a)
  have receiver : sectorOrigin current selection.leaving = .fuel atp .atp leavingDescriptor :=
    Option.some.inj ((nuclear_sector_actual source current _ _ selection.leavingActual).2.symm.trans l)
  refine ⟨atp,bct,?_,donor,receiver⟩
  rw [← same,oldSame]
  rfl

private theorem lift_fuel_injective (occurrence : Nat) (kind : FuelKind) :
    Function.Injective (DescriptorBond.lift (AtomOrigin.fuel (cursor := cursor) occurrence kind)) := by
  intro first second same
  cases first
  cases second
  simpa only [DescriptorBond.lift,SourceBond.mk.injEq,AtomOrigin.fuel.injEq,
    DescriptorBond.mk.injEq,true_and] using same

private theorem prior_chain_debit_absent (graph : Graph.Molecule) (atp : Nat) :
    sourceDebit (cursor := cursor) atp ∉ resolvedBonds graph (fun atom => .prior (.chain atom)) := by
  intro held
  obtain ⟨descriptor,_,same⟩ := List.mem_map.mp held
  have left := congrArg SourceBond.left same
  change AtomOrigin.prior (.chain descriptor.left) = .fuel atp .atp leavingDescriptor at left
  cases left

private theorem prior_ammonia_debit_absent (graph : Graph.Molecule) (atp : Nat)
    (slot : Fin (LiveStock cursor).length) :
    sourceDebit (cursor := cursor) atp ∉ resolvedBonds graph (fun atom => .prior (.ammonia slot atom)) := by
  intro held
  obtain ⟨descriptor,_,same⟩ := List.mem_map.mp held
  have left := congrArg SourceBond.left same
  change AtomOrigin.prior (.ammonia slot descriptor.left) = .fuel atp .atp leavingDescriptor at left
  cases left

private theorem fuel_debit_count_bound (atp occurrence : Nat) (kind : FuelKind) :
    (resolvedBonds (fuelGraph kind) (AtomOrigin.fuel (cursor := cursor) occurrence kind)).count
      (sourceDebit atp) ≤ if occurrence == atp then 1 else 0 := by
  classical
  by_cases sameOccurrence : occurrence = atp
  · subst occurrence
    simp only [beq_self_eq_true,ite_true]
    cases kind with
    | atp =>
      change ((descriptorBonds atpGraph).map (DescriptorBond.lift (.fuel atp .atp))).count
        (atpDebit.lift (.fuel atp .atp)) ≤ 1
      rw [List.count_map_of_injective _ _ (lift_fuel_injective atp .atp)]
      decide +kernel
    | bicarbonate =>
      have absent : sourceDebit (cursor := cursor) atp ∉
          resolvedBonds (fuelGraph .bicarbonate) (.fuel atp .bicarbonate) := by
        intro held
        obtain ⟨descriptor,_,same⟩ := List.mem_map.mp held
        have left := congrArg SourceBond.left same
        have kind := (AtomOrigin.fuel.inj left).2.1
        cases kind
      rw [List.count_eq_zero.mpr absent]
      exact Nat.zero_le _
  · have absent : sourceDebit (cursor := cursor) atp ∉
        resolvedBonds (fuelGraph kind) (.fuel occurrence kind) := by
      intro held
      obtain ⟨descriptor,_,same⟩ := List.mem_map.mp held
      have left := congrArg SourceBond.left same
      exact sameOccurrence (AtomOrigin.fuel.inj left).1
    rw [List.count_eq_zero.mpr absent]
    simp [sameOccurrence]

private theorem fuel_debits_count_bound (entries : List (FuelKind × Nat)) (atp : Nat) :
    (entries.flatMap (fun entry => resolvedBonds (fuelGraph entry.1)
      (AtomOrigin.fuel (cursor := cursor) entry.2 entry.1))).count (sourceDebit atp) ≤
        (entries.map Prod.snd).count atp := by
  induction entries with
  | nil => simp
  | cons entry rest ih =>
    simp only [List.flatMap_cons,List.count_append,List.map_cons,List.count_cons]
    simpa only [Nat.add_comm] using Nat.add_le_add (fuel_debit_count_bound atp entry.2 entry.1) ih

private theorem source_debit_unique (source : Common before step raw) (atp : Nat)
    (held : sourceDebit atp ∈ source.bonds) : (source.bonds.erase (sourceDebit atp)).count (sourceDebit atp) = 0 := by
  have bound : source.bonds.count (sourceDebit atp) ≤ 1 := by
    rw [common_bonds_resolved source,List.count_append,List.count_append,
      List.count_eq_zero.mpr (prior_chain_debit_absent _ atp),
      List.count_eq_zero.mpr (prior_ammonia_debit_absent _ atp _),Nat.zero_add]
    apply (fuel_debits_count_bound raw.fuel.zipIdx atp).trans
    have unique : (raw.fuel.zipIdx.map Prod.snd).Nodup := by
      rw [List.zipIdx_map_snd]
      exact List.nodup_range' _
    exact List.nodup_iff_count_le_one.mp unique atp
  have positive := List.count_pos_iff.mpr held
  have once : source.bonds.count (sourceDebit atp) = 1 := by omega
  simp only [List.count_erase,once,beq_self_eq_true,ite_true,Nat.sub_self]

inductive ProductOwner
  | chain
  | ammonia
  | adp
  | carboxyphosphate
  | retainedFuel (occurrence : Nat) (kind : FuelKind)
  deriving DecidableEq

def owner (atp bct : Nat) : AtomOrigin cursor → ProductOwner
  | .prior (.chain _) => .chain
  | .prior (.ammonia _ _) => .ammonia
  | .fuel occurrence kind atom =>
    if occurrence = atp ∧ kind = .atp then
      if gammaAtom atom then .carboxyphosphate else .adp
    else if occurrence = bct ∧ kind = .bicarbonate then .carboxyphosphate
    else .retainedFuel occurrence kind

def productAtoms (source : Common before step raw) (atp bct : Nat) (part : ProductOwner) : List (Atom cursor) :=
  source.atoms.filter (fun atom => owner atp bct atom.origin == part)

def productBonds (source : Common before step raw) (atp bct : Nat) (part : ProductOwner) :
    List (SourceBond cursor) :=
  ((source.bonds.erase (sourceDebit atp)) ++ [sourceCredit atp bct]).filter
    (fun bond => owner atp bct bond.left == part)

def retainedAtoms (source : Common before step raw) (atp bct : Nat) : List (Atom cursor) :=
  source.atoms.filter (fun atom => !(owner atp bct atom.origin == .adp) &&
    !(owner atp bct atom.origin == .carboxyphosphate))

private theorem source_bond_owner (source : Common before step raw) (atp bct : Nat)
    (bond : SourceBond cursor) (held : bond ∈ source.bonds) (different : bond ≠ sourceDebit atp) :
    owner atp bct bond.left = owner atp bct bond.right := by
  rw [common_bonds_resolved source] at held
  rcases List.mem_append.mp held with priorHeld | fuelHeld
  · rcases List.mem_append.mp priorHeld with chainHeld | ammoniaHeld
    · obtain ⟨descriptor,_,same⟩ := List.mem_map.mp chainHeld
      subst bond
      rfl
    · obtain ⟨descriptor,_,same⟩ := List.mem_map.mp ammoniaHeld
      subst bond
      rfl
  · obtain ⟨entry,_,entryHeld⟩ := List.mem_flatMap.mp fuelHeld
    obtain ⟨descriptor,descriptorHeld,same⟩ := List.mem_map.mp entryHeld
    subst bond
    rcases entry with ⟨kind,index⟩
    change (if index = atp ∧ kind = .atp then
        if gammaAtom descriptor.left then ProductOwner.carboxyphosphate else ProductOwner.adp
      else if index = bct ∧ kind = .bicarbonate then ProductOwner.carboxyphosphate else ProductOwner.retainedFuel index kind) =
      (if index = atp ∧ kind = .atp then
        if gammaAtom descriptor.right then ProductOwner.carboxyphosphate else ProductOwner.adp
      else if index = bct ∧ kind = .bicarbonate then ProductOwner.carboxyphosphate else ProductOwner.retainedFuel index kind)
    by_cases selected : index = atp ∧ kind = .atp
    · obtain ⟨rfl,rfl⟩ := selected
      have descriptorDifferent : descriptor ≠ atpDebit := by
        intro same
        apply different
        rw [same]
        rfl
      have gammaSame : gammaAtom descriptor.left = gammaAtom descriptor.right := by
        by_contra unequal
        exact descriptorDifferent ((atp_cross_gamma descriptor descriptorHeld).mp unequal)
      simp only [gammaSame]
    · simp only [if_neg selected]

private theorem bond_inventory_erase (bonds : List (SourceBond cursor)) (bond : SourceBond cursor)
    (held : bond ∈ bonds) :
    bondInventory (bonds.erase bond) = bondInventory bonds-Finsupp.single bond 1 := by
  have erased := List.sum_map_erase (fun other : SourceBond cursor =>
    (Finsupp.single other 1 : Incidence cursor)) held
  change (Finsupp.single bond 1 : Incidence cursor)+bondInventory (bonds.erase bond) = bondInventory bonds at erased
  exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using erased)

private theorem product_atom_partition (source : Common before step raw) (atp bct : Nat) :
    source.atoms.Perm (productAtoms source atp bct .adp ++
      productAtoms source atp bct .carboxyphosphate ++ retainedAtoms source atp bct) := by
  classical
  let adp := fun atom : Atom cursor => owner atp bct atom.origin == .adp
  let carboxy := fun atom : Atom cursor => owner atp bct atom.origin == .carboxyphosphate
  have outer := List.filter_append_perm adp source.atoms
  have inner := List.filter_append_perm carboxy (source.atoms.filter (fun atom => !adp atom))
  have carboxySame : (source.atoms.filter (fun atom => !adp atom)).filter carboxy =
      source.atoms.filter carboxy := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro atom _
    dsimp [adp,carboxy]
    cases owner atp bct atom.origin <;> simp
  have retainedSame : (source.atoms.filter (fun atom => !adp atom)).filter (fun atom => !carboxy atom) =
      retainedAtoms source atp bct := by
    simp only [List.filter_filter,retainedAtoms,adp,carboxy,Bool.and_comm]
  rw [carboxySame,retainedSame] at inner
  simpa only [productAtoms,adp,carboxy,List.append_assoc] using
    ((inner.append_left (source.atoms.filter adp)).trans outer).symm

private theorem after_product_graph (source : Common before step raw) (current : NativeCurrent source)
    (trace : NativeIncidenceTrace source current) (actual : nativeIncidence? source current = .ok trace)
    (atp bct : Nat) (token : trace.selection.bond = ⟨sourceDebit atp,sourceCredit atp bct⟩) :
    trace.after.graph.incidence =
      bondInventory (source.bonds.erase (sourceDebit atp) ++ [sourceCredit atp bct]) := by
  have sourceHeld := (source_token_vertices source current trace.selection.bond trace.selection.bondActual).1
  rw [token] at sourceHeld
  have erased := bond_inventory_erase source.bonds (sourceDebit atp) sourceHeld
  have starts := (native_incidence_starts_full source current trace actual).1
  rw [native_incidence_graph,starts]
  change bondInventory source.bonds+trace.selection.token.incidenceDelta = _
  rw [selected_incidence_delta,token]
  simp only [BondToken.delta,bondInventory,List.map_append,List.sum_append,List.map_cons,
    List.map_nil,List.sum_cons,List.sum_nil,add_zero] at erased ⊢
  rw [erased]
  abel

private theorem after_product_charge (source : Common before step raw) (current : NativeCurrent source)
    (trace : NativeIncidenceTrace source current) (actual : nativeIncidence? source current = .ok trace)
    (atp bct : Nat)
    (donor : trace.selection.token.chargeDonor = .fuel bct .bicarbonate attackingDescriptor)
    (receiver : trace.selection.token.chargeReceiver = .fuel atp .atp leavingDescriptor) :
    trace.after.graph.formalCharge = chargeInventory source.atoms+
      (Finsupp.single (.fuel bct .bicarbonate attackingDescriptor) 1-
        Finsupp.single (.fuel atp .atp leavingDescriptor) 1) := by
  rw [native_incidence_graph,(native_incidence_starts_full source current trace actual).1]
  change chargeInventory source.atoms+trace.selection.token.delta = _
  simp only [ChargedToken.delta,donor,receiver]

private theorem product_bonds_local (source : Common before step raw) (atp bct : Nat)
    (debitHeld : sourceDebit atp ∈ source.bonds) :
    ∀ bond ∈ source.bonds.erase (sourceDebit atp) ++ [sourceCredit atp bct],
      owner atp bct bond.left = owner atp bct bond.right := by
  intro bond held
  rcases List.mem_append.mp held with oldHeld | newHeld
  · apply source_bond_owner source atp bct bond (List.mem_of_mem_erase oldHeld)
    intro same
    subst bond
    exact List.count_eq_zero.mp (source_debit_unique source atp debitHeld) oldHeld
  · have same := List.mem_singleton.mp newHeld
    subst bond
    have phosphorusGamma : gammaAtom phosphorusDescriptor = true := by decide +kernel
    simp [sourceCredit,owner,phosphorusGamma]

structure FirstProducts (source : Common before step raw) (current : NativeCurrent source)
    (trace : NativeIncidenceTrace source current) where
  atp : Nat
  bicarbonate : Nat
  token : trace.selection.bond = ⟨sourceDebit atp,sourceCredit atp bicarbonate⟩
  atomPartition : source.atoms.Perm (productAtoms source atp bicarbonate .adp ++
    productAtoms source atp bicarbonate .carboxyphosphate ++ retainedAtoms source atp bicarbonate)
  incidence : trace.after.graph.incidence =
    bondInventory (source.bonds.erase (sourceDebit atp) ++ [sourceCredit atp bicarbonate])
  charge : trace.after.graph.formalCharge = chargeInventory source.atoms+
    (Finsupp.single (.fuel bicarbonate .bicarbonate attackingDescriptor) 1-
      Finsupp.single (.fuel atp .atp leavingDescriptor) 1)
  localBonds : ∀ bond ∈ source.bonds.erase (sourceDebit atp) ++ [sourceCredit atp bicarbonate],
    owner atp bicarbonate bond.left = owner atp bicarbonate bond.right

theorem native_incidence_first_products (source : Common before step raw) (current : NativeCurrent source) :
    ∃ trace, nativeIncidence? source current = .ok trace ∧ Nonempty (FirstProducts source current trace) := by
  obtain ⟨trace,actual⟩ := native_incidence_source_positive source current
  obtain ⟨atp,bct,token,donor,receiver⟩ := selected_product_token source current trace.selection
  have debitHeld := (source_token_vertices source current trace.selection.bond trace.selection.bondActual).1
  rw [token] at debitHeld
  exact ⟨trace,actual,⟨{
    atp := atp
    bicarbonate := bct
    token := token
    atomPartition := product_atom_partition source atp bct
    incidence := after_product_graph source current trace actual atp bct token
    charge := after_product_charge source current trace actual atp bct donor receiver
    localBonds := product_bonds_local source atp bct debitHeld }⟩⟩

end
end CPS1MaterialIncidence.NativeProducts
