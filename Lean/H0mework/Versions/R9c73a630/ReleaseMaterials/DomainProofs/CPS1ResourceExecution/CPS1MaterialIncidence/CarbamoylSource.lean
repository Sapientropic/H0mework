import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.ActualAmmoniaDynamics
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1EnzymeBath.Partner

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1MaterialIncidence.NativeCarbamoyl
noncomputable section
open CPS1AtomicSource CPS1AtomicDynamics CPS1SameEventFunction CPS1PhosphorylExchange
open NativeProducts NativeSubstitution
open scoped BigOperators

variable {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
  {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
  {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}

def ammoniaHydrogen : Graph.Atom := ammoniaGraph.atoms.get ⟨1,by decide⟩
def carbamateOxygen : Graph.Atom := bicarbonateGraph.atoms.get ⟨3,by decide⟩
def bicarbonateHydrogen : Graph.Atom := bicarbonateGraph.atoms.get ⟨4,by decide⟩

def originalHydrogen (_source : Common before step raw) : AtomOrigin cursor :=
  .prior (.ammonia before.packet.source.ammonia.slot ammoniaHydrogen)

def nitrogenHydrogen (source : Common before step raw) : SourceBond cursor :=
  ⟨ammoniaNitrogen source,originalHydrogen source,"SING",false,"N"⟩

def oxygenHydrogen (bct : Nat) : SourceBond cursor :=
  ⟨.fuel bct .bicarbonate carbamateOxygen,.fuel bct .bicarbonate bicarbonateHydrogen,
    "SING",false,"N"⟩

theorem other_atp (source : Common before step raw) (first : Nat) :
    ∃ second, (FuelKind.atp,second) ∈ raw.fuel.zipIdx ∧ second ≠ first := by
  let entries := raw.fuel.zipIdx.filter (fun entry => entry.1 == .atp)
  let slots := entries.map Prod.snd
  have length : 2 ≤ slots.length := by
    have mapped : (entries.map Prod.fst) = raw.fuel.filter (· == .atp) := by
      change (raw.fuel.zipIdx.filter ((fun x : FuelKind => x == .atp) ∘ Prod.fst)).map Prod.fst = _
      rw [← List.filter_map,List.zipIdx_map_fst]
    have same := congrArg List.length mapped
    simp only [List.length_map] at same
    simpa only [slots,List.length_map,same] using source.atpFuel
  have fullUnique : (raw.fuel.zipIdx.map Prod.snd).Nodup := by
    rw [List.zipIdx_map_snd]
    exact List.nodup_range' _
  have unique : slots.Nodup := fullUnique.sublist (List.filter_sublist.map Prod.snd)
  have zeroLt : 0 < slots.length := by omega
  have oneLt : 1 < slots.length := by omega
  have different : slots[0] ≠ slots[1] := by
    intro same
    have impossible := (List.getElem_inj unique).mp same
    omega
  have selected (second : Nat) (held : second ∈ slots) : (FuelKind.atp,second) ∈ raw.fuel.zipIdx := by
    obtain ⟨entry,entryHeld,same⟩ := List.mem_map.mp held
    have parts := List.mem_filter.mp entryHeld
    have kind : entry.1 = .atp := beq_iff_eq.mp parts.2
    rcases entry with ⟨kind,index⟩
    dsimp only at kind same
    subst kind
    subst second
    exact parts.1
  by_cases zero : slots[0] = first
  · exact ⟨slots[1],selected _ (List.getElem_mem oneLt),by simpa only [← zero] using Ne.symm different⟩
  · exact ⟨slots[0],selected _ (List.getElem_mem zeroLt),zero⟩

theorem source_fuel_occurrence (source : Common before step raw)
    (occurrence : Nat) (kind : FuelKind) (payload : Graph.Atom)
    (held : AtomOrigin.fuel occurrence kind payload ∈ vertices source) :
    (kind,occurrence) ∈ raw.fuel.zipIdx := by
  obtain ⟨atom,atomHeld,origin⟩ := List.mem_map.mp held
  rw [source.atomSource] at atomHeld
  rcases List.mem_append.mp atomHeld with priorHeld | fuelHeld
  · obtain ⟨prior,_,same⟩ := List.mem_map.mp priorHeld
    subst atom
    cases origin
  · obtain ⟨entry,entryHeld,payloadHeld⟩ := List.mem_flatMap.mp fuelHeld
    obtain ⟨original,_,same⟩ := List.mem_map.mp payloadHeld
    subst atom
    have parts := AtomOrigin.fuel.inj origin
    rw [← parts.1,← parts.2.1]
    exact entryHeld

theorem fuel_atom_held (source : Common before step raw)
    (occurrence : Nat) (kind : FuelKind) (payload : Graph.Atom)
    (indexed : (kind,occurrence) ∈ raw.fuel.zipIdx) (held : payload ∈ (fuelGraph kind).atoms) :
    (⟨.fuel occurrence kind payload,payload⟩ : Atom cursor) ∈ source.atoms := by
  rw [source.atomSource]
  exact List.mem_append_right _ (List.mem_flatMap.mpr
    ⟨(kind,occurrence),indexed,List.mem_map.mpr ⟨payload,held,rfl⟩⟩)

theorem ammonia_atom_held (source : Common before step raw)
    (payload : Graph.Atom) (held : payload ∈ ammoniaGraph.atoms) :
    (⟨.prior (.ammonia before.packet.source.ammonia.slot payload),payload⟩ : Atom cursor) ∈ source.atoms := by
  rw [source.atomSource]
  exact List.mem_append_left _ (List.mem_map.mpr
    ⟨.ammonia before.packet.source.ammonia.slot payload,
      List.mem_append_right _ (List.mem_map.mpr ⟨payload,held,rfl⟩),rfl⟩)

theorem fuel_bond_held (source : Common before step raw)
    (occurrence : Nat) (kind : FuelKind) (bond : DescriptorBond)
    (indexed : (kind,occurrence) ∈ raw.fuel.zipIdx)
    (held : bond ∈ descriptorBonds (fuelGraph kind)) : bond.lift (.fuel occurrence kind) ∈ source.bonds := by
  rw [common_bonds_resolved source]
  exact List.mem_append_right _ (List.mem_flatMap.mpr
    ⟨(kind,occurrence),indexed,List.mem_map.mpr ⟨bond,held,rfl⟩⟩)

theorem ammonia_bond_held (source : Common before step raw) : nitrogenHydrogen source ∈ source.bonds := by
  rw [common_bonds_resolved source]
  apply List.mem_append_left
  apply List.mem_append_right
  apply List.mem_map.mpr
  refine ⟨⟨nitrogenDescriptor,ammoniaHydrogen,"SING",false,"N"⟩,?_,rfl⟩
  decide +kernel

inductive SourcePart | chain | ammonia | fuel (occurrence : Nat) (kind : FuelKind)
  deriving DecidableEq

def sourcePart : AtomOrigin cursor → SourcePart
  | .prior (.chain _) => .chain
  | .prior (.ammonia _ _) => .ammonia
  | .fuel occurrence kind _ => .fuel occurrence kind

theorem source_bond_local (source : Common before step raw)
    (bond : SourceBond cursor) (held : bond ∈ source.bonds) : sourcePart bond.left = sourcePart bond.right := by
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
    obtain ⟨descriptor,_,same⟩ := List.mem_map.mp entryHeld
    subst bond
    rfl

theorem find_unique {α : Type} (rows : List α) (predicate : α → Bool) (wanted : α)
    (held : wanted ∈ rows) (selected : predicate wanted = true)
    (unique : ∀ candidate ∈ rows, predicate candidate = true → candidate = wanted) :
    rows.find? predicate = some wanted := by
  cases found : rows.find? predicate with
  | none => exact False.elim ((List.find?_eq_none.mp found) wanted held selected)
  | some actual =>
    have same := unique actual (List.mem_of_find?_eq_some found) (List.find?_some found)
    subst actual
    rfl

theorem source_atom_find (source : Common before step raw) (atom : Atom cursor)
    (held : atom ∈ source.atoms) : source.atoms.find? (fun candidate => candidate.origin == atom.origin) = some atom := by
  apply find_unique _ _ atom held (by simp)
  intro candidate candidateHeld selected
  exact List.inj_on_of_nodup_map (source_vertices_unique source) candidateHeld held (beq_iff_eq.mp selected)

theorem nitrogen_hydrogen_find (source : Common before step raw) :
    sourceHydrogenBond? source (originalHydrogen source) (ammoniaNitrogen source) = some (nitrogenHydrogen source) := by
  have atomHeld := ammonia_atom_held source ammoniaHydrogen (by decide +kernel)
  have atomFound := source_atom_find source _ atomHeld
  have bondFound : source.bonds.find? (fun bond =>
      ((bond.left == ammoniaNitrogen source && bond.right == originalHydrogen source) ||
        (bond.left == originalHydrogen source && bond.right == ammoniaNitrogen source)) && bond.order == "SING") =
      some (nitrogenHydrogen source) := by
    apply find_unique _ _ _ (ammonia_bond_held source) (by simp [nitrogenHydrogen])
    intro bond held selected
    rw [common_bonds_resolved source] at held
    rcases List.mem_append.mp held with priorHeld | fuelHeld
    · rcases List.mem_append.mp priorHeld with chainHeld | ammoniaHeld
      · obtain ⟨descriptor,_,same⟩ := List.mem_map.mp chainHeld
        subst bond
        simp [DescriptorBond.lift,ammoniaNitrogen,originalHydrogen] at selected
      · obtain ⟨descriptor,descriptorHeld,same⟩ := List.mem_map.mp ammoniaHeld
        subst bond
        have unique : (descriptorBonds ammoniaGraph).filter (fun bond =>
            ((bond.left == nitrogenDescriptor && bond.right == ammoniaHydrogen) ||
             (bond.left == ammoniaHydrogen && bond.right == nitrogenDescriptor)) && bond.order == "SING") =
            [⟨nitrogenDescriptor,ammoniaHydrogen,"SING",false,"N"⟩] := by decide +kernel
        have filtered : descriptor ∈ (descriptorBonds ammoniaGraph).filter (fun bond =>
            ((bond.left == nitrogenDescriptor && bond.right == ammoniaHydrogen) ||
             (bond.left == ammoniaHydrogen && bond.right == nitrogenDescriptor)) && bond.order == "SING") := by
          exact List.mem_filter.mpr ⟨descriptorHeld,by simpa [DescriptorBond.lift,ammoniaNitrogen,originalHydrogen] using selected⟩
        rw [unique] at filtered
        rw [List.mem_singleton.mp filtered]
        rfl
    · obtain ⟨entry,_,entryHeld⟩ := List.mem_flatMap.mp fuelHeld
      obtain ⟨descriptor,_,same⟩ := List.mem_map.mp entryHeld
      subst bond
      simp [DescriptorBond.lift,ammoniaNitrogen,originalHydrogen] at selected
  simp only [sourceHydrogenBond?,originalHydrogen,atomFound]
  exact bondFound

theorem oxygen_hydrogen_find (source : Common before step raw) (bct : Nat)
    (indexed : (FuelKind.bicarbonate,bct) ∈ raw.fuel.zipIdx) :
    sourceHydrogenBond? source (.fuel bct .bicarbonate bicarbonateHydrogen)
      (.fuel bct .bicarbonate carbamateOxygen) = some (oxygenHydrogen bct) := by
  have atomHeld := fuel_atom_held source bct .bicarbonate bicarbonateHydrogen indexed (by decide +kernel)
  have atomFound := source_atom_find source _ atomHeld
  have bondHeld : oxygenHydrogen (cursor := cursor) bct ∈ source.bonds :=
    fuel_bond_held source bct .bicarbonate
      ⟨carbamateOxygen,bicarbonateHydrogen,"SING",false,"N"⟩ indexed (by decide +kernel)
  have bondFound : source.bonds.find? (fun bond =>
      ((bond.left == .fuel bct .bicarbonate carbamateOxygen && bond.right == .fuel bct .bicarbonate bicarbonateHydrogen) ||
        (bond.left == .fuel bct .bicarbonate bicarbonateHydrogen && bond.right == .fuel bct .bicarbonate carbamateOxygen)) &&
        bond.order == "SING") = some (oxygenHydrogen bct) := by
    apply find_unique _ _ _ bondHeld (by simp [oxygenHydrogen])
    intro bond held selected
    rw [common_bonds_resolved source] at held
    rcases List.mem_append.mp held with priorHeld | fuelHeld
    · rcases List.mem_append.mp priorHeld with chainHeld | ammoniaHeld
      · obtain ⟨descriptor,_,same⟩ := List.mem_map.mp chainHeld
        subst bond
        simp [DescriptorBond.lift] at selected
      · obtain ⟨descriptor,_,same⟩ := List.mem_map.mp ammoniaHeld
        subst bond
        simp [DescriptorBond.lift] at selected
    · obtain ⟨entry,_,entryHeld⟩ := List.mem_flatMap.mp fuelHeld
      obtain ⟨descriptor,descriptorHeld,same⟩ := List.mem_map.mp entryHeld
      subst bond
      have parts : ((entry.2 = bct ∧ entry.1 = .bicarbonate ∧ descriptor.left = carbamateOxygen ∧
          descriptor.right = bicarbonateHydrogen) ∨
        (entry.2 = bct ∧ entry.1 = .bicarbonate ∧ descriptor.left = bicarbonateHydrogen ∧
          descriptor.right = carbamateOxygen)) ∧ descriptor.order = "SING" := by
        simpa [DescriptorBond.lift,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq,AtomOrigin.fuel.injEq,
          and_assoc,and_left_comm,and_comm] using selected
      have entryEq : entry = (.bicarbonate,bct) := by
        rcases parts.1 with ⟨index,kind,_,_⟩ | ⟨index,kind,_,_⟩ <;> exact Prod.ext kind index
      subst entry
      have filtered : descriptor ∈ (descriptorBonds bicarbonateGraph).filter (fun bond =>
          ((bond.left == carbamateOxygen && bond.right == bicarbonateHydrogen) ||
            (bond.left == bicarbonateHydrogen && bond.right == carbamateOxygen)) && bond.order == "SING") := by
        refine List.mem_filter.mpr ⟨descriptorHeld,?_⟩
        simpa only [DescriptorBond.lift,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq,AtomOrigin.fuel.injEq,
          true_and] using selected
      have unique : (descriptorBonds bicarbonateGraph).filter (fun bond =>
          ((bond.left == carbamateOxygen && bond.right == bicarbonateHydrogen) ||
            (bond.left == bicarbonateHydrogen && bond.right == carbamateOxygen)) && bond.order == "SING") =
          [⟨carbamateOxygen,bicarbonateHydrogen,"SING",false,"N"⟩] := by decide +kernel
      rw [unique] at filtered
      rw [List.mem_singleton.mp filtered]
      rfl
  simp only [sourceHydrogenBond?,atomFound]
  exact bondFound

structure CarbamoylSites (source : Common before step raw) (current : NativeCurrent source)
    (material : NativeAmmoniaSubstitution source current) where
  atp : Nat
  indexed : (FuelKind.atp,atp) ∈ raw.fuel.zipIdx
  fresh : atp ≠ material.products.atp
  bicarbonateIndexed : (FuelKind.bicarbonate,material.products.bicarbonate) ∈ raw.fuel.zipIdx

theorem source_carbamoyl_sites (source : Common before step raw) (current : NativeCurrent source)
    (material : NativeAmmoniaSubstitution source current) : Nonempty (CarbamoylSites source current material) := by
  obtain ⟨atp,indexed,fresh⟩ := other_atp source material.products.atp
  have oxygenHeld := (source_token_vertices source current material.trace.selection.bond material.trace.selection.bondActual).2.2.2.2
  rw [material.products.token] at oxygenHeld
  exact ⟨⟨atp,indexed,fresh,source_fuel_occurrence source material.products.bicarbonate .bicarbonate attackingDescriptor oxygenHeld⟩⟩

def protonInstruction (source : Common before step raw) (bct : Nat) : ChargedInstruction cursor :=
  .proton (originalHydrogen source) (ammoniaNitrogen source) (.fuel bct .bicarbonate attackingDescriptor)

def protonToken (source : Common before step raw) (bct : Nat) : ChargedToken cursor :=
  ⟨.fuel bct .bicarbonate attackingDescriptor,ammoniaNitrogen source,
    some ⟨nitrogenHydrogen source,some ⟨.fuel bct .bicarbonate attackingDescriptor,
      originalHydrogen source,"SING",false,"N"⟩⟩⟩

def deprotonateInstruction (bct : Nat) : ChargedInstruction cursor :=
  .deprotonate (.fuel bct .bicarbonate bicarbonateHydrogen) (.fuel bct .bicarbonate carbamateOxygen)

def deprotonateToken (bct : Nat) : ChargedToken cursor :=
  ⟨.fuel bct .bicarbonate bicarbonateHydrogen,.fuel bct .bicarbonate carbamateOxygen,
    some ⟨oxygenHydrogen bct,none⟩⟩

def phosphorylationCredit (atp bct : Nat) : SourceBond cursor :=
  ⟨.fuel atp .atp phosphorusDescriptor,.fuel bct .bicarbonate carbamateOxygen,"SING",false,"STEREONONE"⟩

def phosphorylationToken (atp bct : Nat) : ChargedToken cursor :=
  ⟨.fuel bct .bicarbonate carbamateOxygen,.fuel atp .atp leavingDescriptor,
    some ⟨sourceDebit atp,some (phosphorylationCredit atp bct)⟩⟩

theorem proton_prepared (source : Common before step raw) (bct : Nat) :
    prepareCharged? source (protonInstruction source bct) = some (protonToken source bct) := by
  rw [protonInstruction,charged_proton_data,nitrogen_hydrogen_find]
  rfl

theorem deprotonate_prepared (source : Common before step raw) (bct : Nat)
    (indexed : (FuelKind.bicarbonate,bct) ∈ raw.fuel.zipIdx) :
    prepareCharged? source (deprotonateInstruction bct) = some (deprotonateToken bct) := by
  rw [deprotonateInstruction,charged_deprotonate_data,oxygen_hydrogen_find source bct indexed]
  rfl

theorem inventory_nonnegative (bonds : List (SourceBond cursor)) (bond : SourceBond cursor) :
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

theorem inventory_paid (bonds : List (SourceBond cursor)) (bond : SourceBond cursor)
    (held : bond ∈ bonds) : 1 ≤ bondInventory bonds bond := by
  classical
  induction bonds with
  | nil => simp only [List.not_mem_nil] at held
  | cons first rest ih =>
    change 1 ≤ (Finsupp.single first 1 : Incidence cursor) bond+bondInventory rest bond
    rcases List.mem_cons.mp held with same | restHeld
    · subst bond
      simp only [Finsupp.single_eq_same]
      have nonnegative := inventory_nonnegative rest first
      omega
    · have tail := ih restHeld
      by_cases same : first = bond
      · simp only [same,Finsupp.single_eq_same]
        omega
      · simp only [Finsupp.single_apply,if_neg same,zero_add]
        exact tail

theorem inventory_absent (bonds : List (SourceBond cursor)) (bond : SourceBond cursor)
    (absent : bond ∉ bonds) : bondInventory bonds bond = 0 := by
  classical
  induction bonds with
  | nil => simp [bondInventory]
  | cons first rest ih =>
    have conditions : bond ≠ first ∧ bond ∉ rest := by simpa only [List.mem_cons,not_or] using absent
    change (Finsupp.single first 1 : Incidence cursor) bond+bondInventory rest bond = 0
    simp only [Finsupp.single_apply,if_neg (Ne.symm conditions.1),ih conditions.2,add_zero]

theorem inventory_erase (bonds : List (SourceBond cursor)) (bond : SourceBond cursor)
    (held : bond ∈ bonds) : bondInventory (bonds.erase bond) = bondInventory bonds-Finsupp.single bond 1 := by
  classical
  have erased := List.sum_map_erase (fun edge : SourceBond cursor => (Finsupp.single edge 1 : Incidence cursor)) held
  change Finsupp.single bond 1+bondInventory (bonds.erase bond) = bondInventory bonds at erased
  exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using erased)

def bondAfter (bonds : List (SourceBond cursor)) (action : SourceBondAction cursor) : List (SourceBond cursor) :=
  bonds.erase action.debit ++ action.credit.toList

theorem record_normal {source : Common before step raw} {current : NativeCurrent source}
    (state : ChargedState source current) (token : ChargedToken cursor) (bonds : List (SourceBond cursor))
    (normal : state.graph.incidence = bondInventory bonds) (action : SourceBondAction cursor)
    (selected : token.bond = some action) (held : action.debit ∈ bonds) :
    (state.record token).graph.incidence = bondInventory (bondAfter bonds action) := by
  rw [charged_record_graph]
  change state.graph.incidence+token.incidenceDelta = _
  rw [normal]
  simp only [ChargedToken.incidenceDelta,selected,Option.toList_some,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,bondAfter,bondInventory,List.map_append,List.sum_append]
  change bondInventory bonds+action.delta = bondInventory (bonds.erase action.debit)+_
  rw [inventory_erase bonds action.debit held]
  unfold SourceBondAction.delta
  abel

theorem record_electrons {source : Common before step raw} {current : NativeCurrent source}
    (state : ChargedState source current) (token : ChargedToken cursor) (origin : AtomOrigin cursor) :
    electronInventory source (state.record token).graph origin =
      electronInventory source state.graph origin-token.delta origin := by
  rw [charged_record_graph]
  simp only [electronInventory,applyChargedToken,Finsupp.add_apply]
  ring

def substitutionBonds (source : Common before step raw) {current : NativeCurrent source}
    (material : NativeAmmoniaSubstitution source current) :
    List (SourceBond cursor) :=
  bondAfter (source.bonds.erase (sourceDebit material.products.atp) ++
    [sourceCredit material.products.atp material.products.bicarbonate])
    ⟨carbamateDebit material.products.bicarbonate,some (carbamateCredit source material.products.bicarbonate)⟩

theorem substitution_normal (source : Common before step raw) (current : NativeCurrent source)
    (material : NativeAmmoniaSubstitution source current) :
    material.event.after.graph.incidence = bondInventory (substitutionBonds source material) := by
  have held : carbamateDebit material.products.bicarbonate ∈
      source.bonds.erase (sourceDebit material.products.atp) ++ [sourceCredit material.products.atp material.products.bicarbonate] := by
    by_contra absent
    have paid := material.event.debitPaid (carbamateDebit material.products.bicarbonate)
      (by simp [carbamateToken,ChargedToken.debits])
    rw [material.products.incidence,inventory_absent _ _ absent] at paid
    omega
  exact record_normal material.trace.after (carbamateToken source material.products.bicarbonate) _
    material.products.incidence _ rfl held

theorem substitution_electrons (source : Common before step raw) (current : NativeCurrent source)
    (material : NativeAmmoniaSubstitution source current) (origin : AtomOrigin cursor) :
    electronInventory source material.event.after.graph origin =
      electronInventory source (sourceGraph source) origin-
        (Finsupp.single (.fuel material.products.bicarbonate .bicarbonate attackingDescriptor) 1-
          Finsupp.single (.fuel material.products.atp .atp leavingDescriptor) 1 : Charges cursor) origin-
        (carbamateToken source material.products.bicarbonate).delta origin := by
  change electronInventory source
    (material.trace.after.record (carbamateToken source material.products.bicarbonate)).graph origin = _
  rw [record_electrons]
  simp only [electronInventory,material.products.charge,Finsupp.add_apply,sourceGraph]
  ring

theorem substitution_spent (source : Common before step raw) (current : NativeCurrent source)
    (material : NativeAmmoniaSubstitution source current) :
    material.event.after.spent = [sourceDebit material.products.atp,carbamateDebit material.products.bicarbonate] := by
  rw [material.spent,NativeIncidenceTrace.after,charged_record_spent,
    (native_incidence_starts_full source current material.trace material.firstActual).2]
  simp only [List.nil_append,IncidenceSelection.token,material.products.token,ChargedToken.debits,
    Option.toList_some,List.map_cons,List.map_nil,List.singleton_append]

def SamePair (bond target : SourceBond cursor) : Prop :=
  (bond.left = target.left ∧ bond.right = target.right) ∨
    (bond.left = target.right ∧ bond.right = target.left)

theorem source_cross_absent (source : Common before step raw) (credit : SourceBond cursor)
    (different : sourcePart credit.left ≠ sourcePart credit.right) :
    ∀ bond ∈ source.bonds, ¬ SamePair bond credit := by
  intro bond held ends
  have locality := source_bond_local source bond held
  rcases ends with ⟨left,right⟩ | ⟨left,right⟩
  · exact different (left ▸ right ▸ locality)
  · exact different (left ▸ right ▸ locality.symm)

theorem substitution_support (source : Common before step raw) (current : NativeCurrent source)
    (material : NativeAmmoniaSubstitution source current) (bond : SourceBond cursor)
    (held : bond ∈ substitutionBonds source material) :
    bond ∈ source.bonds ∨ bond = sourceCredit material.products.atp material.products.bicarbonate ∨
      bond = carbamateCredit source material.products.bicarbonate := by
  rcases List.mem_append.mp held with oldHeld | credited
  · have beforeHeld := List.mem_of_mem_erase oldHeld
    rcases List.mem_append.mp beforeHeld with sourceHeld | firstCredit
    · exact Or.inl (List.mem_of_mem_erase sourceHeld)
    · exact Or.inr (Or.inl (List.mem_singleton.mp firstCredit))
  · exact Or.inr (Or.inr (List.mem_singleton.mp credited))

theorem bond_after_support (bonds : List (SourceBond cursor)) (action : SourceBondAction cursor)
    (bond : SourceBond cursor) (held : bond ∈ bondAfter bonds action) :
    bond ∈ bonds ∨ bond ∈ action.credit.toList := by
  rcases List.mem_append.mp held with old | fresh
  · exact Or.inl (List.mem_of_mem_erase old)
  · exact Or.inr fresh

theorem pair_free {atoms : List (Atom cursor)} (graph : OriginGraph atoms)
    (bonds : List (SourceBond cursor)) (normal : graph.incidence = bondInventory bonds)
    (credit : SourceBond cursor) (absent : ∀ bond ∈ bonds, ¬ SamePair bond credit) :
    graph.incidence credit = 0 ∧ adjacent graph credit.left credit.right = false := by
  have missing : credit ∉ bonds := fun held => absent credit held (Or.inl ⟨rfl,rfl⟩)
  refine ⟨normal ▸ inventory_absent bonds credit missing,?_⟩
  apply Bool.eq_false_iff.mpr
  intro occupied
  obtain ⟨bond,bondHeld,checked⟩ := List.any_eq_true.mp occupied
  have parts : decide (0 < graph.incidence bond) = true ∧
      ((bond.left == credit.left && bond.right == credit.right) ||
        (bond.left == credit.right && bond.right == credit.left)) = true := by
    simpa only [Bool.and_eq_true] using checked
  have present : bond ∈ bonds := by
    by_contra missing
    have positive := of_decide_eq_true parts.1
    rw [normal,inventory_absent bonds bond missing] at positive
    omega
  apply absent bond present
  simpa only [SamePair,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] using parts.2

structure TokenStep {source : Common before step raw} {current : NativeCurrent source}
    (state : ChargedState source current) (token : ChargedToken cursor) : Type where
  safe : token.safe source
  ready : electronReady source state.graph
  electronPaid : 1 ≤ electronInventory source state.graph token.chargeDonor
  unused : ∀ bond ∈ token.debits, bond ∉ state.spent
  debitPaid : ∀ bond ∈ token.debits, 1 ≤ state.graph.incidence bond
  creditFree : ∀ bond ∈ token.credits, state.graph.incidence bond = 0
  pairFree : ∀ bond ∈ token.credits, adjacent state.graph bond.left bond.right = false

def tokenStep? {source : Common before step raw} {current : NativeCurrent source}
    (state : ChargedState source current) (token : ChargedToken cursor) :
    Except (NativeIncidenceResidual cursor) (TokenStep state token) := by
  classical
  exact if safe : token.safe source then
    if ready : electronReady source state.graph then
      if paid : 1 ≤ electronInventory source state.graph token.chargeDonor then
        if unused : ∀ bond ∈ token.debits, bond ∉ state.spent then
          if debit : ∀ bond ∈ token.debits, 1 ≤ state.graph.incidence bond then
            if credit : ∀ bond ∈ token.credits, state.graph.incidence bond = 0 then
              if pair : ∀ bond ∈ token.credits, adjacent state.graph bond.left bond.right = false then
                .ok ⟨safe,ready,paid,unused,debit,credit,pair⟩
              else .error .occupiedAtomPair
            else .error .occupiedBond
          else .error .bondShortage
        else .error .reusedSourceBond
      else .error (.electronShortage token.chargeDonor (electronInventory source state.graph token.chargeDonor))
    else .error .negativeElectronResource
  else .error .unsafeSourceToken

def TokenStep.after {source : Common before step raw} {current : NativeCurrent source}
    {state : ChargedState source current} {token : ChargedToken cursor} (_event : TokenStep state token) :
    ChargedState source current := state.record token

def TokenStep.charged {source : Common before step raw} {current : NativeCurrent source}
    {state : ChargedState source current} {token : ChargedToken cursor} (event : TokenStep state token)
    (instruction : ChargedInstruction cursor) (prepared : prepareCharged? source instruction = some token) :
    SourceChargedStep source current :=
  ⟨state,instruction,token,prepared,event.safe,event.ready,event.electronPaid,event.unused,event.debitPaid,event.creditFree,event.pairFree⟩

theorem TokenStep.checked {source : Common before step raw} {current : NativeCurrent source}
    {state : ChargedState source current} {token : ChargedToken cursor} (event : TokenStep state token) :
    tokenStep? state token = .ok event := by
  simp only [tokenStep?,dif_pos event.safe,dif_pos event.ready,dif_pos event.electronPaid,
    dif_pos event.unused,dif_pos event.debitPaid,dif_pos event.creditFree,dif_pos event.pairFree]

theorem TokenStep.charged_checked {source : Common before step raw} {current : NativeCurrent source}
    {state : ChargedState source current} {token : ChargedToken cursor} (event : TokenStep state token)
    (instruction : ChargedInstruction cursor) (prepared : prepareCharged? source instruction = some token) :
    stepCharged? source current state instruction = .ok (event.charged instruction prepared) := by
  unfold stepCharged?
  split
  · rename_i unresolved
    rw [prepared] at unresolved
    cases unresolved
  · rename_i selected resolution
    have same : selected = token := Option.some.inj (resolution.symm.trans prepared)
    subst selected
    simp only [dif_pos event.safe,dif_pos event.ready,dif_pos event.electronPaid,
      dif_pos event.unused,dif_pos event.debitPaid,dif_pos event.creditFree,dif_pos event.pairFree]
    rfl

theorem TokenStep.ready_after {source : Common before step raw} {current : NativeCurrent source}
    {state : ChargedState source current} {token : ChargedToken cursor} (event : TokenStep state token) :
    electronReady source event.after.graph := by
  intro origin held
  rw [TokenStep.after,record_electrons]
  by_cases donor : origin = token.chargeDonor
  · subst origin
    simp only [ChargedToken.delta,Finsupp.sub_apply,Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne event.safe.2.2.1,sub_zero]
    exact sub_nonneg.mpr event.electronPaid
  · by_cases receiver : origin = token.chargeReceiver
    · subst origin
      simp only [ChargedToken.delta,Finsupp.sub_apply,
        Finsupp.single_eq_of_ne (Ne.symm event.safe.2.2.1),Finsupp.single_eq_same,zero_sub,sub_neg_eq_add]
      have prior := event.ready _ held
      omega
    · simp only [ChargedToken.delta,Finsupp.sub_apply,Finsupp.single_eq_of_ne donor,
        Finsupp.single_eq_of_ne receiver,sub_self,sub_zero]
      exact event.ready origin held

theorem TokenStep.normal_after {source : Common before step raw} {current : NativeCurrent source}
    {state : ChargedState source current} {token : ChargedToken cursor} (event : TokenStep state token)
    (bonds : List (SourceBond cursor)) (normal : state.graph.incidence = bondInventory bonds)
    (action : SourceBondAction cursor) (selected : token.bond = some action) :
    event.after.graph.incidence = bondInventory (bondAfter bonds action) := by
  apply record_normal state token bonds normal action selected
  by_contra missing
  have paid := event.debitPaid action.debit (by simp [ChargedToken.debits,selected])
  rw [normal,inventory_absent bonds action.debit missing] at paid
  omega

end
end CPS1MaterialIncidence.NativeCarbamoyl
