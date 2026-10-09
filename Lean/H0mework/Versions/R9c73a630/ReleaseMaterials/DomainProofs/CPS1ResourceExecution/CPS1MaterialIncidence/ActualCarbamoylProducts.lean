import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.CarbamoylSerial

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

theorem lift_fuel_injective (occurrence : Nat) (kind : FuelKind) :
    Function.Injective (DescriptorBond.lift (AtomOrigin.fuel (cursor := cursor) occurrence kind)) := by
  intro first second same
  cases first
  cases second
  simpa only [DescriptorBond.lift,SourceBond.mk.injEq,AtomOrigin.fuel.injEq,
    DescriptorBond.mk.injEq,true_and] using same

theorem fuel_bond_count_bound (wanted occurrence : Nat) (wantedKind kind : FuelKind) (bond : DescriptorBond) :
    (resolvedBonds (fuelGraph kind) (AtomOrigin.fuel (cursor := cursor) occurrence kind)).count
      (bond.lift (.fuel wanted wantedKind)) ≤ if occurrence == wanted then 1 else 0 := by
  classical
  by_cases same : occurrence = wanted
  · subst occurrence
    simp only [beq_self_eq_true,ite_true]
    by_cases sameKind : kind = wantedKind
    · subst kind
      rw [resolvedBonds,List.count_map_of_injective _ _ (lift_fuel_injective wanted wantedKind)]
      have unique : (descriptorBonds (fuelGraph wantedKind)).Nodup := by
        cases wantedKind <;> decide +kernel
      exact List.nodup_iff_count_le_one.mp unique bond
    · have absent : bond.lift (AtomOrigin.fuel (cursor := cursor) wanted wantedKind) ∉
          resolvedBonds (fuelGraph kind) (.fuel wanted kind) := by
        intro held
        obtain ⟨descriptor,_,actual⟩ := List.mem_map.mp held
        have left := congrArg SourceBond.left actual
        exact sameKind (AtomOrigin.fuel.inj left).2.1
      rw [List.count_eq_zero.mpr absent]
      exact Nat.zero_le _
  · have absent : bond.lift (AtomOrigin.fuel (cursor := cursor) wanted wantedKind) ∉
        resolvedBonds (fuelGraph kind) (.fuel occurrence kind) := by
      intro held
      obtain ⟨descriptor,_,actual⟩ := List.mem_map.mp held
      exact same (AtomOrigin.fuel.inj (congrArg SourceBond.left actual)).1
    rw [List.count_eq_zero.mpr absent]
    simp [same]

theorem fuels_bond_count_bound (entries : List (FuelKind × Nat)) (wanted : Nat)
    (kind : FuelKind) (bond : DescriptorBond) :
    (entries.flatMap (fun entry => resolvedBonds (fuelGraph entry.1)
      (AtomOrigin.fuel (cursor := cursor) entry.2 entry.1))).count (bond.lift (.fuel wanted kind)) ≤
        (entries.map Prod.snd).count wanted := by
  induction entries with
  | nil => simp
  | cons entry rest ih =>
    simp only [List.flatMap_cons,List.count_append,List.map_cons,List.count_cons]
    simpa only [Nat.add_comm] using Nat.add_le_add (fuel_bond_count_bound wanted entry.2 kind entry.1 bond) ih

theorem fuel_bond_not_prior (graph : Graph.Molecule) (prior : Graph.Atom → Classical.AtomOrigin cursor)
    (wanted : Nat) (kind : FuelKind) (bond : DescriptorBond) :
    bond.lift (.fuel wanted kind) ∉ resolvedBonds graph (fun atom => .prior (prior atom)) := by
  intro held
  obtain ⟨descriptor,_,same⟩ := List.mem_map.mp held
  have left := congrArg SourceBond.left same
  change AtomOrigin.prior (prior descriptor.left) = .fuel wanted kind bond.left at left
  cases left

theorem source_fuel_bond_once (source : Common before step raw) (wanted : Nat) (kind : FuelKind)
    (bond : DescriptorBond) (indexed : (kind,wanted) ∈ raw.fuel.zipIdx)
    (present : bond ∈ descriptorBonds (fuelGraph kind)) : source.bonds.count (bond.lift (.fuel wanted kind)) = 1 := by
  have bound : source.bonds.count (bond.lift (.fuel wanted kind)) ≤ 1 := by
    rw [common_bonds_resolved source,List.count_append,List.count_append,
      List.count_eq_zero.mpr (fuel_bond_not_prior _ _ wanted kind bond),
      List.count_eq_zero.mpr (fuel_bond_not_prior _ _ wanted kind bond),Nat.zero_add]
    apply (fuels_bond_count_bound raw.fuel.zipIdx wanted kind bond).trans
    have unique : (raw.fuel.zipIdx.map Prod.snd).Nodup := by
      rw [List.zipIdx_map_snd]
      exact List.nodup_range' _
    exact List.nodup_iff_count_le_one.mp unique wanted
  have positive := List.count_pos_iff.mpr (fuel_bond_held source wanted kind bond indexed present)
  omega

theorem ammonia_hydrogen_once (source : Common before step raw) : source.bonds.count (nitrogenHydrogen source) = 1 := by
  have chainAbsent : nitrogenHydrogen source ∉ resolvedBonds before.packet.source.graph (fun atom => .prior (.chain atom)) := by
    intro held
    obtain ⟨descriptor,_,same⟩ := List.mem_map.mp held
    have left := congrArg SourceBond.left same
    simp [DescriptorBond.lift,nitrogenHydrogen,ammoniaNitrogen] at left
  have fuelAbsent : nitrogenHydrogen source ∉ raw.fuel.zipIdx.flatMap
      (fun entry => resolvedBonds (fuelGraph entry.1) (.fuel entry.2 entry.1)) := by
    intro held
    obtain ⟨entry,_,entryHeld⟩ := List.mem_flatMap.mp held
    obtain ⟨descriptor,_,same⟩ := List.mem_map.mp entryHeld
    have left := congrArg SourceBond.left same
    simp [DescriptorBond.lift,nitrogenHydrogen,ammoniaNitrogen] at left
  have injective : Function.Injective (DescriptorBond.lift
      (fun atom => AtomOrigin.prior (.ammonia before.packet.source.ammonia.slot atom))) := by
    intro first second same
    cases first
    cases second
    simpa only [DescriptorBond.lift,SourceBond.mk.injEq,AtomOrigin.prior.injEq,
      Classical.AtomOrigin.ammonia.injEq,DescriptorBond.mk.injEq,true_and] using same
  rw [common_bonds_resolved source,List.count_append,List.count_append,
    List.count_eq_zero.mpr chainAbsent,List.count_eq_zero.mpr fuelAbsent,Nat.zero_add,Nat.add_zero]
  change ((descriptorBonds ammoniaGraph).map (DescriptorBond.lift
    (fun atom => .prior (.ammonia before.packet.source.ammonia.slot atom)))).count
    (DescriptorBond.lift (fun atom => .prior (.ammonia before.packet.source.ammonia.slot atom))
      ⟨nitrogenDescriptor,ammoniaHydrogen,"SING",false,"N"⟩) = 1
  rw [List.count_map_of_injective _ _ injective]
  decide +kernel

inductive FinalOwner
  | chain | firstADP | secondADP | carbamoylPhosphate | phosphate | proton
  | retainedFuel (occurrence : Nat) (kind : FuelKind)
  deriving DecidableEq

def finalOwner (first second bct : Nat) : AtomOrigin cursor → FinalOwner
  | .prior (.chain _) => .chain
  | .prior (.ammonia _ atom) => if atom == ammoniaHydrogen then .phosphate else .carbamoylPhosphate
  | .fuel occurrence kind atom =>
    if occurrence = first ∧ kind = .atp then
      if gammaAtom atom then .phosphate else .firstADP
    else if occurrence = second ∧ kind = .atp then
      if gammaAtom atom then .carbamoylPhosphate else .secondADP
    else if occurrence = bct ∧ kind = .bicarbonate then
      if atom == bicarbonateHydrogen then .proton
      else if atom == attackingDescriptor then .phosphate else .carbamoylPhosphate
    else .retainedFuel occurrence kind

def finalAtoms {source : Common before step raw} {current : NativeCurrent source}
    {material : NativeAmmoniaSubstitution source current} (serial : CarbamoylSerial source current material)
    (part : FinalOwner) : List (Atom cursor) :=
  source.atoms.filter (fun atom => finalOwner material.products.atp serial.sites.atp material.products.bicarbonate atom.origin == part)

def finalBonds {source : Common before step raw} {current : NativeCurrent source}
    {material : NativeAmmoniaSubstitution source current} (serial : CarbamoylSerial source current material)
    (part : FinalOwner) : List (SourceBond cursor) :=
  serial.bonds.filter (fun bond =>
    finalOwner material.products.atp serial.sites.atp material.products.bicarbonate bond.left == part &&
    finalOwner material.products.atp serial.sites.atp material.products.bicarbonate bond.right == part)

@[simp] theorem first_gamma_cp (flag : Bool) :
    ((if flag then FinalOwner.phosphate else .firstADP) == .carbamoylPhosphate) = false := by
  cases flag <;> rfl

@[simp] theorem second_gamma_cp (flag : Bool) :
    ((if flag then FinalOwner.carbamoylPhosphate else .secondADP) == .carbamoylPhosphate) = flag := by
  cases flag <;> rfl

@[simp] theorem ammonia_cp (atom : Graph.Atom) :
    ((if atom == ammoniaHydrogen then FinalOwner.phosphate else .carbamoylPhosphate) == .carbamoylPhosphate) =
      !(atom == ammoniaHydrogen) := by
  cases (atom == ammoniaHydrogen) <;> rfl

@[simp] theorem bicarbonate_cp (atom : Graph.Atom) :
    ((if atom == bicarbonateHydrogen then FinalOwner.proton else
      if atom == attackingDescriptor then .phosphate else .carbamoylPhosphate) == .carbamoylPhosphate) =
      (!(atom == bicarbonateHydrogen) && !(atom == attackingDescriptor)) := by
  cases (atom == bicarbonateHydrogen) <;> cases (atom == attackingDescriptor) <;> rfl

def partitionAtoms {α : Type} [DecidableEq α] (owner : Atom cursor → α) :
    List (Atom cursor) → List α → List (Atom cursor)
  | atoms,[] => atoms
  | atoms,part :: parts => atoms.filter (fun atom => owner atom == part) ++
      partitionAtoms owner (atoms.filter (fun atom => !(owner atom == part))) parts

theorem partition_atoms_perm {α : Type} [DecidableEq α] (owner : Atom cursor → α)
    (atoms : List (Atom cursor)) (parts : List α) : atoms.Perm (partitionAtoms owner atoms parts) := by
  induction parts generalizing atoms with
  | nil => exact List.Perm.refl _
  | cons part parts ih =>
    exact (List.filter_append_perm (fun atom => owner atom == part) atoms).symm.trans
      ((ih (atoms.filter (fun atom => !(owner atom == part)))).append_left _)

def completePartition {source : Common before step raw} {current : NativeCurrent source}
    {material : NativeAmmoniaSubstitution source current} (serial : CarbamoylSerial source current material) : List (Atom cursor) :=
  partitionAtoms (fun atom => finalOwner material.products.atp serial.sites.atp material.products.bicarbonate atom.origin)
    source.atoms [.firstADP,.secondADP,.carbamoylPhosphate,.phosphate,.proton]

theorem complete_partition {source : Common before step raw} {current : NativeCurrent source}
    {material : NativeAmmoniaSubstitution source current} (serial : CarbamoylSerial source current material) :
    source.atoms.Perm (completePartition serial) := partition_atoms_perm _ _ _

theorem serial_charge {source : Common before step raw} {current : NativeCurrent source}
    {material : NativeAmmoniaSubstitution source current} (serial : CarbamoylSerial source current material) :
    serial.after.graph.formalCharge = material.event.after.graph.formalCharge+
      (protonToken source material.products.bicarbonate).delta+
      (deprotonateToken material.products.bicarbonate).delta+
      (phosphorylationToken serial.sites.atp material.products.bicarbonate).delta := by
  simp only [CarbamoylSerial.after,TokenStep.after,charged_record_graph,applyChargedToken]

theorem origin_sum_absent (atoms : List (Atom cursor)) (weight : Atom cursor → ℤ)
    (origin : AtomOrigin cursor) (absent : origin ∉ atoms.map Atom.origin) :
    ((atoms.map (fun atom => Finsupp.single atom.origin (weight atom))).sum : Charges cursor) origin = 0 := by
  classical
  induction atoms with
  | nil => simp
  | cons atom rest ih =>
    simp only [List.map_cons,List.mem_cons,not_or] at absent
    simp only [List.map_cons,List.sum_cons,Finsupp.add_apply,Finsupp.single_apply,
      if_neg (Ne.symm absent.1),ih absent.2,add_zero]

theorem origin_sum_selected (atoms : List (Atom cursor)) (weight : Atom cursor → ℤ)
    (unique : (atoms.map Atom.origin).Nodup) (atom : Atom cursor) (held : atom ∈ atoms) :
    ((atoms.map (fun other => Finsupp.single other.origin (weight other))).sum : Charges cursor) atom.origin = weight atom := by
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
      simp only [List.map_cons,List.sum_cons,Finsupp.add_apply,Finsupp.single_apply,if_neg different,zero_add]
      exact ih nodup.2 restHeld

theorem initial_atom_charge (source : Common before step raw) (atom : Atom cursor) (held : atom ∈ source.atoms) :
    (sourceGraph source).formalCharge atom.origin = atom.descriptor.source.charge := by
  exact origin_sum_selected source.atoms _ (source_vertices_unique source) atom held

theorem two_flatMap {α β : Type} [DecidableEq α] (rows : List α) (first second : α)
    (firstHeld : first ∈ rows) (secondHeld : second ∈ rows) (different : first ≠ second)
    (unique : rows.Nodup) (f : α → List β)
    (other : ∀ entry ∈ rows, entry ≠ first → entry ≠ second → f entry = []) :
    (rows.flatMap f).Perm (f first ++ f second) := by
  have secondRemaining : second ∈ rows.erase first := (List.mem_erase_of_ne (Ne.symm different)).mpr secondHeld
  have firstAbsent : first ∉ rows.erase first := unique.not_mem_erase
  have secondAbsent : second ∉ (rows.erase first).erase second := (unique.erase first).not_mem_erase
  have remaining : ((rows.erase first).erase second).flatMap f = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro entry held
    have prior := List.mem_of_mem_erase held
    apply other entry (List.mem_of_mem_erase prior)
    · intro same
      exact firstAbsent (same ▸ prior)
    · intro same
      exact secondAbsent (same ▸ held)
  have splitFirst := (List.perm_cons_erase firstHeld).flatMap_right f
  have splitSecond := (List.perm_cons_erase secondRemaining).flatMap_right f
  simp only [List.flatMap_cons,remaining,List.append_nil] at splitSecond
  exact splitFirst.trans (splitSecond.append_left (f first))

theorem fuel_entries_unique (fuel : List FuelKind) : fuel.zipIdx.Nodup := by
  apply List.Nodup.of_map Prod.snd
  rw [List.zipIdx_map_snd]
  exact List.nodup_range' _

def cpPriorAtoms (_source : Common before step raw) : List (Atom cursor) :=
  (ammoniaGraph.atoms.filter (fun atom => !(atom == ammoniaHydrogen))).map
    (fun atom => ⟨.prior (.ammonia before.packet.source.ammonia.slot atom),atom⟩)

def cpGammaAtoms (atp : Nat) : List (Atom cursor) :=
  (atpGraph.atoms.filter gammaAtom).map (fun atom => ⟨.fuel atp .atp atom,atom⟩)

def cpBicarbonateAtoms (bct : Nat) : List (Atom cursor) :=
  (bicarbonateGraph.atoms.filter (fun atom => !(atom == bicarbonateHydrogen) && !(atom == attackingDescriptor))).map
    (fun atom => ⟨.fuel bct .bicarbonate atom,atom⟩)

def cpSourceAtoms {source : Common before step raw} {current : NativeCurrent source}
    {material : NativeAmmoniaSubstitution source current} (serial : CarbamoylSerial source current material) : List (Atom cursor) :=
  cpPriorAtoms source ++ cpGammaAtoms serial.sites.atp ++ cpBicarbonateAtoms material.products.bicarbonate

theorem cp_atoms_source {source : Common before step raw} {current : NativeCurrent source}
    {material : NativeAmmoniaSubstitution source current} (serial : CarbamoylSerial source current material) :
    (finalAtoms serial .carbamoylPhosphate).Perm (cpSourceAtoms serial) := by
  let own : AtomOrigin cursor → FinalOwner := finalOwner material.products.atp serial.sites.atp material.products.bicarbonate
  let f (entry : FuelKind × Nat) : List (Atom cursor) :=
    ((fuelGraph entry.1).atoms.map (fun atom => (⟨.fuel entry.2 entry.1 atom,atom⟩ : Atom cursor))).filter
      (fun atom => own atom.origin == .carbamoylPhosphate)
  have fuelParts : (raw.fuel.zipIdx.flatMap f).Perm
      (cpGammaAtoms (cursor := cursor) serial.sites.atp ++ cpBicarbonateAtoms material.products.bicarbonate) := by
    have cut := two_flatMap raw.fuel.zipIdx (.atp,serial.sites.atp)
      (.bicarbonate,material.products.bicarbonate) serial.sites.indexed serial.sites.bicarbonateIndexed
      (by simp) (fuel_entries_unique raw.fuel) f
    have empty : ∀ entry ∈ raw.fuel.zipIdx, entry ≠ (.atp,serial.sites.atp) →
        entry ≠ (.bicarbonate,material.products.bicarbonate) → f entry = [] := by
      intro entry _ notATP notBct
      have second : ¬ (entry.2 = serial.sites.atp ∧ entry.1 = .atp) := by
        rintro ⟨index,kind⟩
        exact notATP (Prod.ext kind index)
      have bicarbonate : ¬ (entry.2 = material.products.bicarbonate ∧ entry.1 = .bicarbonate) := by
        rintro ⟨index,kind⟩
        exact notBct (Prod.ext kind index)
      simp only [f,List.filter_map,List.map_eq_nil_iff]
      apply List.filter_eq_nil_iff.mpr
      intro atom _
      by_cases first : entry.2 = material.products.atp ∧ entry.1 = .atp
      · cases value : gammaAtom atom <;> simp [own,finalOwner,first,value]
      · simp [own,finalOwner,first,second,bicarbonate]
    have actual := cut empty
    have atpPart : f (.atp,serial.sites.atp) = cpGammaAtoms serial.sites.atp := by
      simp [f,own,finalOwner,serial.sites.fresh,cpGammaAtoms,fuelGraph,List.filter_map,Function.comp_def]
    have bctPart : f (.bicarbonate,material.products.bicarbonate) = cpBicarbonateAtoms material.products.bicarbonate := by
      simp [f,own,finalOwner,cpBicarbonateAtoms,fuelGraph,List.filter_map,Function.comp_def,
        bicarbonateGraph,bicarbonateHydrogen,attackingDescriptor]
    simpa only [atpPart,bctPart] using actual
  have priorPart : (before.packet.source.atoms.map (fun atom => (⟨.prior atom,atom.descriptor⟩ : Atom cursor))).filter
      (fun atom => own atom.origin == .carbamoylPhosphate) = cpPriorAtoms source := by
    simp [Classical.Source.atoms,List.filter_map,List.filter_append,List.map_append,
      Classical.AtomOrigin.descriptor,own,finalOwner,cpPriorAtoms,Function.comp_def,ammoniaGraph,ammoniaHydrogen]
  rw [finalAtoms,source.atomSource,commonAtoms,List.filter_append]
  change ((before.packet.source.atoms.map (fun atom => (⟨.prior atom,atom.descriptor⟩ : Atom cursor))).filter
    (fun atom => own atom.origin == .carbamoylPhosphate) ++
    (raw.fuel.zipIdx.flatMap (fun entry =>
      (fuelGraph entry.1).atoms.map (fun atom => (⟨.fuel entry.2 entry.1 atom,atom⟩ : Atom cursor)))).filter
    (fun atom => own atom.origin == .carbamoylPhosphate)).Perm _
  rw [priorPart,List.filter_flatMap]
  exact fuelParts.append_left _

def cpIndex : AtomOrigin cursor → Nat
  | .prior (.chain _) => 10
  | .prior (.ammonia _ atom) =>
    if atom.address.atom = "N" then 6 else if atom.address.atom = "H1" then 8 else if atom.address.atom = "H2" then 9 else 10
  | .fuel _ .atp atom =>
    if atom.address.atom = "28" then 0 else if atom.address.atom = "27" then 2 else
      if atom.address.atom = "29" then 3 else if atom.address.atom = "26" then 4 else 10
  | .fuel _ .bicarbonate atom =>
    if atom.address.atom = "O3" then 1 else if atom.address.atom = "C" then 5 else if atom.address.atom = "O1" then 7 else 10

def normalizeAtomStereo (stereo : String) : String := if stereo = "N" then "CHI_UNSPECIFIED" else stereo
def normalizeBondStereo (stereo : String) : String := if stereo = "N" then "STEREONONE" else stereo

abbrev ChemicalAtom := Nat × CPS1EnzymeBath.Primary.Element × ℤ × Bool × String
abbrev ChemicalBond := Nat × Nat × Nat × Bool × String

def atomView {source : Common before step raw} (graph : OriginGraph source.atoms) (atom : Atom cursor) : ChemicalAtom :=
  (cpIndex atom.origin,atom.descriptor.source.element,graph.formalCharge atom.origin,
    atom.descriptor.source.aromatic,normalizeAtomStereo atom.descriptor.source.stereo)

def bondView (bond : SourceBond cursor) : ChemicalBond :=
  (min (cpIndex bond.left) (cpIndex bond.right),max (cpIndex bond.left) (cpIndex bond.right),
    if bond.order = "DOUB" then 2 else if bond.order = "SING" then 1 else 0,
    bond.aromatic,normalizeBondStereo bond.stereo)

def templateAtomView (atom : CPS1EnzymeBath.Primary.Atom) : ChemicalAtom :=
  (atom.ordinal,atom.element,atom.charge,atom.aromatic,atom.stereo)

def templateBondView (bond : CPS1EnzymeBath.Primary.Bond) : ChemicalBond :=
  (min bond.left bond.right,max bond.left bond.right,bond.order,bond.aromatic,bond.stereo)

theorem cp_source_atoms_held {source : Common before step raw} {current : NativeCurrent source}
    {material : NativeAmmoniaSubstitution source current} (serial : CarbamoylSerial source current material)
    (atom : Atom cursor) (held : atom ∈ cpSourceAtoms serial) : atom ∈ source.atoms := by
  have present := (cp_atoms_source serial).mem_iff.mpr held
  exact (List.mem_filter.mp present).1

theorem serial_atom_charge {source : Common before step raw} {current : NativeCurrent source}
    {material : NativeAmmoniaSubstitution source current} (serial : CarbamoylSerial source current material)
    (atom : Atom cursor) (held : atom ∈ source.atoms) :
    serial.after.graph.formalCharge atom.origin = atom.descriptor.source.charge+
      (Finsupp.single (.fuel material.products.bicarbonate .bicarbonate attackingDescriptor) 1-
        Finsupp.single (.fuel material.products.atp .atp leavingDescriptor) 1 : Charges cursor) atom.origin+
      (carbamateToken source material.products.bicarbonate).delta atom.origin+
      (protonToken source material.products.bicarbonate).delta atom.origin+
      (deprotonateToken material.products.bicarbonate).delta atom.origin+
      (phosphorylationToken serial.sites.atp material.products.bicarbonate).delta atom.origin := by
  have materialGraph := congrArg Prod.snd material.whole
  change material.event.after.graph = applyChargedToken material.trace.after.graph (carbamateToken source material.products.bicarbonate) at materialGraph
  rw [serial_charge,materialGraph]
  simp only [applyChargedToken,Finsupp.add_apply,material.products.charge]
  rw [show chargeInventory source.atoms atom.origin = atom.descriptor.source.charge from initial_atom_charge source atom held]

theorem cp_source_atoms_exact {source : Common before step raw} {current : NativeCurrent source}
    {material : NativeAmmoniaSubstitution source current} (serial : CarbamoylSerial source current material) :
    cpSourceAtoms serial = [
      ⟨.prior (.ammonia before.packet.source.ammonia.slot (ammoniaGraph.atoms.get ⟨0,by decide⟩)),ammoniaGraph.atoms.get ⟨0,by decide⟩⟩,
      ⟨.prior (.ammonia before.packet.source.ammonia.slot (ammoniaGraph.atoms.get ⟨2,by decide⟩)),ammoniaGraph.atoms.get ⟨2,by decide⟩⟩,
      ⟨.prior (.ammonia before.packet.source.ammonia.slot (ammoniaGraph.atoms.get ⟨3,by decide⟩)),ammoniaGraph.atoms.get ⟨3,by decide⟩⟩,
      ⟨.fuel serial.sites.atp .atp (atpGraph.atoms.get ⟨26,by decide⟩),atpGraph.atoms.get ⟨26,by decide⟩⟩,
      ⟨.fuel serial.sites.atp .atp (atpGraph.atoms.get ⟨27,by decide⟩),atpGraph.atoms.get ⟨27,by decide⟩⟩,
      ⟨.fuel serial.sites.atp .atp (atpGraph.atoms.get ⟨28,by decide⟩),atpGraph.atoms.get ⟨28,by decide⟩⟩,
      ⟨.fuel serial.sites.atp .atp (atpGraph.atoms.get ⟨29,by decide⟩),atpGraph.atoms.get ⟨29,by decide⟩⟩,
      ⟨.fuel material.products.bicarbonate .bicarbonate (bicarbonateGraph.atoms.get ⟨0,by decide⟩),bicarbonateGraph.atoms.get ⟨0,by decide⟩⟩,
      ⟨.fuel material.products.bicarbonate .bicarbonate (bicarbonateGraph.atoms.get ⟨1,by decide⟩),bicarbonateGraph.atoms.get ⟨1,by decide⟩⟩,
      ⟨.fuel material.products.bicarbonate .bicarbonate (bicarbonateGraph.atoms.get ⟨3,by decide⟩),bicarbonateGraph.atoms.get ⟨3,by decide⟩⟩] := by
  rfl

theorem cp_atom_charge {source : Common before step raw} {current : NativeCurrent source}
    {material : NativeAmmoniaSubstitution source current} (serial : CarbamoylSerial source current material)
    (atom : Atom cursor) (held : atom ∈ cpSourceAtoms serial) :
    serial.after.graph.formalCharge atom.origin = atom.descriptor.source.charge := by
  rw [serial_atom_charge serial atom (cp_source_atoms_held serial atom held)]
  rw [cp_source_atoms_exact] at held
  simp only [List.mem_cons,List.not_mem_nil,or_false] at held
  rcases held with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [protonToken,deprotonateToken,phosphorylationToken,carbamateToken,ChargedToken.delta,
    ammoniaNitrogen,originalHydrogen,nitrogenDescriptor,ammoniaHydrogen,
    attackingDescriptor,carbamateOxygen,bicarbonateHydrogen,ammoniaGraph,bicarbonateGraph,
    leavingDescriptor,atpGraph,CPS1EnzymeBath.Primary.atp,CPS1EnzymeBath.Joint.bathAtom]

def sourceAtomView (atom : Atom cursor) : ChemicalAtom :=
  (cpIndex atom.origin,atom.descriptor.source.element,atom.descriptor.source.charge,
    atom.descriptor.source.aromatic,normalizeAtomStereo atom.descriptor.source.stereo)

theorem cp_template_atoms {source : Common before step raw} {current : NativeCurrent source}
    {material : NativeAmmoniaSubstitution source current} (serial : CarbamoylSerial source current material) :
    ((finalAtoms serial .carbamoylPhosphate).map (atomView serial.after.graph)).Perm
      (CPS1EnzymeBath.Primary.carbamoylPhosphate.atoms.map templateAtomView) := by
  have actual := (cp_atoms_source serial).map (atomView serial.after.graph)
  have charges : (cpSourceAtoms serial).map (atomView serial.after.graph) = (cpSourceAtoms serial).map sourceAtomView := by
    apply List.map_congr_left
    intro atom held
    simp only [atomView,sourceAtomView,cp_atom_charge serial atom held]
  rw [charges] at actual
  apply actual.trans
  change ([(6,.N,0,false,"CHI_UNSPECIFIED"),(8,.H,0,false,"CHI_UNSPECIFIED"),
    (9,.H,0,false,"CHI_UNSPECIFIED"),(4,.O,0,false,"CHI_UNSPECIFIED"),
    (2,.O,-1,false,"CHI_UNSPECIFIED"),(0,.P,0,false,"CHI_UNSPECIFIED"),
    (3,.O,-1,false,"CHI_UNSPECIFIED"),(5,.C,0,false,"CHI_UNSPECIFIED"),
    (7,.O,0,false,"CHI_UNSPECIFIED"),(1,.O,0,false,"CHI_UNSPECIFIED")] : List ChemicalAtom).Perm _
  decide +kernel

def bicarbonatePart (atom : Graph.Atom) : FinalOwner :=
  if atom == bicarbonateHydrogen then .proton
  else if atom == attackingDescriptor then .phosphate else .carbamoylPhosphate

theorem atp_cross_gamma : ∀ bond ∈ descriptorBonds atpGraph,
    gammaAtom bond.left ≠ gammaAtom bond.right → bond = atpDebit := by decide +kernel

theorem bicarbonate_cross : ∀ bond ∈ descriptorBonds bicarbonateGraph,
    bicarbonatePart bond.left ≠ bicarbonatePart bond.right →
      bond = ⟨carbonDescriptor,attackingDescriptor,"SING",false,"N"⟩ ∨
      bond = ⟨carbamateOxygen,bicarbonateHydrogen,"SING",false,"N"⟩ := by decide +kernel

theorem ammonia_cross : ∀ bond ∈ descriptorBonds ammoniaGraph,
    (bond.left == ammoniaHydrogen) ≠ (bond.right == ammoniaHydrogen) →
      bond = ⟨nitrogenDescriptor,ammoniaHydrogen,"SING",false,"N"⟩ := by decide +kernel

theorem source_surviving_owner {source : Common before step raw} {current : NativeCurrent source}
    {material : NativeAmmoniaSubstitution source current} (serial : CarbamoylSerial source current material)
    (bond : SourceBond cursor) (held : bond ∈ source.bonds)
    (notFirst : bond ≠ sourceDebit material.products.atp)
    (notCarbon : bond ≠ carbamateDebit material.products.bicarbonate)
    (notNitrogen : bond ≠ nitrogenHydrogen source)
    (notOxygen : bond ≠ oxygenHydrogen material.products.bicarbonate)
    (notSecond : bond ≠ sourceDebit serial.sites.atp) :
    finalOwner material.products.atp serial.sites.atp material.products.bicarbonate bond.left =
      finalOwner material.products.atp serial.sites.atp material.products.bicarbonate bond.right := by
  rw [common_bonds_resolved source] at held
  rcases List.mem_append.mp held with priorHeld | fuelHeld
  · rcases List.mem_append.mp priorHeld with chainHeld | ammoniaHeld
    · obtain ⟨descriptor,_,same⟩ := List.mem_map.mp chainHeld
      subst bond
      rfl
    · obtain ⟨descriptor,descriptorHeld,same⟩ := List.mem_map.mp ammoniaHeld
      subst bond
      have flags : (descriptor.left == ammoniaHydrogen) = (descriptor.right == ammoniaHydrogen) := by
        by_contra different
        have same := ammonia_cross descriptor descriptorHeld different
        apply notNitrogen
        rw [same]
        rfl
      simp only [DescriptorBond.lift,finalOwner,flags]
  · obtain ⟨entry,_,entryHeld⟩ := List.mem_flatMap.mp fuelHeld
    obtain ⟨descriptor,descriptorHeld,same⟩ := List.mem_map.mp entryHeld
    subst bond
    rcases entry with ⟨kind,occurrence⟩
    cases kind with
    | atp =>
      have flags (selected : occurrence = material.products.atp ∨ occurrence = serial.sites.atp) :
          gammaAtom descriptor.left = gammaAtom descriptor.right := by
        by_contra different
        have same := atp_cross_gamma descriptor descriptorHeld different
        rcases selected with first | second
        · apply notFirst
          rw [same,first]
          rfl
        · apply notSecond
          rw [same,second]
          rfl
      by_cases first : occurrence = material.products.atp
      · simp only [DescriptorBond.lift,finalOwner,first,and_self,ite_true,flags (Or.inl first)]
      · by_cases second : occurrence = serial.sites.atp
        · simp only [DescriptorBond.lift,finalOwner,second,and_self,ite_true,flags (Or.inr second)]
        · simp [DescriptorBond.lift,finalOwner,first,second]
    | bicarbonate =>
      by_cases selected : occurrence = material.products.bicarbonate
      · have parts : bicarbonatePart descriptor.left = bicarbonatePart descriptor.right := by
          by_contra different
          rcases bicarbonate_cross descriptor descriptorHeld different with carbon | oxygen
          · apply notCarbon
            rw [carbon,selected]
            rfl
          · apply notOxygen
            rw [oxygen,selected]
            rfl
        simpa only [DescriptorBond.lift,finalOwner,selected,reduceCtorEq,and_false,ite_false,and_self,ite_true,bicarbonatePart] using parts
      · simp [DescriptorBond.lift,finalOwner,selected]

theorem source_debits_once {source : Common before step raw} {current : NativeCurrent source}
    {material : NativeAmmoniaSubstitution source current} (serial : CarbamoylSerial source current material) :
    source.bonds.count (sourceDebit material.products.atp) = 1 ∧
    source.bonds.count (carbamateDebit material.products.bicarbonate) = 1 ∧
    source.bonds.count (nitrogenHydrogen source) = 1 ∧
    source.bonds.count (oxygenHydrogen material.products.bicarbonate) = 1 ∧
    source.bonds.count (sourceDebit serial.sites.atp) = 1 := by
  have vertices := source_token_vertices source current material.trace.selection.bond material.trace.selection.bondActual
  rw [material.products.token] at vertices
  have firstIndexed : (FuelKind.atp,material.products.atp) ∈ raw.fuel.zipIdx :=
    source_fuel_occurrence source material.products.atp .atp leavingDescriptor vertices.2.1
  exact ⟨source_fuel_bond_once source material.products.atp .atp atpDebit firstIndexed (by decide +kernel),
    source_fuel_bond_once source material.products.bicarbonate .bicarbonate
      ⟨carbonDescriptor,attackingDescriptor,"SING",false,"N"⟩ serial.sites.bicarbonateIndexed (by decide +kernel),
    ammonia_hydrogen_once source,
    source_fuel_bond_once source material.products.bicarbonate .bicarbonate
      ⟨carbamateOxygen,bicarbonateHydrogen,"SING",false,"N"⟩ serial.sites.bicarbonateIndexed (by decide +kernel),
    source_fuel_bond_once source serial.sites.atp .atp atpDebit serial.sites.indexed (by decide +kernel)⟩

theorem serial_debits_absent {source : Common before step raw} {current : NativeCurrent source}
    {material : NativeAmmoniaSubstitution source current} (serial : CarbamoylSerial source current material)
    (bond : SourceBond cursor) (selected : bond ∈ [sourceDebit material.products.atp,
      carbamateDebit material.products.bicarbonate,nitrogenHydrogen source,
      oxygenHydrogen material.products.bicarbonate,sourceDebit serial.sites.atp]) : bond ∉ serial.bonds := by
  obtain ⟨first,carbon,nitrogen,oxygen,second⟩ := source_debits_once serial
  have one : source.bonds.count bond = 1 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at selected
    rcases selected with rfl | rfl | rfl | rfl | rfl
    · exact first
    · exact carbon
    · exact nitrogen
    · exact oxygen
    · exact second
  simp only [List.mem_cons,List.not_mem_nil,or_false] at selected
  rcases selected with rfl | rfl | rfl | rfl | rfl
  all_goals
    apply List.count_eq_zero.mp
    simp [CarbamoylSerial.bonds,substitutionBonds,bondAfter,List.count_erase,
      sourceDebit,atpDebit,DescriptorBond.lift,
      carbamateDebit,nitrogenHydrogen,oxygenHydrogen,sourceCredit,carbamateCredit,
      protonCredit,phosphorylationCredit,ammoniaNitrogen,originalHydrogen,serial.sites.fresh,
      carbonDescriptor,carbamateOxygen,attackingDescriptor,bicarbonateHydrogen,bicarbonateGraph] at one ⊢
    omega

theorem serial_bonds_local {source : Common before step raw} {current : NativeCurrent source}
    {material : NativeAmmoniaSubstitution source current} (serial : CarbamoylSerial source current material) :
    ∀ bond ∈ serial.bonds,
      finalOwner material.products.atp serial.sites.atp material.products.bicarbonate bond.left =
        finalOwner material.products.atp serial.sites.atp material.products.bicarbonate bond.right := by
  intro bond held
  have outside (debit : SourceBond cursor) (paid : debit ∈ [sourceDebit material.products.atp,
      carbamateDebit material.products.bicarbonate,nitrogenHydrogen source,
      oxygenHydrogen material.products.bicarbonate,sourceDebit serial.sites.atp]) : bond ≠ debit := by
    intro same
    exact serial_debits_absent serial debit paid (same ▸ held)
  rcases bond_after_support _ _ bond held with oldSecond | lastCredit
  · rcases bond_after_support _ _ bond oldSecond with oldProton | impossible
    · rcases bond_after_support _ _ bond oldProton with oldMaterial | proton
      · rcases substitution_support source current material bond oldMaterial with original | firstCredit | carbonCredit
        · exact source_surviving_owner serial bond original
            (outside _ (by simp)) (outside _ (by simp)) (outside _ (by simp))
            (outside _ (by simp)) (outside _ (by simp))
        · subst bond
          simp [finalOwner,sourceCredit,phosphorusDescriptor,gammaAtom,atpGraph,
            CPS1EnzymeBath.Primary.atp,CPS1EnzymeBath.Joint.bathAtom,attackingDescriptor,
            bicarbonateHydrogen,bicarbonateGraph]
          decide +kernel
        · subst bond
          simp [finalOwner,carbamateCredit,ammoniaNitrogen,carbonDescriptor,attackingDescriptor,
            bicarbonateHydrogen,bicarbonateGraph,nitrogenDescriptor,ammoniaHydrogen,ammoniaGraph]
      · have same : bond = protonCredit source material.products.bicarbonate := List.mem_singleton.mp proton
        subst bond
        simp [finalOwner,protonCredit,originalHydrogen,attackingDescriptor,bicarbonateHydrogen,bicarbonateGraph]
    · simp at impossible
  · have same : bond = phosphorylationCredit serial.sites.atp material.products.bicarbonate := List.mem_singleton.mp lastCredit
    subst bond
    simp [finalOwner,phosphorylationCredit,serial.sites.fresh,phosphorusDescriptor,gammaAtom,atpGraph,
      CPS1EnzymeBath.Primary.atp,CPS1EnzymeBath.Joint.bathAtom,carbamateOxygen,attackingDescriptor,
      bicarbonateHydrogen,bicarbonateGraph]
    decide +kernel

def cpPriorBonds (_source : Common before step raw) : List (SourceBond cursor) :=
  ((descriptorBonds ammoniaGraph).filter (fun bond =>
    !(bond.left == ammoniaHydrogen) && !(bond.right == ammoniaHydrogen))).map
    (DescriptorBond.lift (fun atom => .prior (.ammonia before.packet.source.ammonia.slot atom)))

def cpGammaBonds (atp : Nat) : List (SourceBond cursor) :=
  ((descriptorBonds atpGraph).filter (fun bond => gammaAtom bond.left && gammaAtom bond.right)).map
    (DescriptorBond.lift (.fuel atp .atp))

def cpBicarbonateBonds (bct : Nat) : List (SourceBond cursor) :=
  ((descriptorBonds bicarbonateGraph).filter (fun bond =>
    !(bond.left == bicarbonateHydrogen) && !(bond.left == attackingDescriptor) &&
    !(bond.right == bicarbonateHydrogen) && !(bond.right == attackingDescriptor))).map
    (DescriptorBond.lift (.fuel bct .bicarbonate))

def cpBondPredicate {source : Common before step raw} {current : NativeCurrent source}
    {material : NativeAmmoniaSubstitution source current} (serial : CarbamoylSerial source current material)
    (bond : SourceBond cursor) : Bool :=
  finalOwner material.products.atp serial.sites.atp material.products.bicarbonate bond.left == .carbamoylPhosphate &&
  finalOwner material.products.atp serial.sites.atp material.products.bicarbonate bond.right == .carbamoylPhosphate

theorem cp_initial_bonds_source {source : Common before step raw} {current : NativeCurrent source}
    {material : NativeAmmoniaSubstitution source current} (serial : CarbamoylSerial source current material) :
    (source.bonds.filter (cpBondPredicate serial)).Perm
      (cpPriorBonds source ++ cpGammaBonds serial.sites.atp ++ cpBicarbonateBonds material.products.bicarbonate) := by
  let f (entry : FuelKind × Nat) := (resolvedBonds (fuelGraph entry.1) (AtomOrigin.fuel (cursor := cursor) entry.2 entry.1)).filter
    (cpBondPredicate serial)
  have empty : ∀ entry ∈ raw.fuel.zipIdx, entry ≠ (.atp,serial.sites.atp) →
      entry ≠ (.bicarbonate,material.products.bicarbonate) → f entry = [] := by
    intro entry _ notATP notBct
    have second : ¬ (entry.2 = serial.sites.atp ∧ entry.1 = .atp) := by
      rintro ⟨index,kind⟩
      exact notATP (Prod.ext kind index)
    have bicarbonate : ¬ (entry.2 = material.products.bicarbonate ∧ entry.1 = .bicarbonate) := by
      rintro ⟨index,kind⟩
      exact notBct (Prod.ext kind index)
    simp only [f,resolvedBonds,List.filter_map,List.map_eq_nil_iff]
    apply List.filter_eq_nil_iff.mpr
    intro bond _
    by_cases first : entry.2 = material.products.atp ∧ entry.1 = .atp
    · simp [cpBondPredicate,DescriptorBond.lift,finalOwner,first]
    · simp [cpBondPredicate,DescriptorBond.lift,finalOwner,first,second,bicarbonate]
  have parts := two_flatMap raw.fuel.zipIdx (.atp,serial.sites.atp) (.bicarbonate,material.products.bicarbonate)
    serial.sites.indexed serial.sites.bicarbonateIndexed (by simp) (fuel_entries_unique raw.fuel) f empty
  have atpPart : f (.atp,serial.sites.atp) = cpGammaBonds serial.sites.atp := by
    simp [f,resolvedBonds,List.filter_map,Function.comp_def,cpBondPredicate,DescriptorBond.lift,
      finalOwner,serial.sites.fresh,cpGammaBonds,fuelGraph]
  have bctPart : f (.bicarbonate,material.products.bicarbonate) = cpBicarbonateBonds material.products.bicarbonate := by
    simp [f,resolvedBonds,List.filter_map,Function.comp_def,cpBondPredicate,DescriptorBond.lift,
      finalOwner,cpBicarbonateBonds,Bool.and_assoc,fuelGraph,descriptorBonds,bicarbonateGraph,
      bicarbonateHydrogen,attackingDescriptor]
  rw [atpPart,bctPart] at parts
  have priorPart : (resolvedBonds before.packet.source.graph (fun atom => .prior (.chain atom)) ++
      resolvedBonds ammoniaGraph (fun atom => .prior (.ammonia before.packet.source.ammonia.slot atom))).filter
      (cpBondPredicate serial) = cpPriorBonds source := by
    simp [List.filter_append,resolvedBonds,List.filter_map,Function.comp_def,cpBondPredicate,DescriptorBond.lift,
      finalOwner,cpPriorBonds,ammoniaHydrogen,ammoniaGraph,descriptorBonds]
  rw [common_bonds_resolved source,List.filter_append,priorPart,List.filter_flatMap]
  exact parts.append_left _

theorem filter_erase_unselected {α : Type} [DecidableEq α] (rows : List α) (predicate : α → Bool)
    (element : α) (unselected : predicate element = false) :
    (rows.erase element).filter predicate = rows.filter predicate := by
  rw [← List.erase_filter]
  apply List.erase_eq_self_iff.mpr
  intro held
  have selected := (List.mem_filter.mp held).2
  rw [unselected] at selected
  cases selected

theorem filter_bond_after (bonds : List (SourceBond cursor)) (action : SourceBondAction cursor)
    (predicate : SourceBond cursor → Bool) (unselected : predicate action.debit = false) :
    (bondAfter bonds action).filter predicate = bonds.filter predicate ++ action.credit.toList.filter predicate := by
  rw [bondAfter,List.filter_append,filter_erase_unselected bonds predicate action.debit unselected]

theorem cp_final_bonds {source : Common before step raw} {current : NativeCurrent source}
    {material : NativeAmmoniaSubstitution source current} (serial : CarbamoylSerial source current material) :
    finalBonds serial .carbamoylPhosphate = source.bonds.filter (cpBondPredicate serial) ++
      [carbamateCredit source material.products.bicarbonate,phosphorylationCredit serial.sites.atp material.products.bicarbonate] := by
  have leavingGamma : gammaAtom leavingDescriptor = false := by decide +kernel
  have phosphorusGamma : gammaAtom phosphorusDescriptor = true := by decide +kernel
  have first : cpBondPredicate serial (sourceDebit material.products.atp) = false := by
    simp [cpBondPredicate,sourceDebit,atpDebit,DescriptorBond.lift,finalOwner,leavingGamma,phosphorusGamma]
  have carbon : cpBondPredicate serial (carbamateDebit material.products.bicarbonate) = false := by
    simp [cpBondPredicate,carbamateDebit,finalOwner,carbonDescriptor,attackingDescriptor,bicarbonateHydrogen,bicarbonateGraph]
  have nitrogen : cpBondPredicate serial (nitrogenHydrogen source) = false := by
    simp [cpBondPredicate,nitrogenHydrogen,finalOwner,ammoniaNitrogen,originalHydrogen,ammoniaHydrogen,nitrogenDescriptor,ammoniaGraph]
  have oxygen : cpBondPredicate serial (oxygenHydrogen material.products.bicarbonate) = false := by
    simp [cpBondPredicate,oxygenHydrogen,finalOwner,carbamateOxygen,attackingDescriptor,bicarbonateHydrogen,bicarbonateGraph]
  have second : cpBondPredicate serial (sourceDebit serial.sites.atp) = false := by
    simp [cpBondPredicate,sourceDebit,atpDebit,DescriptorBond.lift,finalOwner,serial.sites.fresh,leavingGamma,phosphorusGamma]
  change serial.bonds.filter (cpBondPredicate serial) = _
  rw [CarbamoylSerial.bonds,filter_bond_after _ _ _ second,filter_bond_after _ _ _ oxygen,
    filter_bond_after _ _ _ nitrogen,substitutionBonds,filter_bond_after _ _ _ carbon,
    List.filter_append,filter_erase_unselected _ _ _ first]
  simp [cpBondPredicate,finalOwner,sourceCredit,carbamateCredit,protonCredit,phosphorylationCredit,
    serial.sites.fresh,phosphorusGamma,attackingDescriptor,carbonDescriptor,carbamateOxygen,bicarbonateHydrogen,
    bicarbonateGraph,ammoniaNitrogen,originalHydrogen,nitrogenDescriptor,ammoniaHydrogen,ammoniaGraph]

theorem cp_template_bonds {source : Common before step raw} {current : NativeCurrent source}
    {material : NativeAmmoniaSubstitution source current} (serial : CarbamoylSerial source current material) :
    ((finalBonds serial .carbamoylPhosphate).map bondView).Perm
      (CPS1EnzymeBath.Primary.carbamoylPhosphate.bonds.map templateBondView) := by
  have parts := (cp_initial_bonds_source serial).append_right
    [carbamateCredit source material.products.bicarbonate,phosphorylationCredit serial.sites.atp material.products.bicarbonate]
  rw [← cp_final_bonds serial] at parts
  apply ((parts.map bondView).trans)
  change ([(6,8,1,false,"STEREONONE"),(6,9,1,false,"STEREONONE"),
    (0,4,2,false,"STEREONONE"),(0,2,1,false,"STEREONONE"),(0,3,1,false,"STEREONONE"),
    (5,7,2,false,"STEREONONE"),(1,5,1,false,"STEREONONE"),
    (5,6,1,false,"STEREONONE"),(0,1,1,false,"STEREONONE")] : List ChemicalBond).Perm _
  decide +kernel

structure CPIdentity {source : Common before step raw} {current : NativeCurrent source}
    {material : NativeAmmoniaSubstitution source current} (serial : CarbamoylSerial source current material) : Prop where
  atoms : ((finalAtoms serial .carbamoylPhosphate).map (atomView serial.after.graph)).Perm
    (CPS1EnzymeBath.Primary.carbamoylPhosphate.atoms.map templateAtomView)
  bonds : ((finalBonds serial .carbamoylPhosphate).map bondView).Perm
    (CPS1EnzymeBath.Primary.carbamoylPhosphate.bonds.map templateBondView)

theorem cp_identity {source : Common before step raw} {current : NativeCurrent source}
    {material : NativeAmmoniaSubstitution source current} (serial : CarbamoylSerial source current material) :
    CPIdentity serial := ⟨cp_template_atoms serial,cp_template_bonds serial⟩

def classifyCP? {source : Common before step raw} {current : NativeCurrent source}
    {material : NativeAmmoniaSubstitution source current} (serial : CarbamoylSerial source current material) :
    Option CPS1EnzymeBath.Primary.TemplateKind := by
  classical
  exact if CPIdentity serial then some .carbamoylPhosphate else none

theorem source_cp_classified {source : Common before step raw} {current : NativeCurrent source}
    {material : NativeAmmoniaSubstitution source current} (serial : CarbamoylSerial source current material) :
    classifyCP? serial = some .carbamoylPhosphate := by
  simp only [classifyCP?,if_pos (cp_identity serial)]

structure SourceGeneratedCarbamoyl (source : Common before step raw) (current : NativeCurrent source) where
  dynamics : NativeAmmoniaDynamics.SourceGeneratedDynamics source current
  serial : CarbamoylSerial source current dynamics.origin.material
  identity : CPIdentity serial
  partition : source.atoms.Perm (completePartition serial)
  localBonds : ∀ bond ∈ serial.bonds,
    finalOwner dynamics.origin.material.products.atp serial.sites.atp dynamics.origin.material.products.bicarbonate bond.left =
      finalOwner dynamics.origin.material.products.atp serial.sites.atp dynamics.origin.material.products.bicarbonate bond.right

theorem source_generated_carbamoyl_products (source : Common before step raw) (current : NativeCurrent source) :
    Nonempty (SourceGeneratedCarbamoyl source current) := by
  obtain ⟨dynamics⟩ := NativeAmmoniaDynamics.source_generated_ammonia_dynamics source current
  obtain ⟨serial⟩ := source_carbamoyl_serial source current dynamics.origin.material
  exact ⟨⟨dynamics,serial,cp_identity serial,complete_partition serial,serial_bonds_local serial⟩⟩

end
end CPS1MaterialIncidence.NativeCarbamoyl
