import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.ActualFirstProducts

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1MaterialIncidence.NativeSubstitution
noncomputable section
open CPS1AtomicSource CPS1AtomicDynamics CPS1SameEventFunction CPS1PhosphorylExchange
open NativeProducts

variable {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
  {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
  {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}

def carbonDescriptor : Graph.Atom := bicarbonateGraph.atoms.get ⟨0,by decide⟩
def nitrogenDescriptor : Graph.Atom := ammoniaGraph.atoms.get ⟨0,by decide⟩

def ammoniaNitrogen (_source : Common before step raw) : AtomOrigin cursor :=
  .prior (.ammonia before.packet.source.ammonia.slot nitrogenDescriptor)

def carbamateDebit (bct : Nat) : SourceBond cursor :=
  ⟨.fuel bct .bicarbonate carbonDescriptor,.fuel bct .bicarbonate attackingDescriptor,
    "SING",false,"N"⟩

def carbamateCredit (source : Common before step raw) (bct : Nat) : SourceBond cursor :=
  ⟨.fuel bct .bicarbonate carbonDescriptor,ammoniaNitrogen source,"SING",false,"N"⟩

def carbamateToken (source : Common before step raw) (bct : Nat) : ChargedToken cursor :=
  ⟨ammoniaNitrogen source,.fuel bct .bicarbonate attackingDescriptor,
    some ⟨carbamateDebit bct,some (carbamateCredit source bct)⟩⟩

private theorem source_fuel_occurrence (source : Common before step raw)
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

private theorem fuel_atom_held (source : Common before step raw)
    (occurrence : Nat) (kind : FuelKind) (payload : Graph.Atom)
    (indexed : (kind,occurrence) ∈ raw.fuel.zipIdx) (held : payload ∈ (fuelGraph kind).atoms) :
    (⟨.fuel occurrence kind payload,payload⟩ : Atom cursor) ∈ source.atoms := by
  rw [source.atomSource]
  exact List.mem_append_right _ (List.mem_flatMap.mpr
    ⟨(kind,occurrence),indexed,List.mem_map.mpr ⟨payload,held,rfl⟩⟩)

private theorem ammonia_atom_held (source : Common before step raw)
    (payload : Graph.Atom) (held : payload ∈ ammoniaGraph.atoms) :
    (⟨.prior (.ammonia before.packet.source.ammonia.slot payload),payload⟩ : Atom cursor) ∈ source.atoms := by
  rw [source.atomSource]
  apply List.mem_append_left
  apply List.mem_map.mpr
  refine ⟨.ammonia before.packet.source.ammonia.slot payload,?_,rfl⟩
  exact List.mem_append_right _ (List.mem_map.mpr ⟨payload,held,rfl⟩)

private theorem product_bicarbonate_index (source : Common before step raw) (current : NativeCurrent source)
    (trace : NativeIncidenceTrace source current) (products : FirstProducts source current trace) :
    (FuelKind.bicarbonate,products.bicarbonate) ∈ raw.fuel.zipIdx := by
  have held := (source_token_vertices source current trace.selection.bond trace.selection.bondActual).2.2.2.2
  rw [products.token] at held
  exact source_fuel_occurrence source products.bicarbonate .bicarbonate attackingDescriptor held

private theorem carbamate_debit_held (source : Common before step raw) (bct : Nat)
    (indexed : (FuelKind.bicarbonate,bct) ∈ raw.fuel.zipIdx) : carbamateDebit bct ∈ source.bonds := by
  rw [common_bonds_resolved source]
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨(.bicarbonate,bct),indexed,?_⟩
  apply List.mem_map.mpr
  refine ⟨⟨carbonDescriptor,attackingDescriptor,"SING",false,"N"⟩,?_,rfl⟩
  change (⟨carbonDescriptor,attackingDescriptor,"SING",false,"N"⟩ : DescriptorBond) ∈
    descriptorBonds bicarbonateGraph
  decide +kernel

private theorem native_after_ready (source : Common before step raw) (current : NativeCurrent source)
    (trace : NativeIncidenceTrace source current) : electronReady source trace.after.graph := by
  intro origin held
  have update (origin : AtomOrigin cursor) :
      electronInventory source trace.after.graph origin =
        electronInventory source trace.before.graph origin-trace.selection.token.delta origin := by
    rw [native_incidence_graph]
    simp only [electronInventory,applyChargedToken,Finsupp.add_apply]
    ring
  rw [update]
  by_cases donor : origin = trace.selection.token.chargeDonor
  · subst origin
    simp only [ChargedToken.delta,Finsupp.sub_apply,Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne trace.safe.2.2.1,sub_zero]
    exact sub_nonneg.mpr trace.electronPaid
  · by_cases receiver : origin = trace.selection.token.chargeReceiver
    · subst origin
      simp only [ChargedToken.delta,Finsupp.sub_apply,
        Finsupp.single_eq_of_ne (Ne.symm trace.safe.2.2.1),Finsupp.single_eq_same,zero_sub,sub_neg_eq_add]
      have prior := trace.ready _ held
      omega
    · simp only [ChargedToken.delta,Finsupp.sub_apply,Finsupp.single_eq_of_ne donor,
        Finsupp.single_eq_of_ne receiver,sub_self,sub_zero]
      exact trace.ready origin held

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

private theorem product_carbon_ammonia_pair_absent (source : Common before step raw)
    (current : NativeCurrent source) (trace : NativeIncidenceTrace source current)
    (products : FirstProducts source current trace) (bond : SourceBond cursor)
    (held : bond ∈ source.bonds.erase (sourceDebit products.atp) ++
      [sourceCredit products.atp products.bicarbonate]) :
    ¬ ((bond.left = (carbamateCredit source products.bicarbonate).left ∧
        bond.right = (carbamateCredit source products.bicarbonate).right) ∨
       (bond.left = (carbamateCredit source products.bicarbonate).right ∧
        bond.right = (carbamateCredit source products.bicarbonate).left)) := by
  have locality := products.localBonds bond held
  intro ends
  rcases ends with ⟨left,right⟩ | ⟨left,right⟩
  · simp [left,right,carbamateCredit,ammoniaNitrogen,owner] at locality
  · simp [left,right,carbamateCredit,ammoniaNitrogen,owner] at locality

private theorem carbamate_next_guards (source : Common before step raw) (current : NativeCurrent source)
    (trace : NativeIncidenceTrace source current) (actual : nativeIncidence? source current = .ok trace)
    (products : FirstProducts source current trace) :
    (carbamateToken source products.bicarbonate).safe source ∧
      electronReady source trace.after.graph ∧
      1 ≤ electronInventory source trace.after.graph (carbamateToken source products.bicarbonate).chargeDonor ∧
      (∀ bond ∈ (carbamateToken source products.bicarbonate).debits, bond ∉ trace.after.spent) ∧
      (∀ bond ∈ (carbamateToken source products.bicarbonate).debits, 1 ≤ trace.after.graph.incidence bond) ∧
      (∀ bond ∈ (carbamateToken source products.bicarbonate).credits, trace.after.graph.incidence bond = 0) ∧
      (∀ bond ∈ (carbamateToken source products.bicarbonate).credits,
        adjacent trace.after.graph bond.left bond.right = false) := by
  classical
  have indexed := product_bicarbonate_index source current trace products
  have carbonPresent : carbonDescriptor ∈ (fuelGraph .bicarbonate).atoms := by decide +kernel
  have oxygenPresent : attackingDescriptor ∈ (fuelGraph .bicarbonate).atoms := by decide +kernel
  have nitrogenPresent : nitrogenDescriptor ∈ ammoniaGraph.atoms := by decide +kernel
  have carbonAtomHeld := fuel_atom_held source products.bicarbonate .bicarbonate carbonDescriptor indexed carbonPresent
  have oxygenAtomHeld := fuel_atom_held source products.bicarbonate .bicarbonate attackingDescriptor indexed oxygenPresent
  have nitrogenAtomHeld := ammonia_atom_held source nitrogenDescriptor nitrogenPresent
  have carbonHeld : AtomOrigin.fuel products.bicarbonate .bicarbonate carbonDescriptor ∈ vertices source :=
    List.mem_map_of_mem carbonAtomHeld
  have oxygenHeld : AtomOrigin.fuel products.bicarbonate .bicarbonate attackingDescriptor ∈ vertices source :=
    List.mem_map_of_mem oxygenAtomHeld
  have nitrogenHeld : ammoniaNitrogen source ∈ vertices source := List.mem_map_of_mem nitrogenAtomHeld
  have debitHeld := carbamate_debit_held source products.bicarbonate indexed
  have debitVertices := source_bond_vertices source (carbamateDebit products.bicarbonate) debitHeld
  have safe : (carbamateToken source products.bicarbonate).safe source := by
    refine ⟨nitrogenHeld,oxygenHeld,?_,?_,?_⟩
    · simp [carbamateToken,ammoniaNitrogen]
    · intro bond held
      have same : bond = carbamateDebit products.bicarbonate := by
        simpa [carbamateToken,ChargedToken.debits] using held
      subst bond
      exact ⟨debitHeld,debitVertices.1,debitVertices.2⟩
    · intro bond held
      have same : bond = carbamateCredit source products.bicarbonate := by
        simpa [carbamateToken,ChargedToken.credits] using held
      subst bond
      refine ⟨carbonHeld,nitrogenHeld,?_⟩
      simp [carbamateCredit,ammoniaNitrogen]
  have nitrogenInitial : electronInventory source (sourceGraph source) (ammoniaNitrogen source) = 7 := by
    have inventory := initial_source_atom_electrons source
      ⟨ammoniaNitrogen source,nitrogenDescriptor⟩ nitrogenAtomHeld
    have value : (Charged.atomicNumber nitrogenDescriptor.source.element : ℤ)-nitrogenDescriptor.source.charge = 7 := by
      decide +kernel
    exact inventory.trans value
  have nitrogenAfter : electronInventory source trace.after.graph (ammoniaNitrogen source) = 7 := by
    simpa [electronInventory,products.charge,sourceGraph,ammoniaNitrogen] using nitrogenInitial
  have notFirst : carbamateDebit (cursor := cursor) products.bicarbonate ≠ sourceDebit products.atp := by
    intro same
    have left := congrArg SourceBond.left same
    have kind := (AtomOrigin.fuel.inj left).2.1
    cases kind
  have firstSpent : trace.after.spent = [sourceDebit products.atp] := by
    rw [NativeIncidenceTrace.after,charged_record_spent,
      (native_incidence_starts_full source current trace actual).2]
    simp only [List.nil_append,IncidenceSelection.token,products.token,ChargedToken.debits,
      Option.toList_some,List.map_cons,List.map_nil]
  have creditAbsent : carbamateCredit source products.bicarbonate ∉
      source.bonds.erase (sourceDebit products.atp) ++ [sourceCredit products.atp products.bicarbonate] := by
    intro held
    exact product_carbon_ammonia_pair_absent source current trace products _ held (Or.inl ⟨rfl,rfl⟩)
  refine ⟨safe,native_after_ready source current trace,?_,?_,?_,?_,?_⟩
  · change 1 ≤ electronInventory source trace.after.graph (ammoniaNitrogen source)
    rw [nitrogenAfter]
    norm_num
  · intro bond held
    have same : bond = carbamateDebit products.bicarbonate := by
      simpa [carbamateToken,ChargedToken.debits] using held
    subst bond
    simp [firstSpent,notFirst]
  · intro bond held
    have same : bond = carbamateDebit products.bicarbonate := by
      simpa [carbamateToken,ChargedToken.debits] using held
    subst bond
    rw [products.incidence]
    apply bond_inventory_paid
    exact List.mem_append_left _ ((List.mem_erase_of_ne notFirst).mpr debitHeld)
  · intro bond held
    have same : bond = carbamateCredit source products.bicarbonate := by
      simpa [carbamateToken,ChargedToken.credits] using held
    subst bond
    rw [products.incidence]
    exact bond_inventory_absent _ _ creditAbsent
  · intro credit held
    have same : credit = carbamateCredit source products.bicarbonate := by
      simpa [carbamateToken,ChargedToken.credits] using held
    subst credit
    apply Bool.eq_false_iff.mpr
    intro occupied
    obtain ⟨bond,bondHeld,checked⟩ := List.any_eq_true.mp occupied
    have checkedParts : decide (0 < trace.after.graph.incidence bond) = true ∧
        ((bond.left == (carbamateCredit source products.bicarbonate).left &&
          bond.right == (carbamateCredit source products.bicarbonate).right) ||
         (bond.left == (carbamateCredit source products.bicarbonate).right &&
          bond.right == (carbamateCredit source products.bicarbonate).left)) = true := by
      simpa only [Bool.and_eq_true] using checked
    have supported : trace.after.graph.incidence bond ≠ 0 :=
      Finsupp.mem_support_iff.mp (Finset.mem_toList.mp bondHeld)
    have present : bond ∈ source.bonds.erase (sourceDebit products.atp) ++
        [sourceCredit products.atp products.bicarbonate] := by
      by_contra absent
      rw [products.incidence] at supported
      exact supported (bond_inventory_absent _ _ absent)
    apply product_carbon_ammonia_pair_absent source current trace products bond present
    simpa only [Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] using checkedParts.2

structure CarbonAmmoniaStep (source : Common before step raw) (current : NativeCurrent source)
    (trace : NativeIncidenceTrace source current) (products : FirstProducts source current trace) : Type where
  safe : (carbamateToken source products.bicarbonate).safe source
  ready : electronReady source trace.after.graph
  electronPaid : 1 ≤ electronInventory source trace.after.graph (carbamateToken source products.bicarbonate).chargeDonor
  unused : ∀ bond ∈ (carbamateToken source products.bicarbonate).debits, bond ∉ trace.after.spent
  debitPaid : ∀ bond ∈ (carbamateToken source products.bicarbonate).debits, 1 ≤ trace.after.graph.incidence bond
  creditFree : ∀ bond ∈ (carbamateToken source products.bicarbonate).credits, trace.after.graph.incidence bond = 0
  pairFree : ∀ bond ∈ (carbamateToken source products.bicarbonate).credits,
    adjacent trace.after.graph bond.left bond.right = false

def carbonAmmonia? (source : Common before step raw) (current : NativeCurrent source)
    (trace : NativeIncidenceTrace source current) (products : FirstProducts source current trace) :
    Except (NativeIncidenceResidual cursor) (CarbonAmmoniaStep source current trace products) := by
  classical
  let token := carbamateToken source products.bicarbonate
  exact if safe : token.safe source then
    if ready : electronReady source trace.after.graph then
      if paid : 1 ≤ electronInventory source trace.after.graph token.chargeDonor then
        if unused : ∀ bond ∈ token.debits, bond ∉ trace.after.spent then
          if debit : ∀ bond ∈ token.debits, 1 ≤ trace.after.graph.incidence bond then
            if credit : ∀ bond ∈ token.credits, trace.after.graph.incidence bond = 0 then
              if pairFree : ∀ bond ∈ token.credits, adjacent trace.after.graph bond.left bond.right = false then
                .ok ⟨safe,ready,paid,unused,debit,credit,pairFree⟩
              else .error .occupiedAtomPair
            else .error .occupiedBond
          else .error .bondShortage
        else .error .reusedSourceBond
      else .error (.electronShortage token.chargeDonor (electronInventory source trace.after.graph token.chargeDonor))
    else .error .negativeElectronResource
  else .error .unsafeSourceToken

def CarbonAmmoniaStep.after {source : Common before step raw} {current : NativeCurrent source}
    {trace : NativeIncidenceTrace source current} {products : FirstProducts source current trace}
    (_event : CarbonAmmoniaStep source current trace products) : ChargedState source current :=
  trace.after.record (carbamateToken source products.bicarbonate)

private theorem carbon_ammonia_spent {source : Common before step raw} {current : NativeCurrent source}
    {trace : NativeIncidenceTrace source current} {products : FirstProducts source current trace}
    (event : CarbonAmmoniaStep source current trace products) :
    event.after.spent = trace.after.spent ++ [carbamateDebit products.bicarbonate] := by
  rw [CarbonAmmoniaStep.after,charged_record_spent]
  simp [carbamateToken,ChargedToken.debits]

private theorem carbon_ammonia_whole {source : Common before step raw} {current : NativeCurrent source}
    {trace : NativeIncidenceTrace source current} {products : FirstProducts source current trace}
    (event : CarbonAmmoniaStep source current trace products) :
    event.after.whole = (current,applyChargedToken trace.after.graph (carbamateToken source products.bicarbonate)) := by
  change (current,(trace.after.record (carbamateToken source products.bicarbonate)).graph) = _
  rw [charged_record_graph]

private theorem carbamate_bonds_different (source : Common before step raw) (bct : Nat) :
    carbamateDebit (cursor := cursor) bct ≠ carbamateCredit source bct := by
  intro same
  have right := congrArg SourceBond.right same
  simp [carbamateDebit,carbamateCredit,ammoniaNitrogen] at right

private theorem carbon_ammonia_credit {source : Common before step raw} {current : NativeCurrent source}
    {trace : NativeIncidenceTrace source current} {products : FirstProducts source current trace}
    (event : CarbonAmmoniaStep source current trace products) :
    event.after.graph.incidence (carbamateCredit source products.bicarbonate) = 1 := by
  have held : carbamateCredit source products.bicarbonate ∈ (carbamateToken source products.bicarbonate).credits := by
    simp [carbamateToken,ChargedToken.credits]
  have free := event.creditFree _ held
  rw [CarbonAmmoniaStep.after,charged_record_graph]
  change trace.after.graph.incidence (carbamateCredit source products.bicarbonate)+
    (carbamateToken source products.bicarbonate).incidenceDelta (carbamateCredit source products.bicarbonate) = 1
  simp [carbamateToken,ChargedToken.incidenceDelta,SourceBondAction.delta,free,
    Ne.symm (carbamate_bonds_different source products.bicarbonate)]

private theorem carbon_ammonia_debit {source : Common before step raw} {current : NativeCurrent source}
    {trace : NativeIncidenceTrace source current} {products : FirstProducts source current trace}
    (event : CarbonAmmoniaStep source current trace products) :
    event.after.graph.incidence (carbamateDebit products.bicarbonate) =
      trace.after.graph.incidence (carbamateDebit products.bicarbonate)-1 := by
  rw [CarbonAmmoniaStep.after,charged_record_graph]
  change trace.after.graph.incidence (carbamateDebit products.bicarbonate)+
    (carbamateToken source products.bicarbonate).incidenceDelta (carbamateDebit products.bicarbonate) = _
  simp [carbamateToken,ChargedToken.incidenceDelta,SourceBondAction.delta,
    carbamate_bonds_different source products.bicarbonate,sub_eq_add_neg]

private theorem carbon_ammonia_ready {source : Common before step raw} {current : NativeCurrent source}
    {trace : NativeIncidenceTrace source current} {products : FirstProducts source current trace}
    (event : CarbonAmmoniaStep source current trace products) : electronReady source event.after.graph := by
  intro origin held
  have update (origin : AtomOrigin cursor) :
      electronInventory source event.after.graph origin =
        electronInventory source trace.after.graph origin-(carbamateToken source products.bicarbonate).delta origin := by
    rw [CarbonAmmoniaStep.after,charged_record_graph]
    simp only [electronInventory,applyChargedToken,Finsupp.add_apply]
    ring
  rw [update]
  by_cases donor : origin = (carbamateToken source products.bicarbonate).chargeDonor
  · subst origin
    simp only [ChargedToken.delta,Finsupp.sub_apply,Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne event.safe.2.2.1,sub_zero]
    exact sub_nonneg.mpr event.electronPaid
  · by_cases receiver : origin = (carbamateToken source products.bicarbonate).chargeReceiver
    · subst origin
      simp only [ChargedToken.delta,Finsupp.sub_apply,
        Finsupp.single_eq_of_ne (Ne.symm event.safe.2.2.1),Finsupp.single_eq_same,zero_sub,sub_neg_eq_add]
      have prior := event.ready _ held
      omega
    · simp only [ChargedToken.delta,Finsupp.sub_apply,Finsupp.single_eq_of_ne donor,
        Finsupp.single_eq_of_ne receiver,sub_self,sub_zero]
      exact event.ready origin held

private theorem carbamate_valence_charge (source : Common before step raw) (bct : Nat) :
    singIncidenceBoundary (carbamateToken source bct).incidenceDelta = (carbamateToken source bct).delta := by
  simp only [carbamateToken,ChargedToken.incidenceDelta,Option.toList_some,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,SourceBondAction.delta,singIncidenceBoundary,map_sub,
    Finsupp.linearCombination_single,one_smul,singBondBoundary,carbamateDebit,carbamateCredit,
    ChargedToken.delta]
  simp only [ite_true]
  ext origin
  simp only [Finsupp.add_apply,Finsupp.sub_apply]
  ring

private theorem carbon_ammonia_grade {source : Common before step raw} {current : NativeCurrent source}
    {trace : NativeIncidenceTrace source current} {products : FirstProducts source current trace}
    (event : CarbonAmmoniaStep source current trace products) :
    singIncidenceBoundary (event.after.graph.incidence-trace.after.graph.incidence) =
      event.after.graph.formalCharge-trace.after.graph.formalCharge := by
  rw [CarbonAmmoniaStep.after,charged_record_graph]
  change singIncidenceBoundary ((trace.after.graph.incidence+(carbamateToken source products.bicarbonate).incidenceDelta)-
    trace.after.graph.incidence) =
    (trace.after.graph.formalCharge+(carbamateToken source products.bicarbonate).delta)-trace.after.graph.formalCharge
  simpa only [add_sub_cancel_left] using carbamate_valence_charge source products.bicarbonate

structure NativeAmmoniaSubstitution (source : Common before step raw) (current : NativeCurrent source) : Type where
  trace : NativeIncidenceTrace source current
  firstActual : nativeIncidence? source current = .ok trace
  products : FirstProducts source current trace
  event : CarbonAmmoniaStep source current trace products
  actualNext : carbonAmmonia? source current trace products = .ok event
  fresh : carbamateDebit products.bicarbonate ∉ trace.after.spent
  spent : event.after.spent = trace.after.spent ++ [carbamateDebit products.bicarbonate]
  credit : event.after.graph.incidence (carbamateCredit source products.bicarbonate) = 1
  debit : event.after.graph.incidence (carbamateDebit products.bicarbonate) =
    trace.after.graph.incidence (carbamateDebit products.bicarbonate)-1
  ready : electronReady source event.after.graph
  grade : singIncidenceBoundary (event.after.graph.incidence-trace.after.graph.incidence) =
    event.after.graph.formalCharge-trace.after.graph.formalCharge
  whole : event.after.whole = (current,applyChargedToken trace.after.graph (carbamateToken source products.bicarbonate))

theorem native_incidence_ammonia_substitution (source : Common before step raw) (current : NativeCurrent source) :
    Nonempty (NativeAmmoniaSubstitution source current) := by
  obtain ⟨trace,actual,⟨products⟩⟩ := native_incidence_first_products source current
  obtain ⟨safe,ready,paid,unused,debit,credit,pair⟩ := carbamate_next_guards source current trace actual products
  let event : CarbonAmmoniaStep source current trace products := ⟨safe,ready,paid,unused,debit,credit,pair⟩
  have checked : carbonAmmonia? source current trace products = .ok event := by
    unfold carbonAmmonia?
    dsimp only
    simp only [dif_pos safe,dif_pos ready,dif_pos paid,dif_pos unused,dif_pos debit,dif_pos credit,dif_pos pair]
  have debitHeld : carbamateDebit products.bicarbonate ∈ (carbamateToken source products.bicarbonate).debits := by
    simp [carbamateToken,ChargedToken.debits]
  exact ⟨{
    trace := trace
    firstActual := actual
    products := products
    event := event
    actualNext := checked
    fresh := event.unused _ debitHeld
    spent := carbon_ammonia_spent event
    credit := carbon_ammonia_credit event
    debit := carbon_ammonia_debit event
    ready := carbon_ammonia_ready event
    grade := carbon_ammonia_grade event
    whole := carbon_ammonia_whole event }⟩

end
end CPS1MaterialIncidence.NativeSubstitution
