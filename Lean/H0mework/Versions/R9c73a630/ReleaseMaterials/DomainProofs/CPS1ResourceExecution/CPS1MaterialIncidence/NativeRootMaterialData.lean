import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.NativeRootData

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1MaterialIncidence.NativeRootDataProbe
noncomputable section
open CPS1ResourceExecution CPS1AtomicDynamics CPS1SameEventFunction CPS1PhosphorylExchange CPS1BiologicalUpdate CPS1LiveEditing
open NativeProducts NativeSubstitution NativeAmmoniaDynamics NativeCarbamoyl NativePaidEvent NativePaidPositive
open NativeCPContinuationProbe

universe u v

/-- Data come from the actual checker. The proposition only excludes its
error branch; it cannot select a different successful value. -/
def checked_value {ε : Type u} {α : Type v} (checked : Except ε α)
    (positive : ∃ value, checked = .ok value) : α := by
  cases checked with
  | ok value => exact value
  | error reason => exact False.elim (by obtain ⟨value,actual⟩ := positive; cases actual)

theorem checked_value_actual {ε : Type u} {α : Type v} (checked : Except ε α)
    (positive : ∃ value, checked = .ok value) : checked = .ok (checked_value checked positive) := by
  cases checked with
  | ok value => rfl
  | error reason => obtain ⟨value,actual⟩ := positive; cases actual

variable {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
  {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
  {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}

def source_trace_data (source : Common before step raw) (current : NativeCurrent source) :
    NativeIncidenceTrace source current :=
  checked_value (nativeIncidence? source current) (native_incidence_source_positive source current)

theorem source_trace_actual (source : Common before step raw) (current : NativeCurrent source) :
    nativeIncidence? source current = .ok (source_trace_data source current) :=
  checked_value_actual _ _

def origin_fuel_slot : AtomOrigin cursor → Nat
  | .fuel index _ _ => index
  | .prior _ => 0

theorem first_products_unique {source : Common before step raw} {current : NativeCurrent source}
    {trace : NativeIncidenceTrace source current} (first second : FirstProducts source current trace) :
    first = second := by
  rcases first with ⟨firstATP,firstBct,firstToken,firstPartition,firstIncidence,firstCharge,firstLocal⟩
  rcases second with ⟨secondATP,secondBct,secondToken,secondPartition,secondIncidence,secondCharge,secondLocal⟩
  have tokens := firstToken.symm.trans secondToken
  have atp := congrArg (fun token : BondToken cursor => origin_fuel_slot token.debit.left) tokens
  have bct := congrArg (fun token : BondToken cursor => origin_fuel_slot token.credit.right) tokens
  change firstATP = secondATP at atp
  change firstBct = secondBct at bct
  subst secondATP
  subst secondBct
  rfl

def first_products_data (source : Common before step raw) (current : NativeCurrent source)
    (trace : NativeIncidenceTrace source current) (checked : nativeIncidence? source current = .ok trace) :
    FirstProducts source current trace := by
  let atp := origin_fuel_slot trace.selection.bond.debit.left
  let bct := origin_fuel_slot trace.selection.bond.credit.right
  refine ⟨atp,bct,?_,?_,?_,?_,?_⟩
  all_goals
    obtain ⟨original,actual,⟨products⟩⟩ := native_incidence_first_products source current
    have same : original = trace := Except.ok.inj (actual.symm.trans checked)
    subst original
    have atpActual : products.atp = atp := by
      dsimp only [atp]
      rw [products.token]
      rfl
    have bctActual : products.bicarbonate = bct := by
      dsimp only [bct]
      rw [products.token]
      rfl
    rw [← atpActual,← bctActual]
    first
      | exact products.token
      | exact products.atomPartition
      | exact products.incidence
      | exact products.charge
      | exact products.localBonds


theorem substitution_event_positive (source : Common before step raw) (current : NativeCurrent source)
    (trace : NativeIncidenceTrace source current) (checked : nativeIncidence? source current = .ok trace)
    (products : FirstProducts source current trace) :
    ∃ event, carbonAmmonia? source current trace products = .ok event := by
  obtain ⟨original⟩ := native_incidence_ammonia_substitution source current
  rcases original with ⟨oldTrace,oldChecked,oldProducts,event,actual,fresh,spent,credit,debit,ready,grade,whole⟩
  have sameTrace : oldTrace = trace := Except.ok.inj (oldChecked.symm.trans checked)
  subst oldTrace
  have sameProducts : oldProducts = products := first_products_unique oldProducts products
  subst oldProducts
  exact ⟨event,actual⟩

def source_substitution_data (source : Common before step raw) (current : NativeCurrent source) :
    NativeAmmoniaSubstitution source current := by
  let trace := source_trace_data source current
  have checked : nativeIncidence? source current = .ok trace := source_trace_actual source current
  let products := first_products_data source current trace checked
  have positive := substitution_event_positive source current trace checked products
  let event := checked_value (carbonAmmonia? source current trace products) positive
  have actual : carbonAmmonia? source current trace products = .ok event := checked_value_actual _ _
  refine ⟨trace,checked,products,event,actual,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals
    obtain ⟨original⟩ := native_incidence_ammonia_substitution source current
    rcases original with ⟨oldTrace,oldChecked,oldProducts,oldEvent,oldActual,fresh,spent,credit,debit,ready,grade,whole⟩
    have sameTrace : oldTrace = trace := Except.ok.inj (oldChecked.symm.trans checked)
    subst oldTrace
    have sameProducts : oldProducts = products := first_products_unique oldProducts products
    subst oldProducts
    have sameEvent : oldEvent = event := Except.ok.inj (oldActual.symm.trans actual)
    subst oldEvent
    first
      | exact fresh
      | exact spent
      | exact credit
      | exact debit
      | exact ready
      | exact grade
      | exact whole

theorem substitution_unique {source : Common before step raw} {current : NativeCurrent source}
    (first second : NativeAmmoniaSubstitution source current) : first = second := by
  rcases first with ⟨trace1,checked1,products1,event1,actual1,fresh1,spent1,credit1,debit1,ready1,grade1,whole1⟩
  rcases second with ⟨trace2,checked2,products2,event2,actual2,fresh2,spent2,credit2,debit2,ready2,grade2,whole2⟩
  have sameTrace : trace1 = trace2 := Except.ok.inj (checked1.symm.trans checked2)
  subst trace2
  have sameProducts : products1 = products2 := first_products_unique products1 products2
  subst products2
  have sameEvent : event1 = event2 := Except.ok.inj (actual1.symm.trans actual2)
  subst event2
  rfl

/-- The least successful finite source row supplies the slot. Existence is used
only to reject the actual find?'s none branch. -/
def source_sector_data (source : Common before step raw) (origin : AtomOrigin cursor)
    (present : ∃ index : AtomSector source, originAt source index = origin) :
    {index : AtomSector source // originAt source index = origin} := by
  classical
  let candidates := List.finRange source.atoms.length
  cases actual : candidates.find? (fun index => decide (originAt source index = origin)) with
  | some index => exact ⟨index,of_decide_eq_true (List.find?_some (p := fun index : AtomSector source => decide (originAt source index = origin)) actual)⟩
  | none =>
    exact False.elim (by
      obtain ⟨index,identity⟩ := present
      have absent : ¬ decide (originAt source index = origin) = true :=
        List.find?_eq_none.mp actual index (by simp [candidates])
      exact absent (by simp only [identity,decide_true]))

def source_ammonia_data (source : Common before step raw) (current : NativeCurrent source) :
    AmmoniaSource source current := by
  let material := source_substitution_data source current
  have origins :
      (∃ index : AtomSector source, originAt source index =
        .fuel material.products.bicarbonate .bicarbonate NativeAmmoniaDynamics.carbonDescriptor) ∧
      (∃ index : AtomSector source, originAt source index =
        .fuel material.products.bicarbonate .bicarbonate attackingDescriptor) ∧
      (∃ index : AtomSector source, originAt source index =
        .prior (.ammonia before.packet.source.ammonia.slot NativeAmmoniaDynamics.nitrogenDescriptor)) := by
    obtain ⟨original⟩ := ammonia_source_nonempty source current
    rcases original with ⟨oldMaterial,carbon,leaving,attacking,cActual,lActual,aActual⟩
    have same : oldMaterial = material := substitution_unique oldMaterial material
    subst oldMaterial
    exact ⟨⟨carbon,cActual⟩,⟨leaving,lActual⟩,⟨attacking,aActual⟩⟩
  let carbon := source_sector_data source _ origins.1
  let leaving := source_sector_data source _ origins.2.1
  let attacking := source_sector_data source _ origins.2.2
  exact ⟨material,carbon.val,leaving.val,attacking.val,carbon.property,leaving.property,attacking.property⟩

def source_dynamics_data (source : Common before step raw) (current : NativeCurrent source) :
    SourceGeneratedDynamics source current :=
  let origin := source_ammonia_data source current
  ⟨origin,NativeAmmoniaDynamics.advance origin (initialState origin),rfl⟩


def source_sites_data (source : Common before step raw) (current : NativeCurrent source)
    (material : NativeAmmoniaSubstitution source current) : CarbamoylSites source current material := by
  classical
  have bctIndexed : (FuelKind.bicarbonate,material.products.bicarbonate) ∈ raw.fuel.zipIdx := by
    obtain ⟨sites⟩ := source_carbamoyl_sites source current material
    exact sites.bicarbonateIndexed
  let selected := fun entry : FuelKind × Nat => decide (entry.1 = .atp ∧ entry.2 ≠ material.products.atp)
  cases actual : raw.fuel.zipIdx.find? selected with
  | some entry =>
    have parts : entry.1 = .atp ∧ entry.2 ≠ material.products.atp :=
      of_decide_eq_true (List.find?_some (p := selected) actual)
    have held : (FuelKind.atp,entry.2) ∈ raw.fuel.zipIdx := by
      rw [← parts.1]
      exact List.mem_of_find?_eq_some actual
    exact ⟨entry.2,held,parts.2,bctIndexed⟩
  | none =>
    exact False.elim (by
      obtain ⟨index,held,fresh⟩ := other_atp source material.products.atp
      have absent := List.find?_eq_none.mp actual (FuelKind.atp,index) held
      exact absent (by simp [selected,fresh]))

private def checked_token {source : Common before step raw} {current : NativeCurrent source}
    {state : ChargedState source current} {token : ChargedToken cursor}
    (positive : Nonempty (TokenStep state token)) : TokenStep state token :=
  checked_value (tokenStep? state token) (by
    obtain ⟨event⟩ := positive
    exact ⟨event,event.checked⟩)

def source_serial_data (source : Common before step raw) (current : NativeCurrent source)
    (material : NativeAmmoniaSubstitution source current) : CarbamoylSerial source current material :=
  let sites := source_sites_data source current material
  let proton := checked_token (source_proton_transfer source current material)
  let deprotonate := checked_token (source_oxygen_deprotonation source current material sites proton)
  let phosphorylate := checked_token (source_second_phosphorylation source current material sites proton deprotonate)
  ⟨sites,proton,deprotonate,phosphorylate⟩

def source_carbamoyl_data (source : Common before step raw) (current : NativeCurrent source) :
    SourceGeneratedCarbamoyl source current :=
  let dynamics := source_dynamics_data source current
  let serial := source_serial_data source current dynamics.origin.material
  ⟨dynamics,serial,cp_identity serial,complete_partition serial,serial_bonds_local serial⟩

def source_parent_data (source : Common before step raw) (current : NativeCurrent source) :
    ParentSource source current := ⟨source_carbamoyl_data source current⟩

private def edge_focus_data (source : Common before step raw) (bond : SourceBond cursor)
    (present : Nonempty (EdgeFocus source bond)) : EdgeFocus source bond := by
  have left : ∃ index : AtomSector source, originAt source index = bond.left := by
    obtain ⟨edge⟩ := present
    exact ⟨edge.left,edge.leftActual⟩
  have right : ∃ index : AtomSector source, originAt source index = bond.right := by
    obtain ⟨edge⟩ := present
    exact ⟨edge.right,edge.rightActual⟩
  let first := source_sector_data source bond.left left
  let second := source_sector_data source bond.right right
  exact ⟨first.val,second.val,first.property,second.property⟩

def source_focus_data {source : Common before step raw} {current : NativeCurrent source}
    (paid : SourceGeneratedPaidReturn source current) : CPFocus paid := by
  let protonLeaving := edge_focus_data source (nitrogenHydrogen source)
    (by obtain ⟨focus⟩ := source_cp_focus paid; exact ⟨focus.protonLeaving⟩)
  let protonForming := edge_focus_data source
    (protonCredit source paid.parent.products.dynamics.origin.material.products.bicarbonate)
    (by obtain ⟨focus⟩ := source_cp_focus paid; exact ⟨focus.protonForming⟩)
  let hydroxylLeaving := edge_focus_data source
    (oxygenHydrogen paid.parent.products.dynamics.origin.material.products.bicarbonate)
    (by obtain ⟨focus⟩ := source_cp_focus paid; exact ⟨focus.hydroxylLeaving⟩)
  let atpLeaving := edge_focus_data source (sourceDebit paid.parent.products.serial.sites.atp)
    (by obtain ⟨focus⟩ := source_cp_focus paid; exact ⟨focus.atpLeaving⟩)
  let atpForming := edge_focus_data source (phosphorylationCredit paid.parent.products.serial.sites.atp
    paid.parent.products.dynamics.origin.material.products.bicarbonate)
    (by obtain ⟨focus⟩ := source_cp_focus paid; exact ⟨focus.atpForming⟩)
  exact ⟨protonLeaving,protonForming,hydroxylLeaving,atpLeaving,atpForming,
    paid.parent.products.serial.proton_actual,paid.parent.products.serial.deprotonate_actual,
    paid.parent.products.serial.phosphorylate_actual⟩

def source_continuation_data {source : Common before step raw} {current : NativeCurrent source}
    (paid : SourceGeneratedPaidReturn source current) : CPNativeContinuation paid :=
  let focus := source_focus_data paid
  ⟨focus,advanceCP paid focus,rfl⟩

section Source
variable {origin : CPS1ReactiveNuclear.SourceCursor frame} {water : Nat} {material : List RawSupply}
  {path : CPS1Recycling.SplitSite} {events : List CPS1Recycling.RawEvent}
  {feed : List CPS1Recycling.RawMaterial} {physical : PhysicalRaw} {depth : Nat}
  (whole : WholeRun origin water material path events feed physical depth) (supply : ContinuationRaw)
  (profile : supply.recycling = [] ∧ supply.recycleFeed = [] ∧ supply.physical = noPhysicalSupply)
  (receipt : LocalRepairReceipt (initialBody ⟨frame,origin⟩))
  (repaired : repairWhole whole supply = .repaired receipt)
  {priorRaw : Classical.Raw} {before : Classical.Current receipt.nextBody.current.2 priorRaw}
  {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}
  (source : Common before step raw) (current : NativeCurrent source)

def source_paid_data : SourceGeneratedPaidReturn source current := by
  let parent := source_parent_data source current
  have ready := repaired_native_source_of_profile whole supply profile receipt repaired current
  let pending : PendingDisposition parent :=
    .cpConsumed (sourceJoint receipt.nextBody.current.1) pendingTail ready.1 ready.2.1
      (attachment_actual parent _ ready.1)
      (pending_attachment_fired parent _ _ ready.1 ready.2.1)
  exact ⟨parent,read_all_paid parent,input_stock_source parent,untouched_slots_actual current,
    actual_remaining_after parent,native_paid_whole parent,canonical_paid_stock parent,
    cp_created_read parent,paid_cursor_source parent,pending,next_cursor_exact parent,
    parent.products.dynamics.result.next,rfl,NativeAmmoniaDynamics.disposition_account parent.products.dynamics.result⟩

end Source
end
end CPS1MaterialIncidence.NativeRootDataProbe
