import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AddressedBondResponse.Motion

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace CPS1AddressedBondResponse
noncomputable section
open CPS1Deformation CPS1AddressedTransfer CPS1PositivePulse
open CPS1ElectronicSource (ElectronIndex ElectronicPulse SpinSpace electronCount)
open scoped BigOperators Topology
variable {frame : CPS1Recycling.Frame}

def SuccessfulBondResponse (state : Material frame) (site : BridgeSite state.reference)
    (degree : Generic.Degree) (index : Nat) : Prop :=
  SuccessfulTransfer state site.phosphate.nuclear index ∧
    0 < (distancePolynomial state site).coefficient degree *
      (squaredDistance (state.movedPositions (dyadicTime index)) site-squaredDistance state.positions site)

theorem exists_successful_bond_response (state : Material frame) (site : BridgeSite state.reference)
    (degree : Generic.Degree) (ready : PulseReady state)
    (active : responseFlux state site.phosphate.nuclear 0 ≠ 0)
    (moving : (distancePolynomial state site).leading? = some degree) :
    ∃ index, SuccessfulBondResponse state site degree index := by
  have neighborhood : ∀ᶠ time in 𝓝 (0 : ℝ), 0 < time →
      (∃ next : Material frame × ElectronicPulse, state.pulse? time = .ok next ∧ PulseReady next.1 ∧
        normalize? state.reference (state.movedPositions time) (state.transportedOccupation time) =
          .ok (seedOccupation state time) ∧
        0 < responseFlux state site.phosphate.nuclear 0 * transferredPopulation state site.phosphate.nuclear time) ∧
      0 < (distancePolynomial state site).coefficient degree *
        (squaredDistance (state.movedPositions time) site-squaredDistance state.positions site) := by
    filter_upwards [transfer_eventually_positive state ready site.phosphate.nuclear active,
      distance_eventually_signed state site degree moving] with time transfer distance
    intro positive
    exact ⟨transfer positive,distance positive⟩
  have powers : Filter.Tendsto dyadicTime Filter.atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1)
  obtain ⟨index,present⟩ := (powers.eventually neighborhood).exists
  exact ⟨index,present (dyadic_time_positive index)⟩

def bondIndex (state : Material frame) (site : BridgeSite state.reference)
    (degree : Generic.Degree) (ready : PulseReady state)
    (active : responseFlux state site.phosphate.nuclear 0 ≠ 0)
    (moving : (distancePolynomial state site).leading? = some degree) : Nat := by
  classical
  exact Nat.find (exists_successful_bond_response state site degree ready active moving)

theorem bond_index_spec (state : Material frame) (site : BridgeSite state.reference)
    (degree : Generic.Degree) (ready : PulseReady state)
    (active : responseFlux state site.phosphate.nuclear 0 ≠ 0)
    (moving : (distancePolynomial state site).leading? = some degree) :
    SuccessfulBondResponse state site degree (bondIndex state site degree ready active moving) := by
  classical
  exact Nat.find_spec (exists_successful_bond_response state site degree ready active moving)

theorem bond_index_minimal (state : Material frame) (site : BridgeSite state.reference)
    (degree : Generic.Degree) (ready : PulseReady state)
    (active : responseFlux state site.phosphate.nuclear 0 ≠ 0)
    (moving : (distancePolynomial state site).leading? = some degree) (index : Nat)
    (smaller : index < bondIndex state site degree ready active moving) :
    ¬ SuccessfulBondResponse state site degree index := by
  classical
  exact Nat.find_min (exists_successful_bond_response state site degree ready active moving) smaller

def bondResult (state : Material frame) (site : BridgeSite state.reference)
    (degree : Generic.Degree) (ready : PulseReady state)
    (active : responseFlux state site.phosphate.nuclear 0 ≠ 0)
    (moving : (distancePolynomial state site).leading? = some degree) : Material frame × ElectronicPulse :=
  match actual : state.pulse? (dyadicTime (bondIndex state site degree ready active moving)) with
  | .ok next => next
  | .error _ => False.elim (by
      obtain ⟨⟨next,same,_⟩,_⟩ := bond_index_spec state site degree ready active moving
      rw [actual] at same
      cases same)

theorem bond_result_actual (state : Material frame) (site : BridgeSite state.reference)
    (degree : Generic.Degree) (ready : PulseReady state)
    (active : responseFlux state site.phosphate.nuclear 0 ≠ 0)
    (moving : (distancePolynomial state site).leading? = some degree) :
    state.pulse? (dyadicTime (bondIndex state site degree ready active moving)) =
      .ok (bondResult state site degree ready active moving) := by
  unfold bondResult
  split
  · assumption
  · obtain ⟨⟨next,same,_⟩,_⟩ := bond_index_spec state site degree ready active moving
    contradiction

namespace NativeSource
open CPS1Deformation.Source

structure Emission (current : Occurrence frame) where
  admission : CPS1AddressedTransfer.NativeSource.Emission current
  site : BridgeSite admission.selected.reference
  sourceSite : selectBridge? admission.selected.reference = some site
  degree : Generic.Degree
  moving : (distancePolynomial admission.selected site).leading? = some degree

def Emission.selected {current : Occurrence frame} (emission : Emission current) : Material frame :=
  emission.admission.selected

theorem emission_same_phosphate {current : Occurrence frame} (emission : Emission current) :
    emission.site.phosphate = emission.admission.site :=
  Option.some.inj ((selected_bridge_source emission.selected.reference emission.site emission.sourceSite).1.symm.trans
    emission.admission.sourceSite)

theorem emission_active {current : Occurrence frame} (emission : Emission current) :
    responseFlux emission.selected emission.site.phosphate.nuclear 0 ≠ 0 := by
  rw [emission_same_phosphate]
  exact emission.admission.active

def Emission.index {current : Occurrence frame} (emission : Emission current) : Nat :=
  bondIndex emission.selected emission.site emission.degree emission.admission.admission.ready
    (emission_active emission) emission.moving

def Emission.time {current : Occurrence frame} (emission : Emission current) : ℝ := dyadicTime emission.index

def Emission.response {current : Occurrence frame} (emission : Emission current) : Material frame × ElectronicPulse :=
  bondResult emission.selected emission.site emission.degree emission.admission.admission.ready
    (emission_active emission) emission.moving

def Emission.next {current : Occurrence frame} (emission : Emission current) : Occurrence frame :=
  CPS1Deformation.Source.resume frame current [.pulse emission.time] []

def autoBondResponse? (current : Occurrence frame) : Option (Emission current) :=
  match CPS1AddressedTransfer.NativeSource.autoTransfer? current with
  | none => none
  | some admission => match pair : selectBridge? admission.selected.reference with
    | none => none
    | some site => match generated : (distancePolynomial admission.selected site).leading? with
      | none => none
      | some degree => some ⟨admission,site,pair,degree,generated⟩

def next (current : Occurrence frame) : Occurrence frame :=
  match autoBondResponse? current with
  | some emission => emission.next
  | none => CPS1Deformation.Source.resume frame current [] []

theorem emission_actual {current : Occurrence frame} (emission : Emission current) :
    emission.selected.pulse? emission.time = .ok emission.response :=
  bond_result_actual emission.selected emission.site emission.degree emission.admission.admission.ready
    (emission_active emission) emission.moving

theorem emission_ready {current : Occurrence frame} (emission : Emission current) : PulseReady emission.response.1 := by
  obtain ⟨next,actual,ready,_⟩ := (bond_index_spec emission.selected emission.site emission.degree
    emission.admission.admission.ready (emission_active emission) emission.moving).1
  have same : next = emission.response := Except.ok.inj (actual.symm.trans (emission_actual emission))
  exact same ▸ ready

theorem emission_normalized {current : Occurrence frame} (emission : Emission current) :
    normalize? emission.selected.reference (emission.selected.movedPositions emission.time)
      (emission.selected.transportedOccupation emission.time) = .ok (seedOccupation emission.selected emission.time) := by
  obtain ⟨_,_,_,normalized,_⟩ := (bond_index_spec emission.selected emission.site emission.degree
    emission.admission.admission.ready (emission_active emission) emission.moving).1
  exact normalized

theorem emission_signed_electrons {current : Occurrence frame} (emission : Emission current) :
    0 < responseFlux emission.selected emission.site.phosphate.nuclear 0 *
      transferredPopulation emission.selected emission.site.phosphate.nuclear emission.time := by
  obtain ⟨_,_,_,_,transfer⟩ := (bond_index_spec emission.selected emission.site emission.degree
    emission.admission.admission.ready (emission_active emission) emission.moving).1
  exact transfer

theorem emission_signed_distance {current : Occurrence frame} (emission : Emission current) :
    0 < (distancePolynomial emission.selected emission.site).coefficient emission.degree *
      (squaredDistance (emission.selected.movedPositions emission.time) emission.site-
        squaredDistance emission.selected.positions emission.site) :=
  (bond_index_spec emission.selected emission.site emission.degree emission.admission.admission.ready
    (emission_active emission) emission.moving).2

theorem emission_minimal {current : Occurrence frame} (emission : Emission current) (index : Nat)
    (smaller : index < emission.index) : ¬ SuccessfulBondResponse emission.selected emission.site emission.degree index :=
  bond_index_minimal emission.selected emission.site emission.degree emission.admission.admission.ready
    (emission_active emission) emission.moving index smaller

theorem emission_paid {current : Occurrence frame} (emission : Emission current) :
    0 < emission.time ∧ 0 < emission.response.1.reserve ∧
      emission.response.1.energy+emission.response.1.reserve = emission.selected.energy+emission.selected.reserve :=
  ⟨dyadic_time_positive _,(emission_ready emission).budget,
    (pulse_paid emission.selected emission.response emission.time (emission_actual emission)).2.2.2⟩

theorem emission_seed_actual {current : Occurrence frame} (emission : Emission current) :
    emission.response.1 = (continuousPulseCandidate emission.selected emission.time).reprice
      (emission.selected.reserve-((continuousPulseCandidate emission.selected emission.time).energy-emission.selected.energy)) :=
  response_seed_actual emission.selected emission.response emission.time (emission_actual emission)
    (emission_normalized emission)

theorem emission_actual_pair {current : Occurrence frame} (emission : Emission current) :
    ∃ nextSite : BridgeSite emission.response.1.reference,
      selectBridge? emission.response.1.reference = some nextSite ∧
      nextSite.phosphate.component = emission.site.phosphate.component ∧
      nextSite.phosphate.atomSlot = emission.site.phosphate.atomSlot ∧
      nextSite.oxygenAtomSlot = emission.site.oxygenAtomSlot ∧
      relativePosition emission.response.1.positions nextSite = relativePosition emission.selected.positions emission.site +
        emission.time • relativeVelocity emission.selected emission.site +
        emission.time^2 • relativeQuadratic emission.selected emission.site ∧
      squaredDistance emission.response.1.positions nextSite-squaredDistance emission.selected.positions emission.site =
        (distancePolynomial emission.selected emission.site).delta emission.time ∧
      0 < (distancePolynomial emission.selected emission.site).coefficient emission.degree *
        (squaredDistance emission.response.1.positions nextSite-squaredDistance emission.selected.positions emission.site) := by
  rw [emission_seed_actual]
  exact ⟨emission.site,emission.sourceSite,rfl,rfl,rfl,relative_motion emission.selected emission.site emission.time,
    distance_response emission.selected emission.site emission.time,emission_signed_distance emission⟩

def Emission.fields {current : Occurrence frame} (emission : Emission current) :
    ElectronIndex emission.selected.reference.geometry → SpinSpace := responseFields emission.selected emission.time

def Emission.siteFields {current : Occurrence frame} (emission : Emission current) :
    ElectronIndex emission.selected.reference.geometry → SpinSpace :=
  fun slot => siteProjection emission.selected.reference (emission.selected.movedPositions emission.time)
    emission.site.phosphate.nuclear (emission.fields slot)

def Emission.complementFields {current : Occurrence frame} (emission : Emission current) :
    ElectronIndex emission.selected.reference.geometry → SpinSpace :=
  fun slot => emission.fields slot-emission.siteFields slot

theorem emission_fields_actual {current : Occurrence frame} (emission : Emission current) :
    HEq emission.fields emission.response.1.currentFields := by
  rw [emission_seed_actual]
  exact HEq.rfl

theorem emission_whole_fields {current : Occurrence frame} (emission : Emission current) :
    HEq (fun slot => emission.siteFields slot+emission.complementFields slot) emission.response.1.currentFields := by
  have same : (fun slot => emission.siteFields slot+emission.complementFields slot) = emission.fields :=
    funext (fun _ => add_sub_cancel _ _)
  rw [same]
  exact emission_fields_actual emission

theorem emission_electron_number {current : Occurrence frame} (emission : Emission current) :
    (∑ slot, ‖emission.siteFields slot‖^2)+(∑ slot, ‖emission.complementFields slot‖^2) =
      electronCount frame emission.selected.reference.geometry.originJoint :=
  response_partition_number emission.selected emission.site.phosphate.nuclear emission.time (emission_normalized emission)

theorem emission_complementary_transfer {current : Occurrence frame} (emission : Emission current) :
    (∑ slot, ‖emission.complementFields slot‖^2)-
      (∑ slot, ‖seedFields emission.selected emission.time slot-
        siteProjection emission.selected.reference (emission.selected.movedPositions emission.time)
          emission.site.phosphate.nuclear (seedFields emission.selected emission.time slot)‖^2) =
      -transferredPopulation emission.selected emission.site.phosphate.nuclear emission.time :=
  response_complement_transfer emission.selected emission.site.phosphate.nuclear emission.time (emission_normalized emission)

def available {current : Occurrence frame} (emission : Emission current) : Stock frame :=
  current.current.stock ++ (RawAction.pulse emission.time).material frame

def requested {current : Occurrence frame} (emission : Emission current) : List RawAction :=
  RawAction.pulse emission.time :: current.current.pending

def program {current : Occurrence frame} (emission : Emission current) : List (Reaction frame) :=
  CPS1Deformation.Source.program frame (heldCarrier frame (available emission)) (requested emission)

def execution {current : Occurrence frame} (emission : Emission current) : Execution frame :=
  execute frame (program emission) (available emission)

def afterPulseStock {current : Occurrence frame} (emission : Emission current) : Stock frame :=
  [.deformed emission.response.1,.spentPulse emission.selected emission.time] ++
    ((available emission).erase (.deformed emission.selected)).erase
      (.retained (.retained (.retained (.retained (.rawTime emission.time)))))

def suffix {current : Occurrence frame} (emission : Emission current) : Execution frame :=
  execute frame (CPS1Deformation.Source.program frame (some (.deformed emission.response.1)) current.current.pending)
    (afterPulseStock emission)

theorem emission_held_available {current : Occurrence frame} (emission : Emission current) :
    heldCarrier frame (available emission) = some (.deformed emission.selected) := by
  rw [available,CPS1PositivePulse.NativeSource.held_carrier_append_clock]
  exact emission.admission.admission.held

theorem emission_program {current : Occurrence frame} (emission : Emission current) :
    program emission = .pulse emission.selected emission.time ::
      CPS1Deformation.Source.program frame (some (.deformed emission.response.1)) current.current.pending := by
  change (RawAction.pulse emission.time).reaction frame (heldCarrier frame (available emission)) ::
    CPS1Deformation.Source.program frame
      ((RawAction.pulse emission.time).next frame (heldCarrier frame (available emission))) current.current.pending = _
  rw [emission_held_available]
  simp only [RawAction.reaction,RawAction.next,emission_actual]

theorem emission_fire {current : Occurrence frame} (emission : Emission current) :
    CPS1ResourceExecution.Inventory.fire (Reaction.reactants frame) (Reaction.products frame)
      (.pulse emission.selected emission.time) (available emission) = .ok (afterPulseStock emission) := by
  have carrier : Species.deformed emission.selected ∈ available emission :=
    CPS1PositivePulse.NativeSource.held_carrier_deformed_mem _ _ (emission_held_available emission)
  have clock : Species.retained (.retained (.retained (.retained (.rawTime emission.time)))) ∈ available emission :=
    List.mem_append.mpr (Or.inr List.mem_cons_self)
  simp [CPS1ResourceExecution.Inventory.fire,Reaction.reactants,Reaction.products,guards,
    emission_actual,CPS1ResourceExecution.Inventory.consume,carrier,clock,afterPulseStock]

theorem emission_fired_suffix {current : Occurrence frame} (emission : Emission current) :
    execution emission = ⟨.pulse emission.selected emission.time :: (suffix emission).fired,
      (suffix emission).remaining,(suffix emission).stock,(suffix emission).missing⟩ := by
  rw [execution,emission_program,execute,CPS1ResourceExecution.Inventory.execute_cons,emission_fire]
  rfl

theorem emission_execution {current : Occurrence frame} (emission : Emission current) :
    emission.next.current =
      ⟨(execution emission).stock,(requested emission).drop (execution emission).fired.length,
        current.current.stages ++ [execution emission],(execution emission).missing⟩ := by
  simp only [Emission.next,CPS1Deformation.Source.resume,CPS1Deformation.Source.advance,
    List.map_nil,List.append_nil,List.flatMap_cons,List.flatMap_nil,available,requested,execution,program,
    List.cons_append,List.nil_append]

theorem emission_final_stock {current : Occurrence frame} (emission : Emission current) :
    emission.next.current.stock = (suffix emission).stock := by
  rw [emission_execution,emission_fired_suffix]

theorem emission_pending {current : Occurrence frame} (emission : Emission current) :
    emission.next.current.pending = current.current.pending.drop (suffix emission).fired.length := by
  rw [emission_execution,emission_fired_suffix]
  rfl

theorem emission_first_fired {current : Occurrence frame} (emission : Emission current) :
    (execution emission).fired.head? = some (.pulse emission.selected emission.time) := by
  rw [emission_fired_suffix]
  rfl

theorem emission_whole_inventory {current : Occurrence frame} (emission : Emission current) (species : Species frame) :
    (available emission).count species +
      (CPS1ResourceExecution.Inventory.credit (Reaction.products frame) (execution emission).fired).count species =
        (execution emission).stock.count species +
          (CPS1ResourceExecution.Inventory.debit (Reaction.reactants frame) (execution emission).fired).count species :=
  whole_inventory (program emission) (available emission) species

theorem emission_cut {current : Occurrence frame} (emission : Emission current) (missing : Species frame)
    (cut : (execution emission).missing = some missing) :
    ∃ reaction rest, (execution emission).remaining = reaction :: rest ∧
      (execution emission).stock.count missing < (reaction.reactants frame).count missing :=
  actual_cut (program emission) (available emission) missing cut

theorem emission_stock_good {current : Occurrence frame} (emission : Emission current)
    (good : GoodStock current.current.stock) : GoodStock emission.next.current.stock :=
  resume_good current [.pulse emission.time] [] good

theorem emission_stock_noGuard {current : Occurrence frame} (emission : Emission current)
    (safe : NoGuardStock current.current.stock) : NoGuardStock emission.next.current.stock :=
  resume_noGuard current [.pulse emission.time] [] safe

theorem emission_previous {current : Occurrence frame} (emission : Emission current) :
    emission.next.previous = current.previous := rfl

theorem next_previous (current : Occurrence frame) : (next current).previous = current.previous := by
  unfold next
  split <;> rfl

end NativeSource
end
end CPS1AddressedBondResponse
