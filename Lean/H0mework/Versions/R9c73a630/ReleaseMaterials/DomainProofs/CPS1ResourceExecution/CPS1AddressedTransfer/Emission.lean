import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AddressedTransfer.Response
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1PositiveContinuation.Renewal
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1PositivePulse.NativeSource

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace CPS1AddressedTransfer
noncomputable section
open CPS1Deformation CPS1PositivePulse
open CPS1ElectronicSource (ElectronIndex ElectronicPulse SpinSpace electronCount)
open scoped BigOperators Topology
variable {frame : CPS1Recycling.Frame}

theorem selected_site_source (source : CPS1ElectronicSource.State frame) (site : Site source)
    (actual : selectSite? source = some site) :
    site.component ∈ source.geometry.originJoint.components ∧ site.component.kind = .atp ∧
      ∃ atom : CPS1EnzymeBath.Joint.Atom,
        (atom,site.atomSlot) ∈ (CPS1EnzymeBath.Joint.atoms frame source.geometry.originJoint).zipIdx ∧
        atom.origin = .bath site.component phosphateAtom ∧
        (CPS1MolecularFrame.nucleus source site.nuclear).particle.address = .nucleus site.atomSlot ∧
        (CPS1MolecularFrame.nucleus source site.nuclear).particle.source = atom.descriptor := by
  unfold selectSite? at actual
  cases componentFound : source.geometry.originJoint.components.find? (fun current => current.kind == .atp) with
  | none => simp [componentFound] at actual
  | some component =>
    simp only [componentFound] at actual
    change ((CPS1EnzymeBath.Joint.atoms frame source.geometry.originJoint).zipIdx.find?
      (fun row => row.1.origin == .bath component phosphateAtom)).bind (fun atom =>
      ((List.finRange source.geometry.nuclei.length).find? (fun index =>
        (CPS1MolecularFrame.nucleus source index).particle.address == .nucleus atom.2 &&
          (CPS1MolecularFrame.nucleus source index).particle.source == atom.1.descriptor)).bind
        (fun nuclear => some (⟨component,atom.2,nuclear⟩ : Site source))) = some site at actual
    cases atomFound : (CPS1EnzymeBath.Joint.atoms frame source.geometry.originJoint).zipIdx.find?
        (fun row => row.1.origin == .bath component phosphateAtom) with
    | none => simp [atomFound] at actual
    | some atom =>
      rw [atomFound] at actual
      change ((List.finRange source.geometry.nuclei.length).find? (fun index =>
        (CPS1MolecularFrame.nucleus source index).particle.address == .nucleus atom.2 &&
          (CPS1MolecularFrame.nucleus source index).particle.source == atom.1.descriptor)).bind
        (fun nuclear => some (⟨component,atom.2,nuclear⟩ : Site source)) = some site at actual
      cases nuclearFound : (List.finRange source.geometry.nuclei.length).find? (fun index =>
          (CPS1MolecularFrame.nucleus source index).particle.address == .nucleus atom.2 &&
            (CPS1MolecularFrame.nucleus source index).particle.source == atom.1.descriptor) with
      | none => simp [nuclearFound] at actual
      | some nuclear =>
        rw [nuclearFound] at actual
        change some (⟨component,atom.2,nuclear⟩ : Site source) = some site at actual
        cases Option.some.inj actual
        have kind : component.kind = .atp := by
          simpa only [beq_iff_eq] using List.find?_some componentFound
        have origin : atom.1.origin = .bath component phosphateAtom := by
          simpa only [beq_iff_eq] using List.find?_some atomFound
        have coordinates : (CPS1MolecularFrame.nucleus source nuclear).particle.address = .nucleus atom.2 ∧
            (CPS1MolecularFrame.nucleus source nuclear).particle.source = atom.1.descriptor := by
          simpa only [Bool.and_eq_true,beq_iff_eq] using List.find?_some nuclearFound
        exact ⟨List.mem_of_find?_eq_some componentFound,kind,atom.1,List.mem_of_find?_eq_some atomFound,
          origin,coordinates.1,coordinates.2⟩

def SuccessfulTransfer (state : Material frame)
    (nuclear : CPS1MolecularFrame.NuclearIndex state.reference) (index : Nat) : Prop :=
  ∃ next : Material frame × ElectronicPulse,
    state.pulse? (dyadicTime index) = .ok next ∧ PulseReady next.1 ∧
      normalize? state.reference (state.movedPositions (dyadicTime index))
        (state.transportedOccupation (dyadicTime index)) = .ok (seedOccupation state (dyadicTime index)) ∧
      0 < responseFlux state nuclear 0 * transferredPopulation state nuclear (dyadicTime index)

theorem transfer_eventually_positive (state : Material frame) (ready : PulseReady state)
    (nuclear : CPS1MolecularFrame.NuclearIndex state.reference) (active : responseFlux state nuclear 0 ≠ 0) :
    ∀ᶠ time in 𝓝 (0 : ℝ), 0 < time →
      ∃ next : Material frame × ElectronicPulse, state.pulse? time = .ok next ∧ PulseReady next.1 ∧
        normalize? state.reference (state.movedPositions time) (state.transportedOccupation time) =
          .ok (seedOccupation state time) ∧
        0 < responseFlux state nuclear 0 * transferredPopulation state nuclear time := by
  have fluxContinuous : ContinuousAt (fun time => responseFlux state nuclear 0 * responseFlux state nuclear time) 0 :=
    (response_flux_continuousAt_zero state ready.good ready.unit nuclear).const_mul _
  have currentPositive : 0 < responseFlux state nuclear 0 * responseFlux state nuclear 0 :=
    mul_self_pos.mpr active
  have positive := fluxContinuous.eventually_mem (isOpen_Ioi.mem_nhds currentPositive)
  filter_upwards [positive,CPS1PositiveContinuation.pulse_eventually_ready state ready,
    candidate_normalization_eventually_success state ready.good] with time flux actual normalized
  intro timePositive
  obtain ⟨next,generated,nextReady⟩ := actual timePositive.le
  refine ⟨next,generated,nextReady,normalized,?_⟩
  rw [response_population]
  have fluxPositive : 0 < responseFlux state nuclear 0 * responseFlux state nuclear time := flux
  have generatedPositive : 0 < (2*time)*(responseFlux state nuclear 0 * responseFlux state nuclear time) :=
    mul_pos (mul_pos (by norm_num) timePositive) fluxPositive
  convert generatedPositive using 1; ring

theorem exists_successful_transfer (state : Material frame) (ready : PulseReady state)
    (nuclear : CPS1MolecularFrame.NuclearIndex state.reference) (active : responseFlux state nuclear 0 ≠ 0) :
    ∃ index, SuccessfulTransfer state nuclear index := by
  have powers : Filter.Tendsto dyadicTime Filter.atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1)
  obtain ⟨index,present⟩ := (powers.eventually (transfer_eventually_positive state ready nuclear active)).exists
  exact ⟨index,present (dyadic_time_positive index)⟩

def transferIndex (state : Material frame) (ready : PulseReady state)
    (nuclear : CPS1MolecularFrame.NuclearIndex state.reference) (active : responseFlux state nuclear 0 ≠ 0) : Nat := by
  classical
  exact Nat.find (exists_successful_transfer state ready nuclear active)

theorem transfer_index_spec (state : Material frame) (ready : PulseReady state)
    (nuclear : CPS1MolecularFrame.NuclearIndex state.reference) (active : responseFlux state nuclear 0 ≠ 0) :
    SuccessfulTransfer state nuclear (transferIndex state ready nuclear active) := by
  classical
  exact Nat.find_spec (exists_successful_transfer state ready nuclear active)

def transferResult (state : Material frame) (ready : PulseReady state)
    (nuclear : CPS1MolecularFrame.NuclearIndex state.reference) (active : responseFlux state nuclear 0 ≠ 0) :
    Material frame × ElectronicPulse :=
  match actual : state.pulse? (dyadicTime (transferIndex state ready nuclear active)) with
  | .ok next => next
  | .error _ => False.elim (by
      obtain ⟨next,same,_⟩ := transfer_index_spec state ready nuclear active
      rw [actual] at same
      cases same)

theorem transfer_result_actual (state : Material frame) (ready : PulseReady state)
    (nuclear : CPS1MolecularFrame.NuclearIndex state.reference) (active : responseFlux state nuclear 0 ≠ 0) :
    state.pulse? (dyadicTime (transferIndex state ready nuclear active)) =
      .ok (transferResult state ready nuclear active) := by
  unfold transferResult
  split
  · assumption
  · obtain ⟨next,same,_⟩ := transfer_index_spec state ready nuclear active
    contradiction

theorem site_complement_source (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (nuclear : CPS1MolecularFrame.NuclearIndex source) (field : SpinSpace) :
    field-siteProjection source positions nuclear field =
      (siteSpace source positions nuclear)ᗮ.starProjection field := by
  exact ((siteSpace source positions nuclear).starProjection_orthogonal_val field).symm

theorem response_partition_number (state : Material frame)
    (nuclear : CPS1MolecularFrame.NuclearIndex state.reference) (time : ℝ)
    (normalized : normalize? state.reference (state.movedPositions time) (state.transportedOccupation time) =
      .ok (seedOccupation state time)) :
    (∑ slot, ‖siteProjection state.reference (state.movedPositions time) nuclear (responseFields state time slot)‖^2) +
      (∑ slot, ‖responseFields state time slot-
        siteProjection state.reference (state.movedPositions time) nuclear (responseFields state time slot)‖^2) =
      electronCount frame state.reference.geometry.originJoint := by
  simp_rw [site_complement_source]
  exact response_population_whole state nuclear time normalized

theorem response_complement_transfer (state : Material frame)
    (nuclear : CPS1MolecularFrame.NuclearIndex state.reference) (time : ℝ)
    (normalized : normalize? state.reference (state.movedPositions time) (state.transportedOccupation time) =
      .ok (seedOccupation state time)) :
    (∑ slot, ‖responseFields state time slot-
        siteProjection state.reference (state.movedPositions time) nuclear (responseFields state time slot)‖^2) -
      (∑ slot, ‖seedFields state time slot-
        siteProjection state.reference (state.movedPositions time) nuclear (seedFields state time slot)‖^2) =
      -transferredPopulation state nuclear time := by
  have first := response_seed_good state time normalized
  have second := response_after_good state time normalized
  simp_rw [site_complement_source]
  exact Generic.complementary_transfer _ _ _
    (fun slot => by rw [first.1 slot]; norm_num) (fun slot => by rw [second.1 slot]; norm_num)

namespace NativeSource
open CPS1Deformation.Source

structure Emission (current : Occurrence frame) where
  admission : CPS1PositivePulse.NativeSource.Emission current
  site : Site admission.selected.reference
  sourceSite : selectSite? admission.selected.reference = some site
  active : responseFlux admission.selected site.nuclear 0 ≠ 0

def Emission.selected {current : Occurrence frame} (emission : Emission current) : Material frame :=
  emission.admission.selected

def Emission.index {current : Occurrence frame} (emission : Emission current) : Nat :=
  transferIndex emission.selected emission.admission.ready emission.site.nuclear emission.active

def Emission.time {current : Occurrence frame} (emission : Emission current) : ℝ := dyadicTime emission.index

def Emission.response {current : Occurrence frame} (emission : Emission current) : Material frame × ElectronicPulse :=
  transferResult emission.selected emission.admission.ready emission.site.nuclear emission.active

def Emission.next {current : Occurrence frame} (emission : Emission current) : Occurrence frame :=
  CPS1Deformation.Source.resume frame current [.pulse emission.time] []

def autoTransfer? (current : Occurrence frame) : Option (Emission current) := by
  classical
  exact match CPS1PositivePulse.NativeSource.autoPulse? current with
    | none => none
    | some admission => match selected : selectSite? admission.selected.reference with
      | none => none
      | some site => if active : responseFlux admission.selected site.nuclear 0 ≠ 0
        then some ⟨admission,site,selected,active⟩ else none

def next (current : Occurrence frame) : Occurrence frame :=
  match autoTransfer? current with
  | some emission => emission.next
  | none => CPS1Deformation.Source.resume frame current [] []

theorem emission_actual {current : Occurrence frame} (emission : Emission current) :
    emission.selected.pulse? emission.time = .ok emission.response :=
  transfer_result_actual emission.selected emission.admission.ready emission.site.nuclear emission.active

theorem emission_ready {current : Occurrence frame} (emission : Emission current) : PulseReady emission.response.1 := by
  obtain ⟨result,actual,ready,_⟩ := transfer_index_spec emission.selected emission.admission.ready
    emission.site.nuclear emission.active
  have same : result = emission.response := Except.ok.inj (actual.symm.trans (emission_actual emission))
  exact same ▸ ready

theorem emission_normalized {current : Occurrence frame} (emission : Emission current) :
    normalize? emission.selected.reference (emission.selected.movedPositions emission.time)
      (emission.selected.transportedOccupation emission.time) = .ok (seedOccupation emission.selected emission.time) := by
  obtain ⟨_,_,_,normalized,_⟩ := transfer_index_spec emission.selected emission.admission.ready
    emission.site.nuclear emission.active
  exact normalized

theorem emission_nonzero {current : Occurrence frame} (emission : Emission current) :
    0 < responseFlux emission.selected emission.site.nuclear 0 *
      transferredPopulation emission.selected emission.site.nuclear emission.time := by
  obtain ⟨_,_,_,_,transfer⟩ := transfer_index_spec emission.selected emission.admission.ready
    emission.site.nuclear emission.active
  exact transfer

theorem emission_source_site {current : Occurrence frame} (emission : Emission current) :
    emission.site.component ∈ emission.selected.reference.geometry.originJoint.components ∧
      emission.site.component.kind = .atp ∧
      ∃ atom : CPS1EnzymeBath.Joint.Atom,
        (atom,emission.site.atomSlot) ∈
          (CPS1EnzymeBath.Joint.atoms frame emission.selected.reference.geometry.originJoint).zipIdx ∧
        atom.origin = .bath emission.site.component phosphateAtom ∧
        (CPS1MolecularFrame.nucleus emission.selected.reference emission.site.nuclear).particle.address =
          .nucleus emission.site.atomSlot ∧
        (CPS1MolecularFrame.nucleus emission.selected.reference emission.site.nuclear).particle.source = atom.descriptor :=
  selected_site_source emission.selected.reference emission.site emission.sourceSite

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

def Emission.fields {current : Occurrence frame} (emission : Emission current) :
    ElectronIndex emission.selected.reference.geometry → SpinSpace := responseFields emission.selected emission.time

def Emission.siteFields {current : Occurrence frame} (emission : Emission current) :
    ElectronIndex emission.selected.reference.geometry → SpinSpace :=
  fun slot => siteProjection emission.selected.reference (emission.selected.movedPositions emission.time)
    emission.site.nuclear (emission.fields slot)

def Emission.complementFields {current : Occurrence frame} (emission : Emission current) :
    ElectronIndex emission.selected.reference.geometry → SpinSpace :=
  fun slot => emission.fields slot-emission.siteFields slot

theorem emission_fields_actual {current : Occurrence frame} (emission : Emission current) :
    HEq emission.fields emission.response.1.currentFields := by
  rw [emission_seed_actual]
  exact HEq.rfl

theorem emission_fields_recompose {current : Occurrence frame} (emission : Emission current)
    (slot : ElectronIndex emission.selected.reference.geometry) :
    emission.siteFields slot+emission.complementFields slot = emission.fields slot :=
  add_sub_cancel _ _

theorem emission_whole_fields {current : Occurrence frame} (emission : Emission current) :
    HEq (fun slot => emission.siteFields slot+emission.complementFields slot) emission.response.1.currentFields := by
  have same : (fun slot => emission.siteFields slot+emission.complementFields slot) = emission.fields :=
    funext (emission_fields_recompose emission)
  rw [same]
  exact emission_fields_actual emission

theorem emission_electron_number {current : Occurrence frame} (emission : Emission current) :
    (∑ slot, ‖emission.siteFields slot‖^2)+(∑ slot, ‖emission.complementFields slot‖^2) =
      electronCount frame emission.selected.reference.geometry.originJoint :=
  response_partition_number emission.selected emission.site.nuclear emission.time (emission_normalized emission)

theorem emission_complementary_transfer {current : Occurrence frame} (emission : Emission current) :
    (∑ slot, ‖emission.complementFields slot‖^2)-
      (∑ slot, ‖seedFields emission.selected emission.time slot-
        siteProjection emission.selected.reference (emission.selected.movedPositions emission.time)
          emission.site.nuclear (seedFields emission.selected emission.time slot)‖^2) =
      -transferredPopulation emission.selected emission.site.nuclear emission.time := by
  exact response_complement_transfer emission.selected emission.site.nuclear emission.time (emission_normalized emission)

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
  exact emission.admission.held

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
end CPS1AddressedTransfer
