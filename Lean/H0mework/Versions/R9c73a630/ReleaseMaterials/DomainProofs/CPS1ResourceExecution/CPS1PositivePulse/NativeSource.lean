import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1PositivePulse.Dyadic
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deformation.Actual
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deformation.Good

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace CPS1PositivePulse.NativeSource
noncomputable section
open CPS1Deformation
open CPS1Deformation.Source
variable {frame : CPS1Recycling.Frame}

structure Emission (current : Occurrence frame) where
  selected : Material frame
  ready : PulseReady selected
  held : heldCarrier frame current.current.stock = some (.deformed selected)

def Emission.index {current : Occurrence frame} (emission : Emission current) : Nat :=
  generatedDyadicIndex emission.selected emission.ready

def Emission.time {current : Occurrence frame} (emission : Emission current) : ℝ := dyadicTime emission.index

def Emission.response {current : Occurrence frame} (emission : Emission current) : Material frame × CPS1ElectronicSource.ElectronicPulse :=
  generatedDyadicResult emission.selected emission.ready

def Emission.next {current : Occurrence frame} (emission : Emission current) : Occurrence frame :=
  CPS1Deformation.Source.resume frame current [.pulse emission.time] []

/-- The occurrence supplies the carrier and every current guard before time is generated. -/
def autoPulse? (current : Occurrence frame) : Option (Emission current) := by
  classical
  exact match held : heldCarrier frame current.current.stock with
    | some (.deformed state) => if ready : PulseReady state then some ⟨state,ready,held⟩ else none
    | _ => none

def next (current : Occurrence frame) : Occurrence frame :=
  match autoPulse? current with
  | some emission => emission.next
  | none => CPS1Deformation.Source.resume frame current [] []

theorem emission_time_positive {current : Occurrence frame} (emission : Emission current) :
    0 < emission.time := dyadic_time_positive emission.index

theorem emission_actual {current : Occurrence frame} (emission : Emission current) :
    emission.selected.pulse? emission.time = .ok emission.response :=
  generated_dyadic_actual emission.selected emission.ready

theorem emission_minimal {current : Occurrence frame} (emission : Emission current)
    (index : Nat) (smaller : index < emission.index) :
    ¬ SuccessfulDyadic emission.selected index :=
  generated_dyadic_minimal emission.selected emission.ready index smaller

theorem emission_good {current : Occurrence frame} (emission : Emission current) :
    Good emission.response.1 := generated_dyadic_good emission.selected emission.ready

theorem emission_previous {current : Occurrence frame} (emission : Emission current) :
    emission.next.previous = current.previous := rfl

theorem next_previous (current : Occurrence frame) : (next current).previous = current.previous := by
  unfold next
  split <;> rfl

theorem auto_pulse_generated (current : Occurrence frame) (state : Material frame)
    (held : heldCarrier frame current.current.stock = some (.deformed state)) (ready : PulseReady state) :
    autoPulse? current = some (⟨state,ready,held⟩ : Emission current) := by
  classical
  unfold autoPulse?
  split
  · rename_i selected selectedHeld
    have same : selected = state := Carrier.deformed.inj (Option.some.inj (selectedHeld.symm.trans held))
    subst selected
    simp only [dif_pos ready]
  · simp_all

theorem emission_stock_good {current : Occurrence frame} (emission : Emission current)
    (good : GoodStock current.current.stock) : GoodStock emission.next.current.stock :=
  resume_good current [.pulse emission.time] [] good

theorem emission_stock_noGuard {current : Occurrence frame} (emission : Emission current)
    (safe : NoGuardStock current.current.stock) : NoGuardStock emission.next.current.stock :=
  resume_noGuard current [.pulse emission.time] [] safe

def available {current : Occurrence frame} (emission : Emission current) : Stock frame :=
  current.current.stock ++ (RawAction.pulse emission.time).material frame

def requested {current : Occurrence frame} (emission : Emission current) : List RawAction :=
  RawAction.pulse emission.time :: current.current.pending

def program {current : Occurrence frame} (emission : Emission current) : List (Reaction frame) :=
  CPS1Deformation.Source.program frame (heldCarrier frame (available emission)) (requested emission)

def execution {current : Occurrence frame} (emission : Emission current) : Execution frame :=
  execute frame (program emission) (available emission)

theorem emission_execution {current : Occurrence frame} (emission : Emission current) :
    emission.next.current =
      ⟨(execution emission).stock,(requested emission).drop (execution emission).fired.length,
        current.current.stages ++ [execution emission],(execution emission).missing⟩ := by
  simp only [Emission.next,CPS1Deformation.Source.resume,CPS1Deformation.Source.advance,
    List.map_nil,List.append_nil,List.flatMap_cons,List.flatMap_nil,available,requested,execution,program,
    List.cons_append,List.nil_append]

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

private theorem held_cons (species : Species frame) (rest : Stock frame) :
    heldCarrier frame (species :: rest) = match species with
    | .retained (.retained (.retained (.retained (.retained (.joint joint))))) =>
        some (.molecular (.following (.reference (.joint joint))))
    | .retained (.retained (.retained (.retained (.quantum state)))) =>
        some (.molecular (.following (.reference (.quantum state))))
    | .retained (.retained (.following state)) => some (.molecular (.following (.following state)))
    | .retained (.molecular state) => some (.molecular (.molecular state))
    | .deformed state => some (.deformed state)
    | _ => heldCarrier frame rest := rfl

theorem held_carrier_append_clock (stock : Stock frame) (time : ℝ) :
    heldCarrier frame (stock ++ (RawAction.pulse time).material frame) = heldCarrier frame stock := by
  induction stock with
  | nil => rfl
  | cons species rest previous =>
    rw [List.cons_append,held_cons,held_cons,previous]

theorem held_carrier_deformed_mem (stock : Stock frame) (state : Material frame)
    (actual : heldCarrier frame stock = some (.deformed state)) : Species.deformed state ∈ stock := by
  induction stock with
  | nil => cases actual
  | cons species rest previous =>
    rw [held_cons] at actual
    split at actual
    · cases actual
    · cases actual
    · cases actual
    · cases actual
    · simp only [Option.some.injEq,Carrier.deformed.injEq] at actual
      subst state
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (previous actual)

theorem emission_held_available {current : Occurrence frame} (emission : Emission current) :
    heldCarrier frame (available emission) = some (.deformed emission.selected) := by
  rw [available,held_carrier_append_clock]
  exact emission.held

theorem emission_carrier_mem {current : Occurrence frame} (emission : Emission current) :
    Species.deformed emission.selected ∈ available emission :=
  held_carrier_deformed_mem _ _ (emission_held_available emission)

theorem emission_clock_mem {current : Occurrence frame} (emission : Emission current) :
    Species.retained (.retained (.retained (.retained (.rawTime emission.time)))) ∈
      (available emission).erase (.deformed emission.selected) := by
  apply (List.mem_erase_of_ne (by intro same; cases same)).mpr
  exact List.mem_append.mpr (Or.inr List.mem_cons_self)

theorem emission_paid {current : Occurrence frame} (emission : Emission current) :
    0 < emission.time ∧ 0 ≤ emission.response.1.reserve ∧
      emission.response.1.energy+emission.response.1.reserve = emission.selected.energy+emission.selected.reserve := by
  have paid := pulse_paid emission.selected emission.response emission.time (emission_actual emission)
  exact ⟨emission_time_positive emission,paid.2.2.1,paid.2.2.2⟩

def afterPulseStock {current : Occurrence frame} (emission : Emission current) : Stock frame :=
  [.deformed emission.response.1,.spentPulse emission.selected emission.time] ++
    ((available emission).erase (.deformed emission.selected)).erase
      (.retained (.retained (.retained (.retained (.rawTime emission.time)))))

def suffix {current : Occurrence frame} (emission : Emission current) : Execution frame :=
  execute frame (CPS1Deformation.Source.program frame (some (.deformed emission.response.1)) current.current.pending)
    (afterPulseStock emission)

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
  have clock : Species.retained (.retained (.retained (.retained (.rawTime emission.time)))) ∈
      available emission := List.mem_append.mpr (Or.inr List.mem_cons_self)
  simp [CPS1ResourceExecution.Inventory.fire,Reaction.reactants,Reaction.products,guards,
    emission_actual,CPS1ResourceExecution.Inventory.consume,emission_carrier_mem,clock,afterPulseStock]

/-- Pending actions run after the first generated pulse, so the final stock is the actual suffix stock. -/
theorem emission_fired_suffix {current : Occurrence frame} (emission : Emission current) :
    execution emission =
      ⟨.pulse emission.selected emission.time :: (suffix emission).fired,
        (suffix emission).remaining,(suffix emission).stock,(suffix emission).missing⟩ := by
  rw [execution,emission_program,execute,CPS1ResourceExecution.Inventory.execute_cons,emission_fire]
  rfl

theorem emission_first_fired {current : Occurrence frame} (emission : Emission current) :
    (execution emission).fired.head? = some (.pulse emission.selected emission.time) := by
  rw [emission_fired_suffix]
  rfl

end
end CPS1PositivePulse.NativeSource
