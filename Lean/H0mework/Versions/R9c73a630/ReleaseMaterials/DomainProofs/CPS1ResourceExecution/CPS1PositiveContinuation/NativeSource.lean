import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1PositiveContinuation.Program
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1PositivePulse.NativeSource

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1PositiveContinuation.NativeSource
noncomputable section
open CPS1Deformation CPS1Deformation.Source CPS1PositivePulse
variable {frame : CPS1Recycling.Frame}

abbrev Admission (current : Occurrence frame) := CPS1PositivePulse.NativeSource.Emission current

def clock (time : ℝ) : Species frame :=
  .retained (.retained (.retained (.retained (.rawTime time))))

def clocks (state : Material frame) (ready : PulseReady state) (start depth : Nat) : Stock frame :=
  (rawBlock state ready start depth).flatMap (RawAction.material frame)

def spent (state : Material frame) (ready : PulseReady state) (start : Nat) : Nat → Stock frame :=
  fun depth => Nat.rec (motive := fun _ => Nat → Stock frame)
    (fun _ => [])
    (fun _ recur index => recur (index+1) ++
      [.spentPulse (trajectory state ready index).val (timeAt state ready index)]) depth start

private theorem spent_zero (state : Material frame) (ready : PulseReady state) (start : Nat) :
    spent state ready start 0 = [] := rfl

private theorem spent_succ (state : Material frame) (ready : PulseReady state) (start depth : Nat) :
    spent state ready start (depth+1) = spent state ready (start+1) depth ++
      [.spentPulse (trajectory state ready start).val (timeAt state ready start)] := rfl

theorem clocks_zero (state : Material frame) (ready : PulseReady state) (start : Nat) :
    clocks state ready start 0 = [] := rfl

theorem clocks_succ (state : Material frame) (ready : PulseReady state) (start depth : Nat) :
    clocks state ready start (depth+1) = clock (timeAt state ready start) ::
      clocks state ready (start+1) depth := rfl

theorem held_append_clocks (stock : Stock frame) (state : Material frame)
    (ready : PulseReady state) (start depth : Nat) :
    heldCarrier frame (stock ++ clocks state ready start depth) = heldCarrier frame stock := by
  induction depth generalizing start stock with
  | zero => simp only [clocks_zero,List.append_nil]
  | succ depth previous =>
    rw [clocks_succ]
    have split : stock ++ clock (timeAt state ready start) :: clocks state ready (start+1) depth =
        (stock ++ (RawAction.pulse (timeAt state ready start)).material frame) ++ clocks state ready (start+1) depth := by
      simp only [RawAction.material,clock,List.append_assoc,List.cons_append,List.nil_append]
    rw [split,previous,CPS1PositivePulse.NativeSource.held_carrier_append_clock]

private theorem execution_cons (reaction : Reaction frame) (rest : List (Reaction frame)) (stock : Stock frame) :
    type_of% (CPS1ResourceExecution.Inventory.execute_cons (Reaction.reactants frame)
      (Reaction.products frame) reaction rest stock) :=
  CPS1ResourceExecution.Inventory.execute_cons (Reaction.reactants frame) (Reaction.products frame) reaction rest stock

private theorem fire_held (state : Material frame)
    (response : Material frame × CPS1ElectronicSource.ElectronicPulse) (time : ℝ)
    (actual : state.pulse? time = .ok response) (stock nextStock : Stock frame)
    (fired : CPS1ResourceExecution.Inventory.fire (Reaction.reactants frame) (Reaction.products frame)
      (.pulse state time) stock = .ok nextStock) :
    heldCarrier frame nextStock = some (.deformed response.1) := by
  unfold CPS1ResourceExecution.Inventory.fire at fired
  cases consumed : CPS1ResourceExecution.Inventory.consume (Reaction.reactants frame (.pulse state time)) stock with
  | error missing => simp only [consumed] at fired; cases fired
  | ok remainder =>
    simp only [consumed,Except.ok.injEq] at fired
    rw [← fired]
    simp only [Reaction.products,actual]
    rfl

/-- Only the original executor mutates stock. The permutation tracks every
generated clock and spent pulse, including repeated equal clock values. -/
theorem block_paid (state : Material frame) (ready : PulseReady state) (start depth : Nat)
    (surplus stock : Stock frame)
    (inventory : stock.Perm (.deformed (trajectory state ready start).val ::
      clocks state ready start depth ++ surplus))
    (held : heldCarrier frame stock = some (.deformed (trajectory state ready start).val)) :
    let result := execute frame (reactionBlock state ready start depth) stock
    result.fired = reactionBlock state ready start depth ∧ result.remaining = [] ∧
      result.missing = none ∧
      result.stock.Perm (.deformed (trajectory state ready (start+depth)).val ::
        spent state ready start depth ++ surplus) ∧
      heldCarrier frame result.stock = some (.deformed (trajectory state ready (start+depth)).val) := by
  induction depth generalizing start stock surplus with
  | zero =>
    rw [show reactionBlock state ready start 0 = [] from rfl]
    dsimp only [execute,CPS1ResourceExecution.Inventory.execute]
    refine ⟨rfl,rfl,rfl,?_,?_⟩
    · simpa only [spent_zero,Nat.add_zero,clocks_zero,List.nil_append] using inventory
    · simpa only [Nat.add_zero] using held
  | succ depth previous =>
    let before := (trajectory state ready start).val
    let time := timeAt state ready start
    let response := responseAt state ready start
    have actual : before.pulse? time = .ok response := trajectory_actual state ready start
    have required : (Reaction.pulse before time).reactants frame = [.deformed before,clock time] := by
      simp only [Reaction.reactants,actual,guards,List.append_nil,clock]
    have products : (Reaction.pulse before time).products frame =
        [.deformed response.1,.spentPulse before time] := by simp only [Reaction.products,actual]
    have available : stock.Perm ((Reaction.pulse before time).reactants frame ++
        (clocks state ready (start+1) depth ++ surplus)) := by
      simpa only [required,clocks_succ,List.cons_append,List.nil_append] using inventory
    obtain ⟨nextStock,fired,remaining⟩ := CPS1ResourceExecution.Inventory.fire_available (Reaction.reactants frame)
      (Reaction.products frame) (.pulse before time) _ stock available
    have nextInventory : nextStock.Perm (.deformed (trajectory state ready (start+1)).val ::
        clocks state ready (start+1) depth ++ (.spentPulse before time :: surplus)) := by
      rw [products] at remaining
      change nextStock.Perm (.deformed response.1 :: (.spentPulse before time ::
        (clocks state ready (start+1) depth ++ surplus))) at remaining
      have shuffle : (.spentPulse before time :: (clocks state ready (start+1) depth ++ surplus)).Perm
          (clocks state ready (start+1) depth ++ (.spentPulse before time :: surplus)) := by
        simpa only [List.append_assoc,List.cons_append,List.nil_append] using
          (List.perm_append_comm.append_right surplus :
            (([.spentPulse before time] : Stock frame) ++ clocks state ready (start+1) depth ++ surplus).Perm
              ((clocks state ready (start+1) depth ++ [.spentPulse before time]) ++ surplus))
      have aligned := remaining.trans (shuffle.cons (.deformed response.1))
      rw [trajectory_response]
      simpa only [response,List.cons_append] using aligned
    have nextHeld : heldCarrier frame nextStock =
        some (.deformed (trajectory state ready (start+1)).val) := by
      simpa only [trajectory_response] using fire_held before response time actual stock nextStock fired
    have tail := previous (start+1) (.spentPulse before time :: surplus) nextStock nextInventory nextHeld
    rcases tail with ⟨tailFired,tailRemaining,tailMissing,tailInventory,tailHeld⟩
    rw [show reactionBlock state ready start (depth+1) =
      .pulse before time :: reactionBlock state ready (start+1) depth from rfl]
    simp only [execute]
    rw [execution_cons]
    dsimp only [before,time] at fired
    rw [fired]
    refine ⟨congrArg (Reaction.pulse before time :: ·) tailFired,tailRemaining,tailMissing,?_,?_⟩
    · simpa only [spent_succ,List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,before,time,execute]
        using (show _ from tailInventory)
    · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,execute] using tailHeld

private theorem execute_append_paid (first rest : List (Reaction frame)) (stock : Stock frame)
    (paid : (execute frame first stock).remaining = [])
    (complete : (execute frame first stock).missing = none) :
    execute frame (first ++ rest) stock =
      let after := execute frame rest (execute frame first stock).stock
      ⟨(execute frame first stock).fired ++ after.fired,after.remaining,after.stock,after.missing⟩ := by
  induction first generalizing stock with
  | nil => rfl
  | cons reaction first previous =>
    cases action : CPS1ResourceExecution.Inventory.fire (Reaction.reactants frame) (Reaction.products frame) reaction stock with
    | error missing =>
      unfold execute at complete
      rw [execution_cons,action] at complete
      cases complete
    | ok nextStock =>
      unfold execute at paid complete
      rw [execution_cons,action] at paid complete
      change (execute frame first nextStock).remaining = [] at paid
      change (execute frame first nextStock).missing = none at complete
      have tail := previous nextStock paid complete
      unfold execute at tail
      rw [List.cons_append,execute,execution_cons,action]
      rw [execution_cons,action]
      dsimp only
      rw [tail]
      simp only [List.cons_append]

def actions {current : Occurrence frame} (admission : Admission current) (depth : Nat) : List RawAction :=
  rawBlock admission.selected admission.ready 0 depth

def continued {current : Occurrence frame} (admission : Admission current) (depth : Nat) : Occurrence frame :=
  CPS1Deformation.Source.resume frame current (actions admission depth) []

def autoContinue? (current : Occurrence frame) (depth : Nat) : Option (Occurrence frame) :=
  (CPS1PositivePulse.NativeSource.autoPulse? current).map (fun admission => continued admission depth)

def next (current : Occurrence frame) (depth : Nat) : Occurrence frame :=
  (autoContinue? current depth).getD (CPS1Deformation.Source.resume frame current [] [])

def available {current : Occurrence frame} (admission : Admission current) (depth : Nat) : Stock frame :=
  current.current.stock ++ clocks admission.selected admission.ready 0 depth

def prefixExecution {current : Occurrence frame} (admission : Admission current) (depth : Nat) : Execution frame :=
  execute frame (reactionBlock admission.selected admission.ready 0 depth) (available admission depth)

def terminal {current : Occurrence frame} (admission : Admission current) (depth : Nat) : Material frame :=
  (trajectory admission.selected admission.ready depth).val

def suffix {current : Occurrence frame} (admission : Admission current) (depth : Nat) : Execution frame :=
  execute frame (CPS1Deformation.Source.program frame (some (.deformed (terminal admission depth)))
    current.current.pending) (prefixExecution admission depth).stock

def program {current : Occurrence frame} (admission : Admission current) (depth : Nat) : List (Reaction frame) :=
  CPS1Deformation.Source.program frame (heldCarrier frame (available admission depth))
    (actions admission depth ++ current.current.pending)

def execution {current : Occurrence frame} (admission : Admission current) (depth : Nat) : Execution frame :=
  execute frame (program admission depth) (available admission depth)

theorem available_held {current : Occurrence frame} (admission : Admission current) (depth : Nat) :
    heldCarrier frame (available admission depth) = some (.deformed admission.selected) := by
  rw [available,held_append_clocks]
  exact admission.held

theorem prefix_paid {current : Occurrence frame} (admission : Admission current) (depth : Nat) :
    (prefixExecution admission depth).fired = reactionBlock admission.selected admission.ready 0 depth ∧
      (prefixExecution admission depth).remaining = [] ∧ (prefixExecution admission depth).missing = none ∧
      (prefixExecution admission depth).stock.Perm (.deformed (terminal admission depth) ::
        spent admission.selected admission.ready 0 depth ++ current.current.stock.erase (.deformed admission.selected)) ∧
      heldCarrier frame (prefixExecution admission depth).stock = some (.deformed (terminal admission depth)) := by
  have member : Species.deformed admission.selected ∈ current.current.stock :=
    CPS1PositivePulse.NativeSource.held_carrier_deformed_mem _ _ admission.held
  have inventory : (available admission depth).Perm (.deformed admission.selected ::
      clocks admission.selected admission.ready 0 depth ++ current.current.stock.erase (.deformed admission.selected)) := by
    have first := (List.perm_cons_erase member).append_right (clocks admission.selected admission.ready 0 depth)
    have shuffle := (List.perm_append_comm :
      (current.current.stock.erase (.deformed admission.selected) ++ clocks admission.selected admission.ready 0 depth).Perm
        (clocks admission.selected admission.ready 0 depth ++ current.current.stock.erase (.deformed admission.selected)))
    simp only [List.cons_append] at first ⊢
    exact first.trans (shuffle.cons (.deformed admission.selected))
  simpa only [prefixExecution,trajectory_zero,Nat.zero_add,terminal] using
    block_paid admission.selected admission.ready 0 depth _ (available admission depth) inventory (available_held admission depth)

theorem generated_program {current : Occurrence frame} (admission : Admission current) (depth : Nat) :
    program admission depth = reactionBlock admission.selected admission.ready 0 depth ++
      CPS1Deformation.Source.program frame (some (.deformed (terminal admission depth))) current.current.pending := by
  rw [program,available_held]
  simpa only [actions,trajectory_zero,Nat.zero_add,terminal] using
    program_block admission.selected admission.ready 0 depth current.current.pending

theorem fired_prefix_and_suffix {current : Occurrence frame} (admission : Admission current) (depth : Nat) :
    execution admission depth =
      ⟨reactionBlock admission.selected admission.ready 0 depth ++ (suffix admission depth).fired,
        (suffix admission depth).remaining,(suffix admission depth).stock,(suffix admission depth).missing⟩ := by
  have paid := prefix_paid admission depth
  unfold prefixExecution at paid
  rw [execution,generated_program,execute_append_paid _ _ _ paid.2.1 paid.2.2.1]
  rw [paid.1]
  rfl

theorem continued_execution {current : Occurrence frame} (admission : Admission current) (depth : Nat) :
    (continued admission depth).current =
      ⟨(execution admission depth).stock,(actions admission depth ++ current.current.pending).drop
          (execution admission depth).fired.length,current.current.stages ++ [execution admission depth],
        (execution admission depth).missing⟩ := by
  simp only [continued,CPS1Deformation.Source.resume,CPS1Deformation.Source.advance,
    List.map_nil,List.append_nil,available,clocks,actions,execution,program]

theorem continued_final_stock {current : Occurrence frame} (admission : Admission current) (depth : Nat) :
    (continued admission depth).current.stock = (suffix admission depth).stock := by
  rw [continued_execution,fired_prefix_and_suffix]

theorem continued_pending {current : Occurrence frame} (admission : Admission current) (depth : Nat) :
    (continued admission depth).current.pending = current.current.pending.drop (suffix admission depth).fired.length := by
  rw [continued_execution,fired_prefix_and_suffix]
  simp only [List.length_append]
  rw [reaction_block_length]
  have size : (actions admission depth).length = depth := raw_block_length _ _ _ _
  simpa only [size] using (List.drop_length_add_append
    (l₁ := actions admission depth) (l₂ := current.current.pending) (suffix admission depth).fired.length)

theorem continued_previous {current : Occurrence frame} (admission : Admission current) (depth : Nat) :
    (continued admission depth).previous = current.previous := rfl

theorem continued_whole_inventory {current : Occurrence frame} (admission : Admission current)
    (depth : Nat) (species : Species frame) :
    (available admission depth).count species +
        (CPS1ResourceExecution.Inventory.credit (Reaction.products frame) (execution admission depth).fired).count species =
      (execution admission depth).stock.count species +
        (CPS1ResourceExecution.Inventory.debit (Reaction.reactants frame) (execution admission depth).fired).count species :=
  whole_inventory (program admission depth) (available admission depth) species

theorem continued_cut {current : Occurrence frame} (admission : Admission current) (depth : Nat)
    (missing : Species frame) (cut : (execution admission depth).missing = some missing) :
    ∃ reaction rest, (execution admission depth).remaining = reaction :: rest ∧
      (execution admission depth).stock.count missing < (reaction.reactants frame).count missing :=
  actual_cut (program admission depth) (available admission depth) missing cut

theorem terminal_ready {current : Occurrence frame} (admission : Admission current) (depth : Nat) :
    PulseReady (terminal admission depth) := trajectory_ready admission.selected admission.ready depth

theorem terminal_payment {current : Occurrence frame} (admission : Admission current) (depth : Nat) :
    0 < (terminal admission depth).reserve ∧
      (terminal admission depth).energy+(terminal admission depth).reserve =
        admission.selected.energy+admission.selected.reserve :=
  ⟨(terminal_ready admission depth).budget,trajectory_paid admission.selected admission.ready depth⟩

theorem terminal_source {current : Occurrence frame} (admission : Admission current) (depth : Nat) :
    (terminal admission depth).reference = admission.selected.reference :=
  trajectory_same_source admission.selected admission.ready depth

theorem generated_time_positive {current : Occurrence frame} (admission : Admission current) (index : Nat) :
    0 < timeAt admission.selected admission.ready index := trajectory_positive_time _ _ _

theorem continued_stock_good {current : Occurrence frame} (admission : Admission current) (depth : Nat)
    (good : GoodStock current.current.stock) : GoodStock (continued admission depth).current.stock :=
  resume_good current (actions admission depth) [] good

theorem continued_stock_noGuard {current : Occurrence frame} (admission : Admission current) (depth : Nat)
    (safe : NoGuardStock current.current.stock) : NoGuardStock (continued admission depth).current.stock :=
  resume_noGuard current (actions admission depth) [] safe

theorem auto_continue_generated (current : Occurrence frame) (state : Material frame)
    (held : heldCarrier frame current.current.stock = some (.deformed state)) (ready : PulseReady state)
    (depth : Nat) :
    autoContinue? current depth = some (continued (⟨state,ready,held⟩ : Admission current) depth) := by
  rw [autoContinue?,CPS1PositivePulse.NativeSource.auto_pulse_generated current state held ready]
  rfl

theorem next_previous (current : Occurrence frame) (depth : Nat) :
    (next current depth).previous = current.previous := by
  unfold next autoContinue?
  cases CPS1PositivePulse.NativeSource.autoPulse? current <;> rfl

end
end CPS1PositiveContinuation.NativeSource
