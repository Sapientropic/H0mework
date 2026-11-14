import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.JointCircuit.Ports.Cost

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.BranchPorts
open InterferenceProgram
open SaturationMonoid.ComplexityProjection.SATSource.Affine
open PortEmbedding (Frame)
open FunctionalSubstitution (Instruction)

def Holds (frame : Frame) (calls : List Instruction) : Prop :=
  ∀ point, JointCircuit.read frame.state point=true → ∀ call ∈ calls, call.bind (frame.read point)=frame.read point

theorem initial_read (state : ArenaSource.State) (point : Nat → Bool) (i : Nat) (inside : i < state.arena.code.size) :
    (PortEmbedding.initial state).read point i=JointCircuit.lift state point i := by
  simp [PortEmbedding.Frame.read,PortEmbedding.read,PortEmbedding.ref,PortEmbedding.initial,Array.getD,inside,JointCircuit.lift]

def generate (state : ArenaSource.State) : ForcedBranches.Counted (List Instruction) :=
  let checked := JointCircuitCost.checked state.arena.code.toList
  if checked.value then
    let source := JointCircuitCost.formula state
    let calls := ForcedBranches.generate source.value []
    ⟨calls.value,checked.cells+source.cells+calls.cells+
      16*(CapacityMatching.RowCost.formulaCells source.value+ArenaCost.historySize calls.value+state.arena.code.size+state.relations.length+1)+24⟩
  else ⟨[],checked.cells+16*(state.arena.code.size+state.relations.length+1)+24⟩

theorem generate_holds (state : ArenaSource.State) : Holds (PortEmbedding.initial state) (generate state).value := by
  intro point accepted call member
  simp only [generate,JointCircuitCost.checked_value,JointCircuitCost.formula_value] at member
  split at member
  · rename_i checked
    have source : CNFFormula.eval (JointCircuit.formula state) ((PortEmbedding.initial state).read point)=true := by
      rw [JointCircuit.finite_eval_congr (JointCircuit.formula state) ((PortEmbedding.initial state).read point)
        (JointCircuit.lift state point) (initial_read state point),JointCircuit.formula_lift state checked point]
      exact accepted
    exact ForcedBranches.generate_entails (JointCircuit.formula state) [] ⟨triangular_nil,by simp [RowsWithin]⟩
      ((PortEmbedding.initial state).read point) (by
        rw [Acceptance.eval_compile,truth_bit,FunctionalMessage.empty_formula]
        exact source) call member
  · simp only [List.not_mem_nil] at member

def fromCall (frame : Frame) (call : Instruction) : Option (PortRelations.Offer frame) :=
  if call.address < frame.ports.size then
    let input := PortEmbedding.ref frame.state frame.ports call.address
    match JointCircuit.node frame.state input with
    | .input address =>
        let offer : PortRelations.Offer frame := ⟨input,address,call.body⟩
        if offer.allowed then some offer else none
    | _ => none
  else none

theorem fromCall_spec (frame : Frame) (call : Instruction) (offer : PortRelations.Offer frame)
    (found : fromCall frame call=some offer) :
    offer.allowed=true ∧ offer.body=call.body ∧
      ∀ point, call.bind (frame.read point)=frame.read point → offer.item.relation.read point=true := by
  simp only [fromCall] at found
  split at found
  · split at found
    · split at found
      · rename_i address shape allowed
        simp only [Option.some.injEq] at found
        subst offer
        refine ⟨allowed,rfl,?_⟩
        intro point fixed
        have equation := congrFun fixed call.address
        simp only [Instruction.bind,FunctionalSubstitution.bind,Function.update_self] at equation
        simp only [PortRelations.Offer.item,PortRelations.Offer.emission,ArenaAction.Relation.read,
          PortEmbedding.append_old,PortEmbedding.append_root]
        change (frame.read point call.address==truth (call.body.eval (frame.read point)))=true
        rw [equation,beq_self_eq_true]
      · cases found
    all_goals cases found
  · cases found

def choose (frame : Frame) : List Instruction → Option (PortRelations.Offer frame)
  | [] => none
  | call::rest => match fromCall frame call with
      | some offer => some offer
      | none => choose frame rest

theorem choose_spec (frame : Frame) (calls : List Instruction) (known : Holds frame calls)
    (offer : PortRelations.Offer frame) (found : choose frame calls=some offer) :
    offer.allowed=true ∧ (∃ call ∈ calls,offer.body=call.body) ∧
      ∀ point, JointCircuit.read frame.state point=true → offer.item.relation.read point=true := by
  induction calls with
  | nil => cases found
  | cons call rest ih =>
      cases picked : fromCall frame call with
      | none =>
          have tail := ih (fun point accepted other member => known point accepted other (by simp [member]))
            (by simpa only [choose,picked] using found)
          refine ⟨tail.1,?_,tail.2.2⟩
          obtain ⟨other,member,same⟩ := tail.2.1
          exact ⟨other,by simp [member],same⟩
      | some chosen =>
          simp only [choose,picked,Option.some.injEq] at found
          subst offer
          have spec := fromCall_spec frame call chosen picked
          exact ⟨spec.1,⟨call,by simp,spec.2.1⟩,fun point accepted => spec.2.2 point (known point accepted call (by simp))⟩

def update (frame : Frame) (calls : List Instruction) : PortUpdate.Output :=
  match choose frame calls with
  | none => ⟨frame,false,[],none⟩
  | some offer => PortUpdate.perform frame offer

theorem update_read (frame : Frame) (calls : List Instruction) (known : Holds frame calls) (point : Nat → Bool) :
    (update frame calls).value.read point=JointCircuit.read frame.state point := by
  cases picked : choose frame calls with
  | none => simp [update,picked,PortUpdate.Output.value,JointCircuit.Update.read,FunctionalAffine.legal]
  | some offer =>
      have spec := choose_spec frame calls known offer picked
      simp only [update,picked]
      exact PortUpdate.perform_read frame offer spec.1 spec.2.2 point

def step (state : ArenaSource.State) : PortUpdate.Output :=
  update (PortEmbedding.initial state) (generate state).value

theorem step_read (state : ArenaSource.State) (point : Nat → Bool) : (step state).value.read point=JointCircuit.read state point :=
  update_read (PortEmbedding.initial state) (generate state).value (generate_holds state) point

theorem extend_read (frame : Frame) (body : Fragment) (point : Nat → Bool) :
    (PortEmbedding.extend frame body).read point=frame.read point := by
  let produced := PortEmbedding.append frame.state frame.ports body
  have weight : produced.target.program.weight=produced.ref frame.state.program.weight := by
    apply Fin.ext
    change (ArenaAction.load (PortEmbedding.code frame.state frame.ports body)).mapping.getD (0+frame.state.program.weight.val) 0=
      (ArenaAction.load (PortEmbedding.code frame.state frame.ports body)).mapping.getD frame.state.program.weight.val 0
    rw [Nat.zero_add]
  funext i
  change truth ((run point produced.target.arena.code).getD
    ((frame.ports.map produced.ref).getD i produced.target.program.weight).val 0)=
      truth ((run point frame.state.arena.code).getD (frame.ports.getD i frame.state.program.weight).val 0)
  rw [weight]
  have mapped : (frame.ports.map produced.ref).getD i (produced.ref frame.state.program.weight)=
      produced.ref (frame.ports.getD i frame.state.program.weight) := by
    by_cases inside : i < frame.ports.size <;> simp [Array.getD,inside]
  rw [mapped]
  exact congrArg truth (PortEmbedding.append_old frame.state frame.ports body point (frame.ports.getD i frame.state.program.weight))

theorem bind_read (frame : Frame) (address : Nat) (root : Fin frame.state.arena.code.size) (point : Nat → Bool) :
    (PortEmbedding.bind frame address root).read point=
      frame.read (ArenaAction.Action.environment frame.state.arena address root point) := by
  let action := ArenaAction.apply frame.state.arena address root
  funext i
  change truth ((run point action.arena.code).getD
    ((frame.ports.map action.ref).getD i (action.ref frame.state.program.weight)).val 0)=
      truth ((run (ArenaAction.Action.environment frame.state.arena address root point) frame.state.arena.code).getD
        (frame.ports.getD i frame.state.program.weight).val 0)
  have mapped : (frame.ports.map action.ref).getD i (action.ref frame.state.program.weight)=
      action.ref (frame.ports.getD i frame.state.program.weight) := by
    by_cases inside : i < frame.ports.size <;> simp [Array.getD,inside]
  rw [mapped]
  exact congrArg truth (ArenaAction.apply_read frame.state.arena address root (frame.ports.getD i frame.state.program.weight) point)

theorem perform_read (frame : Frame) (offer : PortRelations.Offer frame) (allowed : offer.allowed=true) (point : Nat → Bool) :
    (PortUpdate.perform frame offer).frame.read point=frame.read (FunctionalSubstitution.fill (PortUpdate.perform frame offer).binding point) := by
  change (PortEmbedding.bind (PortEmbedding.extend frame offer.body) offer.address offer.emission.root).read point=
    frame.read ((PortUpdate.selected offer).bind point)
  have moved := bind_read (PortEmbedding.extend frame offer.body) offer.address offer.emission.root point
  have kept := extend_read frame offer.body (ArenaAction.Action.environment offer.emission.target.arena offer.address offer.emission.root point)
  have same := ArenaSource.selected_environment offer.emission.target offer.item allowed point
  exact moved.trans (kept.trans (congrArg frame.read same))

theorem update_transport (frame : Frame) (calls : List Instruction) (known : Holds frame calls) (point : Nat → Bool) :
    JointCircuit.read (update frame calls).frame.state point=
      JointCircuit.read frame.state (FunctionalSubstitution.fill (update frame calls).binding point) := by
  cases picked : choose frame calls with
  | none => simp only [update,picked,FunctionalSubstitution.fill,List.foldr_nil]
  | some offer =>
      have spec := choose_spec frame calls known offer picked
      have moved := PortUpdate.perform_transport frame offer spec.1 point
      simpa only [update,picked,PortUpdate.perform,Bool.not_false,Bool.true_and] using moved

theorem update_ports_read (frame : Frame) (calls : List Instruction) (known : Holds frame calls) (point : Nat → Bool) :
    (update frame calls).frame.read point=frame.read (FunctionalSubstitution.fill (update frame calls).binding point) := by
  cases picked : choose frame calls with
  | none => simp only [update,picked,FunctionalSubstitution.fill,List.foldr_nil]
  | some offer =>
      simp only [update,picked]
      exact perform_read frame offer (choose_spec frame calls known offer picked).1 point

theorem update_holds (frame : Frame) (calls : List Instruction) (known : Holds frame calls) : Holds (update frame calls).frame calls := by
  intro point accepted call member
  rw [update_ports_read frame calls known point]
  apply known _ _ call member
  rw [← update_transport frame calls known point]
  exact accepted

theorem body_size (calls : List Instruction) (call : Instruction) (member : call ∈ calls) :
    call.body.code.size ≤ ArenaCost.historySize calls := by
  induction calls with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | present
      · simp only [ArenaCost.historySize,FunctionalSchedule.Cost.inputSize_cons,FunctionalSchedule.Cost.instructionSize]; omega
      · have tail := ih present
        simp only [ArenaCost.historySize,FunctionalSchedule.Cost.inputSize_cons] at tail ⊢
        omega

theorem update_size (frame : Frame) (calls : List Instruction) (known : Holds frame calls) :
    (update frame calls).frame.state.arena.code.size ≤ frame.state.arena.code.size+ArenaCost.historySize calls+1 := by
  cases picked : choose frame calls with
  | none => simp only [update,picked]; omega
  | some offer =>
      obtain ⟨call,member,same⟩ := (choose_spec frame calls known offer picked).2.1
      have bound := body_size calls call member
      have size := PortUpdate.perform_size frame offer
      rw [same] at size
      simp only [update,picked]
      omega

theorem update_ports (frame : Frame) (calls : List Instruction) : (update frame calls).frame.ports.size=frame.ports.size := by
  cases picked : choose frame calls with
  | none =>
      have same : update frame calls=⟨frame,false,[],none⟩ := by simp [update,picked]
      rw [same]
  | some offer =>
      have same : update frame calls=PortUpdate.perform frame offer := by simp [update,picked]
      rw [same]
      exact PortUpdate.perform_ports frame offer

theorem update_count (frame : Frame) (calls : List Instruction) : (update frame calls).frame.state.relations.length=frame.state.relations.length := by
  cases picked : choose frame calls with
  | none =>
      have same : update frame calls=⟨frame,false,[],none⟩ := by simp [update,picked]
      rw [same]
  | some offer =>
      have same : update frame calls=PortUpdate.perform frame offer := by simp [update,picked]
      rw [same,PortUpdate.perform_state,ArenaSource.next_count]
      exact PortEmbedding.append_count _ _ _

theorem update_rejected (frame : Frame) (calls : List Instruction) : (update frame calls).rejected=false := by
  unfold update
  split <;> rfl

theorem update_idle (frame : Frame) (calls : List Instruction) (empty : (update frame calls).binding=[]) : (update frame calls).frame=frame := by
  cases picked : choose frame calls with
  | none => simp only [update,picked]
  | some offer => simp only [update,picked,PortUpdate.perform,List.cons_ne_self] at empty

theorem update_decreases (frame : Frame) (calls : List Instruction) (known : Holds frame calls) (nonempty : (update frame calls).binding≠[]) :
    ArenaTotal.remaining (update frame calls).frame.state<ArenaTotal.remaining frame.state := by
  cases picked : choose frame calls with
  | none => simp only [update,picked,ne_eq,not_true_eq_false] at nonempty
  | some offer =>
      simp only [update,picked]
      exact PortUpdate.perform_decreases frame offer (choose_spec frame calls known offer picked).1

def iterate : Nat → Frame → List Instruction → PortUpdate.Output
  | 0,frame,_ => ⟨frame,false,[],none⟩
  | fuel+1,frame,calls =>
      let first := update frame calls
      if first.binding.isEmpty then first else PortUpdate.combine first (iterate fuel first.frame calls)

theorem iterate_read (fuel : Nat) (frame : Frame) (calls : List Instruction) (known : Holds frame calls) (point : Nat → Bool) :
    (iterate fuel frame calls).value.read point=JointCircuit.read frame.state point := by
  induction fuel generalizing frame with
  | zero => simp [iterate,PortUpdate.Output.value,JointCircuit.Update.read,FunctionalAffine.legal]
  | succ fuel ih =>
      simp only [iterate]
      split
      · exact update_read frame calls known point
      · rw [PortUpdate.combine_value,JointIteration.combine_read,ih _ (update_holds frame calls known)]
        have first := update_read frame calls known point
        simpa only [PortUpdate.Output.value,JointCircuit.Update.read,update_rejected,Bool.not_false,Bool.true_and] using first

theorem iterate_ports (fuel : Nat) (frame : Frame) (calls : List Instruction) : (iterate fuel frame calls).frame.ports.size=frame.ports.size := by
  induction fuel generalizing frame with
  | zero => rfl
  | succ fuel ih =>
      by_cases stopped : (update frame calls).binding.isEmpty=true
      · have same : iterate (fuel+1) frame calls=update frame calls := by simp [iterate,stopped]
        rw [same]
        exact update_ports frame calls
      · have same : iterate (fuel+1) frame calls=PortUpdate.combine (update frame calls) (iterate fuel (update frame calls).frame calls) := by simp [iterate,stopped]
        rw [same]
        exact (ih (update frame calls).frame).trans (update_ports frame calls)

theorem iterate_count (fuel : Nat) (frame : Frame) (calls : List Instruction) : (iterate fuel frame calls).frame.state.relations.length=frame.state.relations.length := by
  induction fuel generalizing frame with
  | zero => rfl
  | succ fuel ih =>
      by_cases stopped : (update frame calls).binding.isEmpty=true
      · have same : iterate (fuel+1) frame calls=update frame calls := by simp [iterate,stopped]
        rw [same]
        exact update_count frame calls
      · have same : iterate (fuel+1) frame calls=PortUpdate.combine (update frame calls) (iterate fuel (update frame calls).frame calls) := by simp [iterate,stopped]
        rw [same]
        exact (ih (update frame calls).frame).trans (update_count frame calls)

theorem iterate_size (fuel : Nat) (frame : Frame) (calls : List Instruction) (known : Holds frame calls) :
    (iterate fuel frame calls).frame.state.arena.code.size ≤ frame.state.arena.code.size+fuel*(ArenaCost.historySize calls+1) := by
  induction fuel generalizing frame with
  | zero => simp [iterate]
  | succ fuel ih =>
      have first := update_size frame calls known
      have tail := ih (update frame calls).frame (update_holds frame calls known)
      simp only [iterate]
      split
      · nlinarith
      · change (iterate fuel (update frame calls).frame calls).frame.state.arena.code.size ≤ _
        nlinarith

def Settled (calls : List Instruction) (output : PortUpdate.Output) : Prop := (update output.frame calls).binding=[]

theorem iterate_settled (fuel : Nat) (frame : Frame) (calls : List Instruction) (known : Holds frame calls)
    (enough : ArenaTotal.remaining frame.state ≤ fuel) : Settled calls (iterate fuel frame calls) := by
  induction fuel generalizing frame with
  | zero =>
      change (update frame calls).binding=[]
      by_contra nonempty
      have less := update_decreases frame calls known nonempty
      omega
  | succ fuel ih =>
      simp only [iterate]
      split
      · rename_i stopped
        have empty : (update frame calls).binding=[] := List.isEmpty_iff.mp stopped
        unfold Settled
        rw [update_idle frame calls empty]
        exact empty
      · rename_i live
        have nonempty : (update frame calls).binding≠[] := by simpa only [List.isEmpty_iff] using live
        have less := update_decreases frame calls known nonempty
        exact ih (update frame calls).frame (update_holds frame calls known) (by omega)

def run (state : ArenaSource.State) : PortUpdate.Output :=
  iterate state.arena.code.size (PortEmbedding.initial state) (generate state).value

theorem run_read (state : ArenaSource.State) (point : Nat → Bool) : (run state).value.read point=JointCircuit.read state point :=
  iterate_read state.arena.code.size (PortEmbedding.initial state) (generate state).value (generate_holds state) point

theorem run_settled (state : ArenaSource.State) : Settled (generate state).value (run state) :=
  iterate_settled state.arena.code.size (PortEmbedding.initial state) (generate state).value
    (generate_holds state) (ArenaTotal.remaining_le_nodes state)

theorem run_size (state : ArenaSource.State) :
    (run state).frame.state.arena.code.size ≤ state.arena.code.size+state.arena.code.size*(ArenaCost.historySize (generate state).value+1) :=
  iterate_size state.arena.code.size (PortEmbedding.initial state) (generate state).value (generate_holds state)

theorem iterate_transport (fuel : Nat) (frame : Frame) (calls : List Instruction) (known : Holds frame calls) (point : Nat → Bool) :
    JointCircuit.read (iterate fuel frame calls).frame.state point=
      JointCircuit.read frame.state (FunctionalSubstitution.fill (iterate fuel frame calls).binding point) := by
  induction fuel generalizing frame with
  | zero => rfl
  | succ fuel ih =>
      simp only [iterate]
      split
      · exact update_transport frame calls known point
      · change JointCircuit.read (iterate fuel (update frame calls).frame calls).frame.state point=
          JointCircuit.read frame.state (FunctionalSubstitution.fill ((update frame calls).binding++
            (iterate fuel (update frame calls).frame calls).binding) point)
        rw [PortUpdate.fill_append,ih _ (update_holds frame calls known)]
        exact update_transport frame calls known _

theorem iterate_ports_read (fuel : Nat) (frame : Frame) (calls : List Instruction) (known : Holds frame calls) (point : Nat → Bool) :
    (iterate fuel frame calls).frame.read point=frame.read (FunctionalSubstitution.fill (iterate fuel frame calls).binding point) := by
  induction fuel generalizing frame with
  | zero => rfl
  | succ fuel ih =>
      simp only [iterate]
      split
      · exact update_ports_read frame calls known point
      · change (iterate fuel (update frame calls).frame calls).frame.read point=
          frame.read (FunctionalSubstitution.fill ((update frame calls).binding++
            (iterate fuel (update frame calls).frame calls).binding) point)
        rw [PortUpdate.fill_append,ih _ (update_holds frame calls known)]
        exact update_ports_read frame calls known _

theorem iterate_rejected (fuel : Nat) (frame : Frame) (calls : List Instruction) : (iterate fuel frame calls).rejected=false := by
  induction fuel generalizing frame with
  | zero => rfl
  | succ fuel ih =>
      simp only [iterate]
      split
      · exact update_rejected frame calls
      · exact ih _

theorem iterate_correct (fuel : Nat) (frame : Frame) (calls : List Instruction) (known : Holds frame calls) :
    (∃ point, JointCircuit.read (iterate fuel frame calls).frame.state point=true) ↔ ∃ point, JointCircuit.read frame.state point=true := by
  constructor
  · rintro ⟨point,accepted⟩
    exact ⟨FunctionalSubstitution.fill (iterate fuel frame calls).binding point,(iterate_transport fuel frame calls known point).symm.trans accepted⟩
  · rintro ⟨point,accepted⟩
    have result := (iterate_read fuel frame calls known point).trans accepted
    simp only [PortUpdate.Output.value,JointCircuit.Update.read,Bool.and_eq_true] at result
    exact ⟨point,result.2⟩

theorem update_valid (frame : Frame) (calls : List Instruction) (valid : ArenaSource.Valid frame.state) :
    ArenaSource.Valid (update frame calls).frame.state := by
  cases picked : choose frame calls with
  | none => simpa only [update,picked] using valid
  | some offer =>
      simp only [update,picked]
      exact PortUpdate.perform_valid frame valid offer

theorem iterate_valid (fuel : Nat) (frame : Frame) (calls : List Instruction) (known : Holds frame calls) (valid : ArenaSource.Valid frame.state) :
    ArenaSource.Valid (iterate fuel frame calls).frame.state := by
  induction fuel generalizing frame with
  | zero => exact valid
  | succ fuel ih =>
      simp only [iterate]
      split
      · exact update_valid frame calls valid
      · exact ih _ (update_holds frame calls known) (update_valid frame calls valid)

theorem run_correct (state : ArenaSource.State) :
    (∃ point, JointCircuit.read (run state).frame.state point=true) ↔ ∃ point, JointCircuit.read state point=true :=
  iterate_correct state.arena.code.size (PortEmbedding.initial state) (generate state).value (generate_holds state)

theorem run_rejected (state : ArenaSource.State) : (run state).rejected=false :=
  iterate_rejected state.arena.code.size (PortEmbedding.initial state) (generate state).value

theorem run_valid (state : ArenaSource.State) (valid : ArenaSource.Valid state) : ArenaSource.Valid (run state).frame.state :=
  iterate_valid state.arena.code.size (PortEmbedding.initial state) (generate state).value (generate_holds state) valid

def continueFrom (previous : PortUpdate.Output) : PortUpdate.Output :=
  if previous.rejected then previous else
    let generated := run previous.frame.state
    ⟨generated.frame,generated.rejected,previous.binding++generated.binding,generated.joint⟩

theorem continueFrom_read (previous : PortUpdate.Output) (point : Nat → Bool) :
    (continueFrom previous).value.read point=previous.value.read point := by
  by_cases rejected : previous.rejected=true
  · simp only [continueFrom,rejected,if_true]
  · rw [continueFrom,if_neg rejected]
    change (JointIteration.combine previous.value (run previous.frame.state).value).read point=previous.value.read point
    rw [JointIteration.combine_read,run_read]
    simp only [JointCircuit.Update.read,PortUpdate.Output.value,Bool.eq_false_iff.mpr rejected,Bool.not_false,Bool.true_and]

theorem continueFrom_correct (previous : PortUpdate.Output) :
    (∃ point, (!(continueFrom previous).rejected && JointCircuit.read (continueFrom previous).frame.state point)=true) ↔
      ∃ point, (!previous.rejected && JointCircuit.read previous.frame.state point)=true := by
  cases rejected : previous.rejected with
  | true => simp only [continueFrom,rejected,if_true]
  | false =>
      simp only [continueFrom,rejected,Bool.false_eq_true,if_false,run_rejected,Bool.not_false,Bool.true_and]
      exact run_correct previous.frame.state

theorem continueFrom_valid (previous : PortUpdate.Output) (valid : ArenaSource.Valid previous.frame.state) :
    ArenaSource.Valid (continueFrom previous).frame.state := by
  unfold continueFrom
  split
  · exact valid
  · exact run_valid previous.frame.state valid

def compile {n : Nat} (formula : CNFFormula n) (basis : List Row) : PortUpdate.Output :=
  continueFrom (PortCost.compile formula basis).value

theorem compile_read {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) (point : Nat → Bool) :
    (compile formula basis).value.read point=CNFFormula.eval formula (Gates.coordinate (Table.coordinates n basis) point) :=
  (continueFrom_read _ point).trans (PortCost.compile_read formula basis valid point)

theorem compile_valid {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) : ArenaSource.Valid (compile formula basis).frame.state := by
  apply continueFrom_valid
  rw [PortCost.compile_value]
  exact PortUpdate.compile_valid formula basis valid

def decide {n : Nat} (formula : CNFFormula n) (basis : List Row) : Bool :=
  let output := compile formula basis
  PortUpdate.stateDecision output.frame.state output.rejected

theorem decide_correct {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) : decide formula basis=true ↔
      ∃ point, CNFFormula.eval formula (Gates.coordinate (Table.coordinates n basis) point)=true := by
  let previous := (PortCost.compile formula basis).value
  have oldValid : ArenaSource.Valid previous.frame.state := by
    change ArenaSource.Valid (PortCost.compile formula basis).value.frame.state
    rw [PortCost.compile_value]
    exact PortUpdate.compile_valid formula basis valid
  have oldDecision : PortUpdate.stateDecision previous.frame.state previous.rejected=true ↔
      ∃ point, CNFFormula.eval formula (Gates.coordinate (Table.coordinates n basis) point)=true := by
    change PortUpdate.stateDecision (PortCost.compile formula basis).value.frame.state (PortCost.compile formula basis).value.rejected=true ↔ _
    rw [PortCost.compile_value]
    exact PortUpdate.decide_correct formula basis valid
  have original := (PortUpdate.stateDecision_iff previous.frame.state oldValid previous.rejected).symm.trans oldDecision
  exact (PortUpdate.stateDecision_iff _ (compile_valid formula basis valid) _).trans ((continueFrom_correct previous).trans original)

def projector {n : Nat} (formula : CNFFormula n) (source : Source n) : Source n :=
  let output := compile formula []
  fun point => if output.value.read (extendAssignment point) then source point else 0

theorem projector_original {n : Nat} (formula : CNFFormula n) (source : Source n) : projector formula source=zeroProjector formula source := by
  funext point
  simp only [projector,compile_read formula [] ⟨triangular_nil,by simp [RowsWithin]⟩,zeroProjector_apply]
  rw [FunctionalMessage.empty_formula]

def clausesBound (n c : Nat) : Nat := 4*n+3*n*n+3*c+1
def poolBound (n c : Nat) : Nat := ForcedBranches.Cost.outputStorage n (clausesBound n c)

theorem poolBound_mono (n N c C : Nat) (hn : n ≤ N) (hc : c ≤ C) : poolBound n c ≤ poolBound N C := by
  simp only [poolBound,clausesBound,ForcedBranches.Cost.outputStorage,ConditionalCandidateCost.priorStorage,
    ForcedBranches.Cost.branchStorage,ConditionalCandidateCost.branchStorage,ConditionalCandidateCost.instructionBound,
    ConditionalCandidateCost.bodyScale,ConditionalCandidateCost.Functional.callSize,AffineCarrier.Cost.cellBound,
    ForcedBranches.Cost.forceStorage]
  gcongr

theorem generate_storage (state : ArenaSource.State) : ArenaCost.historySize (generate state).value ≤ poolBound state.arena.code.size state.relations.length := by
  have length := JointCircuit.formula_length state
  have source := ForcedBranches.Cost.generate_storage (JointCircuitCost.formula state).value [] ⟨triangular_nil,by simp [RowsWithin]⟩
  rw [JointCircuitCost.formula_value] at source
  have bound : ForcedBranches.Cost.outputStorage state.arena.code.size (JointCircuit.formula state).length ≤ poolBound state.arena.code.size state.relations.length := by
    unfold poolBound ForcedBranches.Cost.outputStorage ConditionalCandidateCost.priorStorage clausesBound
    gcongr
  simp only [generate]
  split
  · rw [JointCircuitCost.formula_value]
    exact source.trans bound
  · simp only [ArenaCost.historySize,FunctionalSchedule.Cost.inputSize_nil,poolBound,ForcedBranches.Cost.outputStorage]
    omega

theorem generate_length (state : ArenaSource.State) :
    (generate state).value.length ≤ 3*clausesBound state.arena.code.size state.relations.length+state.arena.code.size*state.arena.code.size := by
  have original := ForcedBranches.Cost.generate_length (JointCircuitCost.formula state).value []
  rw [JointCircuitCost.formula_value] at original
  have length := JointCircuit.formula_length state
  simp only [generate]
  split
  · rw [JointCircuitCost.formula_value]
    simp only
    unfold clausesBound
    omega
  · simp

def inventoryBound (n c : Nat) : Nat := n+n*(poolBound n c+1)

theorem run_inventory (state : ArenaSource.State) :
    (run state).frame.state.arena.code.size ≤ inventoryBound state.arena.code.size state.relations.length := by
  exact (run_size state).trans (by unfold inventoryBound; gcongr; exact generate_storage state)

theorem continueFrom_size (previous : PortUpdate.Output) :
    (continueFrom previous).frame.state.arena.code.size ≤ inventoryBound previous.frame.state.arena.code.size previous.frame.state.relations.length := by
  simp only [continueFrom]
  split
  · simp only [inventoryBound]; omega
  · exact run_inventory previous.frame.state

theorem prior_count {n : Nat} (formula : CNFFormula n) (basis : List Row) :
    (PortCost.compile formula basis).value.frame.state.relations.length ≤ 3*formula.length+n*n := by
  have count := PortCost.prepared_count formula basis
  rw [PortCost.compile_value]
  change (PortUpdate.continueFrom (JointRelationCost.compile formula basis).value).frame.state.relations.length ≤ _
  have unchanged (previous : JointCircuit.Update) : (PortUpdate.continueFrom previous).frame.state.relations.length=previous.state.relations.length := by
    by_cases rejected : previous.rejected=true
    · have same : PortUpdate.continueFrom previous=⟨PortEmbedding.initial previous.state,true,previous.binding,previous.joint⟩ := by
        simp [PortUpdate.continueFrom,rejected]
      rw [same]
      rfl
    · have same : PortUpdate.continueFrom previous=⟨(PortUpdate.run previous.state).frame,(PortUpdate.run previous.state).rejected,
        previous.binding++(PortUpdate.run previous.state).binding,(PortUpdate.run previous.state).joint⟩ := by
          simp [PortUpdate.continueFrom,rejected]
      rw [same]
      exact PortUpdate.iterate_count _ _
  rw [unchanged]
  exact count

theorem inventoryBound_mono (n N c C : Nat) (hn : n ≤ N) (hc : c ≤ C) : inventoryBound n c ≤ inventoryBound N C := by
  unfold inventoryBound
  gcongr
  exact poolBound_mono _ _ _ _ hn hc

theorem compile_size {n : Nat} (formula : CNFFormula n) (basis : List Row) (valid : Triangular basis ∧ RowsWithin n basis) :
    (compile formula basis).frame.state.arena.code.size ≤
      inventoryBound (PortCost.capacity (PortCost.capacity (ArenaSource.sourceBound n formula.length (Extract.literalCount formula))))
        (3*formula.length+n*n) := by
  have size := PortUpdate.compile_size formula basis valid
  rw [← PortCost.compile_value] at size
  exact (continueFrom_size (PortCost.compile formula basis).value).trans
    (inventoryBound_mono _ _ _ _ size (prior_count formula basis))

end SaturationMonoid.ComplexityProjection.SATSource.BranchPorts
