import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Offers
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {source : SourceQuota.Generated prepared}
  {catalogue : SourceQuota.Catalogue source.snapshot} {all : Candidates source catalogue}

abbrev code (index : Index prepared) := (Policy.initial input prepared.saved[index].point).source.val.code
abbrev Key (index : Index prepared) := Reaction.Key (code index)
abbrev Frame (index : Index prepared) := Feedback.Residual.Joint.Frame (code index)
def frameOf (index : Index prepared) (cell : Common.Cell all index) := Whole.frames (Common.project all index cell)
def frameSpec (index : Index prepared) := QuotaJoint.frames (scopes all index)
def keysOf (index : Index prepared) (frame : Frame index) := Feedback.Residual.keys (code index) frame.state frame.programs
def rawSpec (index : Index prepared) := (frameSpec (all := all) index).flatMap (keysOf index)
def keySpec (index : Index prepared) := (rawSpec (all := all) index).dedup
def indexProbes (index : Index prepared) : List (Probe all) := (tables all index).map fun table => ⟨index,table⟩
def tableCost (index : Index prepared) := Product.cost (fun _ : Key index => Reaction.moves (code index)) (keySpec (all := all) index)
def rawCost (index : Index prepared) (tailFrames : List (Frame index)) := (tailFrames.map fun frame => 2+(keysOf index frame).length).sum

theorem source_frames (index : Index prepared) :
    (Common.cells all index).flatMap (frameOf index) = frameSpec (all := all) index := by
  simp only [frameSpec,QuotaJoint.frames,scopes,Common.scopes,List.flatMap_map]
  rfl

def wrap (index : Index prepared) (fields : List (Key index)) (same : fields = keySpec (all := all) index)
    (table : ∀ key ∈ fields,Reaction.Move (code index)) : Probe all :=
  ⟨index,show ∀ key ∈ keySpec (all := all) index,Reaction.Move (code index) from same ▸ table⟩
abbrev TableQueue (index : Index prepared) := Product.Queue (Key := Key index)
  (Value := fun _ => Reaction.Move (code index)) (Output := Probe all)
def tableStart (index : Index prepared) (fields : List (Key index)) (same : fields = keySpec (all := all) index) : TableQueue (all := all) index :=
  [.build fields (wrap index fields same)]

theorem table_start_denote (index : Index prepared) (fields : List (Key index)) (same : fields = keySpec (all := all) index) :
    Product.denote (fun _ : Key index => Reaction.moves (code index)) (tableStart index fields same) = indexProbes (all := all) index := by
  cases same
  simp only [tableStart,Product.denote,List.flatMap_cons,List.flatMap_nil,List.append_nil,Product.Task.denote,indexProbes,
    Automatic.tables,QuotaJoint.tables,Feedback.Residual.Joint.tables]
  rfl

theorem table_start_rank (index : Index prepared) (fields : List (Key index)) (same : fields = keySpec (all := all) index) :
    Product.rank (fun _ : Key index => Reaction.moves (code index)) (tableStart index fields same) = tableCost (all := all) index := by
  cases same;rfl

inductive Task where
  | scope (index : Index prepared) (current : Common.Cursor all) (emitted : List (Common.Cell all index))
      (exact_source : emitted++current.denote all index = Common.cells all index)
  | frames (index : Index prepared) (remaining : List (Common.Cell all index)) (cached : List (Frame index))
      (exact_source : cached++remaining.flatMap (frameOf index) = frameSpec (all := all) index)
  | rawFrames (index : Index prepared) (remaining : List (Frame index)) (cached : List (Key index))
      (exact_source : cached++remaining.flatMap (keysOf index) = rawSpec (all := all) index)
  | rawKeys (index : Index prepared) (remaining : List (Key index)) (tailFrames : List (Frame index)) (cached : List (Key index))
      (exact_source : cached++remaining++tailFrames.flatMap (keysOf index) = rawSpec (all := all) index)
  | deduplicate (index : Index prepared) (remaining cached : List (Key index))
      (exact_source : cached++remaining.dedup = keySpec (all := all) index)
  | tables (index : Index prepared) (remaining : TableQueue (all := all) index)
abbrev Queue := List (Task (all := all))
def start : Queue (all := all) := (keys prepared).map fun index => .scope index (Common.start all) [] (Common.initial_denote all index)
def Task.denote : Task (all := all) → List (Probe all)
  | .scope index .. | .frames index .. | .rawFrames index .. | .rawKeys index .. | .deduplicate index .. => indexProbes (all := all) index
  | .tables index remaining => Product.denote (fun _ : Key index => Reaction.moves (code index)) remaining
def denote (queue : Queue (all := all)) := queue.flatMap Task.denote

theorem initial_denote : denote (start (all := all)) = probes all := by
  simp only [denote,start,List.flatMap_map,Task.denote,Review.probes,indexProbes]

def restCost (index : Index prepared) := rawCost index (frameSpec (all := all) index)+(rawSpec (all := all) index).length+tableCost (all := all) index+3
def Task.rank : Task (all := all) → Nat
  | .scope index current .. => current.rank all+(Common.cells all index).length+restCost (all := all) index+2
  | .frames index remaining .. => remaining.length+restCost (all := all) index+1
  | .rawFrames index remaining .. => rawCost index remaining+(rawSpec (all := all) index).length+tableCost (all := all) index+3
  | .rawKeys index remaining tailFrames .. => remaining.length+rawCost index tailFrames+(rawSpec (all := all) index).length+tableCost (all := all) index+4
  | .deduplicate index remaining .. => remaining.length+tableCost (all := all) index+2
  | .tables index remaining => Product.rank (fun _ : Key index => Reaction.moves (code index)) remaining+1
def rank (queue : Queue (all := all)) := (queue.map Task.rank).sum

inductive Event where
  | scope (index : Index prepared) (event : Common.Event all index)
  | scopeComplete (index : Index prepared)
  | frame (index : Index prepared) (cell : Common.Cell all index)
  | framesComplete (index : Index prepared)
  | rawFrame (index : Index prepared) (frame : Frame index)
  | rawKey (index : Index prepared) (key : Key index)
  | frameComplete (index : Index prepared)
  | rawComplete (index : Index prepared)
  | duplicate (index : Index prepared) (key : Key index)
  | distinct (index : Index prepared) (key : Key index)
  | beginTables (index : Index prepared)
  | table (index : Index prepared) (event : Product.Event (Key := Key index)
      (Value := fun _ => Reaction.Move (code index)) (Output := Probe all))
  | tablesComplete (index : Index prepared)

def step : Queue (all := all) → Option (Queue (all := all) × Option (Probe all) × Event (all := all))
  | [] => none
  | .scope index current emitted exact_source::rest => match observed : Common.step all index current with
    | none =>
        let complete : emitted = Common.cells all index := by
          simpa only [Common.stopped_has_no_residual all index current observed,List.append_nil] using exact_source
        some (.frames index emitted [] (by rw [complete];exact source_frames index)::rest,none,.scopeComplete index)
    | some (after,yielded,event) => some
        (.scope index after (emitted++yielded.toList) (by rw [List.append_assoc,←Common.one_step_conserves all index observed];exact exact_source)::rest,
          none,.scope index event)
  | .frames index [] cached exact_source::rest =>
      some (.rawFrames index cached [] (by
        have complete : cached = frameSpec (all := all) index := by simpa only [List.flatMap_nil,List.append_nil] using exact_source
        rw [complete];rfl)::rest,none,.framesComplete index)
  | .frames index (cell::remaining) cached exact_source::rest =>
      some (.frames index remaining (cached++frameOf index cell) (by simpa only [List.flatMap_cons,List.append_assoc] using exact_source)::rest,
        none,.frame index cell)
  | .rawFrames index [] cached exact_source::rest =>
      some (.deduplicate index cached [] (by
        have complete : cached = rawSpec (all := all) index := by simpa only [List.flatMap_nil,List.append_nil] using exact_source
        rw [complete];rfl)::rest,none,.rawComplete index)
  | .rawFrames index (frame::remaining) cached exact_source::rest =>
      some (.rawKeys index (keysOf index frame) remaining cached (by simpa only [List.flatMap_cons,List.append_assoc] using exact_source)::rest,
        none,.rawFrame index frame)
  | .rawKeys index [] tailFrames cached exact_source::rest =>
      some (.rawFrames index tailFrames cached (by simpa only [List.append_nil] using exact_source)::rest,none,.frameComplete index)
  | .rawKeys index (key::remaining) tailFrames cached exact_source::rest =>
      some (.rawKeys index remaining tailFrames (cached++[key]) (by simpa only [List.append_assoc,List.singleton_append] using exact_source)::rest,
        none,.rawKey index key)
  | .deduplicate index [] cached exact_source::rest =>
      let complete : cached = keySpec (all := all) index := by simpa only [List.dedup_nil,List.append_nil] using exact_source
      some (.tables index (tableStart index cached complete)::rest,none,.beginTables index)
  | .deduplicate index (key::remaining) cached exact_source::rest =>
      if inside : key ∈ remaining then
        some (.deduplicate index remaining cached (by simpa only [List.dedup_cons_of_mem inside] using exact_source)::rest,
          none,.duplicate index key)
      else some (.deduplicate index remaining (cached++[key]) (by
        simpa only [List.dedup_cons_of_notMem inside,List.append_assoc,List.singleton_append] using exact_source)::rest,
          none,.distinct index key)
  | .tables index remaining::rest => match observed : Product.step (fun _ : Key index => Reaction.moves (code index)) remaining with
    | none => some (rest,none,.tablesComplete index)
    | some (after,yielded,event) => some (.tables index after::rest,yielded,.table index event)

theorem one_step_conserves {before after : Queue (all := all)} {yielded : Option (Probe all)} {event : Event (all := all)}
    (observed : step before = some (after,yielded,event)) : denote before = yielded.toList++denote after := by
  cases before with
  | nil => cases observed
  | cons task rest =>
    cases task with
    | scope index current emitted exact_source =>
      dsimp only [step] at observed;split at observed
      all_goals cases Option.some.inj observed
      all_goals rfl
    | frames index remaining cached exact_source =>
      cases remaining <;> cases Option.some.inj observed
      all_goals rfl
    | rawFrames index remaining cached exact_source =>
      cases remaining <;> cases Option.some.inj observed
      all_goals rfl
    | rawKeys index remaining tailFrames cached exact_source =>
      cases remaining <;> cases Option.some.inj observed
      all_goals rfl
    | deduplicate index remaining cached exact_source =>
      cases remaining with
      | nil =>
        cases Option.some.inj observed
        simp only [denote,List.flatMap_cons,Task.denote,Option.toList_none,List.nil_append,table_start_denote]
      | cons key remaining =>
        dsimp only [step] at observed;split at observed
        all_goals cases Option.some.inj observed
        all_goals rfl
    | tables index remaining =>
      dsimp only [step] at observed;split at observed
      · rename_i stopped
        cases Option.some.inj observed
        have empty := (Product.stopped_iff_empty _ remaining).mp stopped
        simp only [denote,List.flatMap_cons,Task.denote,empty,Product.denote,List.flatMap_nil,Option.toList_none,List.nil_append]
      · rename_i after emitted event actual
        cases Option.some.inj observed
        have conserved := Product.one_step_conserves_order_and_multiplicity _ actual
        simp only [denote,List.flatMap_cons,Task.denote,conserved,List.append_assoc]

theorem step_decreases_rank {before after : Queue (all := all)} {yielded : Option (Probe all)} {event : Event (all := all)}
    (observed : step before = some (after,yielded,event)) : rank after+1 = rank before := by
  cases before with
  | nil => cases observed
  | cons task rest =>
    cases task with
    | scope index current emitted exact_source =>
      dsimp only [step] at observed;split at observed
      · rename_i stopped
        cases Option.some.inj observed
        have complete : emitted = Common.cells all index := by
          simpa only [Common.stopped_has_no_residual all index current stopped,List.append_nil] using exact_source
        have zero : current.rank all = 0 := by
          cases current with
          | outer remaining => cases remaining with
            | nil => rfl
            | cons entry tail => dsimp only [Common.step] at stopped;split at stopped <;> cases stopped
          | quotas owner remaining tail => cases remaining <;> cases stopped
          | entered => cases stopped
        simp only [rank,List.map_cons,List.sum_cons,Task.rank,complete,zero];omega
      · rename_i next emitted event actual
        cases Option.some.inj observed
        have reduced := Common.step_decreases_rank all index actual
        simp only [rank,List.map_cons,List.sum_cons,Task.rank];omega
    | frames index remaining cached exact_source =>
      cases remaining with
      | nil =>
        cases Option.some.inj observed
        have complete : cached = frameSpec (all := all) index := by simpa only [List.flatMap_nil,List.append_nil] using exact_source
        simp only [rank,List.map_cons,List.sum_cons,Task.rank,List.length_nil,restCost,complete];omega
      | cons cell remaining =>
        cases Option.some.inj observed
        simp only [rank,List.map_cons,List.sum_cons,Task.rank,List.length_cons];omega
    | rawFrames index remaining cached exact_source =>
      cases remaining with
      | nil =>
        cases Option.some.inj observed
        have complete : cached = rawSpec (all := all) index := by simpa only [List.flatMap_nil,List.append_nil] using exact_source
        simp only [rank,List.map_cons,List.sum_cons,Task.rank,rawCost,List.map_nil,List.sum_nil,complete];omega
      | cons frame remaining =>
        cases Option.some.inj observed
        simp only [rank,List.map_cons,List.sum_cons,Task.rank,rawCost];omega
    | rawKeys index remaining tailFrames cached exact_source =>
      cases remaining <;> cases Option.some.inj observed
      all_goals simp only [rank,List.map_cons,List.sum_cons,Task.rank,List.length_nil,List.length_cons];omega
    | deduplicate index remaining cached exact_source =>
      cases remaining with
      | nil =>
        cases Option.some.inj observed
        simp only [rank,List.map_cons,List.sum_cons,Task.rank,List.length_nil,table_start_rank];omega
      | cons key remaining =>
        dsimp only [step] at observed;split at observed
        all_goals cases Option.some.inj observed
        all_goals simp only [rank,List.map_cons,List.sum_cons,Task.rank,List.length_cons];omega
    | tables index remaining =>
      dsimp only [step] at observed;split at observed
      · rename_i stopped
        cases Option.some.inj observed
        have empty := (Product.stopped_iff_empty _ remaining).mp stopped
        simp only [rank,List.map_cons,List.sum_cons,Task.rank,empty,Product.rank,List.map_nil,List.sum_nil];omega
      · rename_i after emitted event actual
        cases Option.some.inj observed
        have reduced := Product.step_decreases_the_source_constructor_rank _ actual
        simp only [rank,List.map_cons,List.sum_cons,Task.rank];omega

theorem stopped_iff_empty (before : Queue (all := all)) : step before = none ↔ before = [] := by
  cases before with
  | nil => simp [step]
  | cons task rest =>
    cases task with
    | scope index current emitted exact_source => dsimp only [step];split <;> simp
    | frames index remaining cached exact_source => cases remaining <;> simp [step]
    | rawFrames index remaining cached exact_source => cases remaining <;> simp [step]
    | rawKeys index remaining tailFrames cached exact_source => cases remaining <;> simp [step]
    | deduplicate index remaining cached exact_source => cases remaining <;> dsimp only [step];all_goals first | (split <;> simp) | simp
    | tables index remaining => dsimp only [step];split <;> simp

variable (owner : Ready all)
inductive State where
  | building (remaining : Queue (all := all)) (cached : List (Probe all)) (conserved : cached++denote remaining = probes all)
  | challengers (probesCache : List (Probe all)) (probesExact : probesCache = probes all)
      (remaining : Offers.Cursor all) (cached : List (Offer all)) (conserved : cached++remaining.denote all = offers all)
  | running (cached : List (Probe all)) (complete : cached = probes all)
      (challengers : List (Offer all)) (challengersExact : challengers = offers all) (current : Enumeration.State owner)
def initial : State owner := .building start [] initial_denote
inductive Action where
  | source (event : Event (all := all))
  | handoff
  | challenger (event : Offers.Event all)
  | beginReview
  | policy (event : Enumeration.Action owner)
def move : State owner → Option (State owner × Action owner)
  | .building remaining cached conserved => match observed : step remaining with
    | none =>
        let complete : cached = probes all := by simpa only [(stopped_iff_empty remaining).mp observed,denote,List.flatMap_nil,List.append_nil] using conserved
        some (.challengers cached complete (Offers.start all) [] (Offers.initial_denote all),.handoff)
    | some (after,yielded,event) => some (.building after (cached++yielded.toList) (by
        rw [List.append_assoc,←one_step_conserves observed];exact conserved),.source event)
  | .challengers probesCache probesExact remaining cached conserved => match observed : Offers.step all remaining with
    | none =>
        let complete : cached = offers all := by
          simpa only [Offers.stopped_has_no_residual all remaining observed,List.append_nil] using conserved
        some (.running probesCache probesExact cached complete (Enumeration.start owner),.beginReview)
    | some (after,yielded,event) => some (.challengers probesCache probesExact after (cached++yielded.toList) (by
        rw [List.append_assoc,←Offers.one_step_conserves all observed];exact conserved),.challenger event)
  | .running cached complete challengers challengersExact current =>
    match observed : Enumeration.moveWith owner cached complete challengers challengersExact current with
    | none => none
    | some (after,event) => some (.running cached complete challengers challengersExact after,.policy event)
def State.finished : State owner → Bool
  | .building .. | .challengers .. => false
  | .running _ _ _ _ current => current.finished owner
def State.rank : State owner → Nat
  | .building remaining .. => Joint.rank remaining+1+(Offers.start all).rank all+1+(Enumeration.start owner).rank owner
  | .challengers _ _ remaining .. => remaining.rank all+1+(Enumeration.start owner).rank owner
  | .running _ _ _ _ current => current.rank owner

theorem move_none_iff_finished (before : State owner) : move owner before = none ↔ before.finished owner = true := by
  cases before with
  | building remaining cached conserved => dsimp only [move,State.finished];split <;> simp
  | challengers probesCache probesExact remaining cached conserved => dsimp only [move,State.finished];split <;> simp
  | running cached complete challengers challengersExact current =>
    dsimp only [move,State.finished];rw [Enumeration.moveWith_eq];split
    · rename_i stopped;simp only [Enumeration.move_none_iff_finished] at stopped;exact ⟨fun _ => stopped,fun _ => rfl⟩
    · rename_i next event observed
      have unfinished : current.finished owner ≠ true := fun finished => by
        have stopped := (Enumeration.move_none_iff_finished owner current).mpr finished;rw [stopped] at observed;cases observed
      exact ⟨(by intro impossible;cases impossible),fun finished => False.elim (unfinished finished)⟩

theorem each_step_progresses {before after : State owner} {action : Action owner}
    (observed : move owner before = some (after,action)) : after.rank owner < before.rank owner := by
  cases before with
  | building remaining cached conserved =>
    dsimp only [move] at observed;split at observed
    · cases Option.some.inj observed;simp only [State.rank];omega
    · rename_i next emitted event actual
      cases Option.some.inj observed
      have reduced := step_decreases_rank actual
      simp only [State.rank];omega
  | challengers probesCache probesExact remaining cached conserved =>
    dsimp only [move] at observed;split at observed
    · cases Option.some.inj observed;simp only [State.rank];omega
    · rename_i next emitted event actual
      cases Option.some.inj observed
      have reduced := Offers.step_progresses all actual
      simp only [State.rank];omega
  | running cached complete challengers challengersExact current =>
    dsimp only [move] at observed;rw [Enumeration.moveWith_eq] at observed;split at observed
    · cases observed
    · rename_i next event actual
      cases Option.some.inj observed
      exact Enumeration.each_paid_constructor_or_review_step_progresses owner actual

inductive History : State owner → State owner → List (Action owner) → Prop
  | nil (before) : History before before []
  | step {before middle after event work} (observed : move owner before = some (middle,event))
      (later : History middle after work) : History before after (event::work)
structure Run (before : State owner) (capacity : Nat) where
  private mk ::
  endpoint : State owner
  work : List (Action owner)
  history : History owner before endpoint work
  fits : work.length ≤ capacity

def execute : (capacity : Nat) → (before : State owner) → Run owner before capacity
  | 0,before => ⟨before,[],.nil before,by rfl⟩
  | capacity+1,before => match observed : move owner before with
    | none => ⟨before,[],.nil before,Nat.zero_le _⟩
    | some (after,event) => let later := execute capacity after
      ⟨later.endpoint,event::later.work,.step observed later.history,by have := later.fits;simpa only [List.length_cons] using Nat.succ_le_succ this⟩

theorem zero_credit_does_not_load_the_source (before : State owner) :
    (execute owner 0 before).endpoint = before ∧ (execute owner 0 before).work = [] := ⟨rfl,rfl⟩
theorem source_rank_finishes_the_whole_chain (capacity : Nat) (before : State owner) (enough : before.rank owner ≤ capacity) :
    (execute owner capacity before).endpoint.finished owner = true := by
  induction capacity generalizing before with
  | zero =>
    cases before with
    | building | challengers => simp_all [State.rank]
    | running cached complete challengers challengersExact current =>
      exact Enumeration.source_rank_completes_generation_and_full_review owner 0 current enough
  | succ capacity ih =>
    unfold execute;split
    · rename_i stopped;exact (move_none_iff_finished owner before).mp stopped
    · rename_i after event actual;exact ih after (by have := each_step_progresses owner actual;omega)
structure Generated where
  private mk ::
  execution : Run owner (initial owner) (Review.capacity owner)
  generated : execution = execute owner (Review.capacity owner) (initial owner)
def generate : Generated owner := ⟨execute owner (Review.capacity owner) (initial owner),rfl⟩
namespace Generated
variable {owner} (made : Generated owner)
def spent := made.execution.work.length
def ordinal (event : Fin made.execution.work.length) := Review.offset owner+event.val
theorem ordinal_bound (event : Fin made.execution.work.length) : made.ordinal event < owner.quota.val := by
  have fits := made.execution.fits;have covered := Review.offset_is_covered_by_the_same_invoice owner;have := event.isLt
  dsimp [ordinal,Review.capacity] at *;omega

def slot (index : Index prepared) (event : Fin made.execution.work.length) :
    Fin (((owner.release.programme.paid.funding.resultAt index).invoice (owner.release.programme.paid.all_paid index)).bill.units) :=
  ⟨made.ordinal event,by rw [((owner.release.programme.paid.funding.resultAt index).invoice (owner.release.programme.paid.all_paid index)).size];exact made.ordinal_bound event⟩
theorem slots_are_not_reused (index : Index prepared) : Function.Injective (made.slot index) := by
  intro first second same;apply Fin.ext
  have equal := congrArg (fun slot => slot.val) same
  dsimp only [slot,ordinal] at equal;omega
theorem all_old_slots_are_separate (index : Index prepared) (old : owner.release.Token) (event : Fin made.execution.work.length) :
    made.slot index event ≠ owner.release.slot index old := by
  intro same
  have bounded := Review.every_old_work_slot_precedes_the_new_tail owner old
  have equal := congrArg (fun slot => slot.val) same
  change Review.offset owner+event.val = owner.release.ordinal old at equal;omega
structure Allocation (index : Index prepared) (event : Fin made.execution.work.length) where
  private mk ::
  invoice : EscrowBudget.Charge.Invoice (owner.release.programme.paid.funding.resultAt index)
  slot : Fin invoice.bill.units
  operation : Action owner
  slot_exact : slot.val = made.ordinal event
  operation_exact : operation = made.execution.work[event]
def allocation (index : Index prepared) (event : Fin made.execution.work.length) : Allocation made index event :=
  ⟨(owner.release.programme.paid.funding.resultAt index).invoice (owner.release.programme.paid.all_paid index),made.slot index event,made.execution.work[event],rfl,rfl⟩
theorem every_event_uses_the_same_successful_invoice (index : Index prepared) (event : Fin made.execution.work.length) :
    (made.allocation index event).invoice.bill.payment.succeeded = true ∧
    (made.allocation index event).invoice.bill.units = owner.quota.val ∧
    (made.allocation index event).operation = made.execution.work[event] :=
  ⟨(made.allocation index event).invoice.paid,(made.allocation index event).invoice.size,rfl⟩
def unused := Review.capacity owner-made.spent
theorem one_tail_covers_all_phases : made.spent+made.unused = Review.capacity owner := by have := made.execution.fits;dsimp [spent,unused];omega

def completed : Option (Choice all) := match made.execution.endpoint with
  | .running _ _ _ _ (.searching (.released policy maximal)) => some (choice all (offer owner policy) maximal)
  | _ => none
def endpoint (index : Index prepared) : Binding.NativeCursor prepared.saved[index].point := match made.execution.endpoint with
  | .running _ _ _ _ (.searching (.released policy _)) => ((offer owner policy).view index).endpoint
  | _ => Review.Generated.retained (owner := owner) index
end Generated

def State.creditMark : State owner → Admission.Credit.Mark all
  | .challengers _ _ remaining _ _ => remaining.creditMark all
  | .running _ _ _ _ current => current.creditMark owner
  | .building .. => .idle
def Action.creditLog : Action owner → Admission.Credit.Log all
  | .challenger event => event.creditLog all
  | .policy event => event.creditLog owner
  | _ => .silent

theorem move_credit_rule {before after : State owner} {event : Action owner}
    (observed : move owner before = some (after,event)) :
    Admission.Credit.Rule (before.creditMark owner) (event.creditLog owner) (after.creditMark owner) := by
  cases before with
  | building remaining cached conserved =>
    dsimp only [move] at observed;split at observed
    all_goals cases Option.some.inj observed
    all_goals exact .fresh _ _ rfl
  | challengers probesCache probesExact remaining cached conserved =>
    dsimp only [move] at observed;split at observed
    · cases Option.some.inj observed;exact .fresh _ _ rfl
    · rename_i next emitted action actual
      cases Option.some.inj observed
      exact Offers.step_credit_rule all actual
  | running cached complete challengers challengersExact current =>
    dsimp only [move] at observed;split at observed
    · cases observed
    · rename_i next action actual
      cases Option.some.inj observed
      exact Enumeration.moveWith_credit_rule owner cached complete challengers challengersExact actual

theorem History.creditTrace {before after : State owner} {work : List (Action owner)}
    (history : History owner before after work) :
    Admission.Credit.Trace (before.creditMark owner) (after.creditMark owner) (work.map (Action.creditLog owner)) := by
  induction history with
  | nil => exact .nil _
  | step observed later ih => exact .step (move_credit_rule owner observed) ih

theorem Generated.all_native_receipts_have_actual_prior_credit_events (made : Generated owner) :
    Admission.Credit.Funded (made.execution.work.map (Action.creditLog owner)) := by
  exact (made.execution.history.creditTrace owner).funded

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint
namespace ReportAcquisition
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {source : SourceQuota.Generated prepared}
  {catalogue : SourceQuota.Catalogue source.snapshot} {all : Candidates source catalogue}
variable (owner : Ready all)
private theorem run_ext {before : Joint.State owner} {capacity : Nat} (first second : Joint.Run owner before capacity)
    (endpoint : first.endpoint = second.endpoint) (work : first.work = second.work) : first = second := by
  rcases first with ⟨first,firstWork,firstHistory,firstFits⟩
  rcases second with ⟨second,secondWork,secondHistory,secondFits⟩
  cases endpoint;cases work;rfl
private def finish (current : Joint.State owner) (work : List (Joint.Action owner))
    (history : Joint.History owner (Joint.initial owner) current work) (fits : work.length ≤ Review.capacity owner)
    (endpoint : current = (Joint.execute owner (Review.capacity owner) (Joint.initial owner)).endpoint)
    (exact_work : work = (Joint.execute owner (Review.capacity owner) (Joint.initial owner)).work) : Joint.Generated owner :=
  let run : Joint.Run owner (Joint.initial owner) (Review.capacity owner) := ⟨current,work,history,fits⟩
  ⟨run,run_ext owner run _ endpoint exact_work⟩
private theorem canonical (made : Joint.Generated owner) : made = Joint.generate owner := by
  rcases made with ⟨run,generated⟩;cases generated;rfl

inductive State where
  | running (left : Nat) (current : Joint.State owner) (work : List (Joint.Action owner))
      (history : Joint.History owner (Joint.initial owner) current work)
      (balance : work.length+left = Review.capacity owner)
      (endpoint : (Joint.execute owner left current).endpoint = (Joint.execute owner (Review.capacity owner) (Joint.initial owner)).endpoint)
      (conserved : work++(Joint.execute owner left current).work = (Joint.execute owner (Review.capacity owner) (Joint.initial owner)).work)
  | finished (made : Joint.Generated owner) (generated : made = Joint.generate owner)
def initial : State owner := .running (Review.capacity owner) (Joint.initial owner) [] (.nil _) (by simp) rfl rfl
inductive Event where
  | action (operation : Joint.Action owner)
  | complete (made : Joint.Generated owner) (generated : made = Joint.generate owner)

private theorem append_history {start before middle : Joint.State owner} {work : List (Joint.Action owner)}
    (history : Joint.History owner start before work) {event : Joint.Action owner}
    (actual : Joint.move owner before = some (middle,event)) : Joint.History owner start middle (work++[event]) := by
  induction history with
  | nil => exact .step actual (.nil _)
  | step first later ih => exact .step first (ih actual)

private theorem step_endpoint (left : Nat) (current after : Joint.State owner) (event : Joint.Action owner)
    (actual : Joint.move owner current = some (after,event)) :
    (Joint.execute owner (left+1) current).endpoint = (Joint.execute owner left after).endpoint := by
  rw [Joint.execute]
  split
  · rename_i absent;rw [absent] at actual;cases actual
  · rename_i next operation observed
    cases Option.some.inj (observed.symm.trans actual);rfl
private theorem step_work (left : Nat) (current after : Joint.State owner) (event : Joint.Action owner)
    (actual : Joint.move owner current = some (after,event)) :
    (Joint.execute owner (left+1) current).work = event::(Joint.execute owner left after).work := by
  rw [Joint.execute]
  split
  · rename_i absent;rw [absent] at actual;cases actual
  · rename_i next operation observed
    cases Option.some.inj (observed.symm.trans actual);rfl
private theorem stopped_endpoint (left : Nat) (current : Joint.State owner) (actual : Joint.move owner current = none) :
    (Joint.execute owner (left+1) current).endpoint = current := by
  rw [Joint.execute]
  split
  · rfl
  · rename_i next operation observed;rw [actual] at observed;cases observed
private theorem stopped_work (left : Nat) (current : Joint.State owner) (actual : Joint.move owner current = none) :
    (Joint.execute owner (left+1) current).work = [] := by
  rw [Joint.execute]
  split
  · rfl
  · rename_i next operation observed;rw [actual] at observed;cases observed

def move : State owner → Option (State owner × Event owner)
  | .running 0 current work history balance endpoint conserved =>
      let made := finish owner current work history (by omega) endpoint (by simpa only [Joint.execute,List.append_nil] using conserved)
      some (.finished made (canonical owner made),.complete made (canonical owner made))
  | .running (left+1) current work history balance endpoint conserved =>
      match actual : Joint.move owner current with
      | none =>
          let made := finish owner current work history (by omega)
            ((stopped_endpoint owner left current actual).symm.trans endpoint)
            (by rw [stopped_work owner left current actual,List.append_nil] at conserved;exact conserved)
          some (.finished made (canonical owner made),.complete made (canonical owner made))
      | some (after,event) =>
          some (.running left after (work++[event]) (append_history owner history actual)
            (by simp only [List.length_append,List.length_singleton];omega)
            ((step_endpoint owner left current after event actual).symm.trans endpoint)
            (by rw [step_work owner left current after event actual] at conserved
                simpa only [List.append_assoc,List.singleton_append] using conserved),.action event)
  | .finished .. => none

def State.rank : State owner → Nat | .running left .. => left+1 | .finished .. => 0
def State.done : State owner → Bool | .finished .. => true | _ => false
theorem progress {before after : State owner} {event : Event owner}
    (actual : move owner before = some (after,event)) : after.rank owner < before.rank owner := by
  cases before with
  | running left current work history balance endpoint conserved =>
      cases left with
      | zero => dsimp only [move] at actual;cases Option.some.inj actual;simp only [State.rank];omega
      | succ left =>
          dsimp only [move] at actual;split at actual
          all_goals cases Option.some.inj actual;simp only [State.rank];omega
  | finished => cases actual
theorem no_move_iff_done (before : State owner) : move owner before = none ↔ before.done owner = true := by
  cases before with
  | running left current work history balance endpoint conserved =>
      cases left with
      | zero => simp [move,State.done]
      | succ left => dsimp only [move,State.done];split <;> simp
  | finished => simp [move,State.done]
end ReportAcquisition
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint
