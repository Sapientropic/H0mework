import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.Meter.Payment
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.Operand.Tables
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {position : Nat}
variable {pool : List (Offer (prepared := prepared) (position := position))}
abbrev ScopeAt (index : Index prepared) := Whole.Scope (Policy.initial input prepared.saved[index].point) input.pricing input.future
  (Policy.reference input prepared.saved[index].point) input.actor input.position
abbrev code (index : Index prepared) := (Policy.initial input prepared.saved[index].point).source.val.code
abbrev Key (index : Index prepared) := Reaction.Key (code index)
abbrev Frame (index : Index prepared) := Feedback.Residual.Joint.Frame (code index)
abbrev Probe (pool : List (Offer (prepared := prepared) (position := position))) := (index : Index prepared) × Table pool index
def frameOf (index : Index prepared) (scope : ScopeAt index) := Whole.frames scope
def frameSpec (index : Index prepared) := QuotaJoint.frames (scopes pool index)
def keysOf (index : Index prepared) (frame : Frame index) := Feedback.Residual.keys (code index) frame.state frame.programs
def rawSpec (index : Index prepared) := (frameSpec (pool := pool) index).flatMap (keysOf index)
def keySpec (index : Index prepared) := (rawSpec (pool := pool) index).dedup
def indexProbes (pool : List (Offer (prepared := prepared) (position := position))) (index : Index prepared) : List (Probe pool) := (Choice.tables pool index).map fun table => ⟨index,table⟩
def tableCost (index : Index prepared) := Product.cost (fun _ : Key index => Reaction.moves (code index)) (keySpec (pool := pool) index)
def rawCost (index : Index prepared) (tailFrames : List (Frame index)) := (tailFrames.map fun frame => 2+(keysOf index frame).length).sum

def wrap (index : Index prepared) (fields : List (Key index)) (same : fields = keySpec (pool := pool) index)
    (table : ∀ key ∈ fields,Reaction.Move (code index)) : Probe pool :=
  ⟨index,show ∀ key ∈ keySpec (pool := pool) index,Reaction.Move (code index) from same ▸ table⟩
abbrev TableQueue (index : Index prepared) := Product.Queue (Key := Key index)
  (Value := fun _ => Reaction.Move (code index)) (Output := Probe pool)
def tableStart (index : Index prepared) (fields : List (Key index)) (same : fields = keySpec (pool := pool) index) : TableQueue (pool := pool) index :=
  [.build fields (wrap index fields same)]

theorem table_start_denote (index : Index prepared) (fields : List (Key index)) (same : fields = keySpec (pool := pool) index) :
    Product.denote (fun _ : Key index => Reaction.moves (code index)) (tableStart index fields same) = indexProbes (pool := pool) index := by
  cases same
  simp only [tableStart,Product.denote,List.flatMap_cons,List.flatMap_nil,List.append_nil,Product.Task.denote,indexProbes,
    Choice.tables,QuotaJoint.tables,Feedback.Residual.Joint.tables]
  rfl

theorem table_start_rank (index : Index prepared) (fields : List (Key index)) (same : fields = keySpec (pool := pool) index) :
    Product.rank (fun _ : Key index => Reaction.moves (code index)) (tableStart index fields same) = tableCost (pool := pool) index := by
  cases same;rfl
inductive Task where
  | scope (index : Index prepared) (remaining : List (Offer (prepared := prepared) (position := position))) (emitted : List (ScopeAt index))
      (exact_source : emitted++remaining.map (fun item => (item.view index).scope) = scopes pool index)
  | frames (index : Index prepared) (remaining : List (ScopeAt index)) (cached : List (Frame index))
      (exact_source : cached++remaining.flatMap (frameOf index) = frameSpec (pool := pool) index)
  | rawFrames (index : Index prepared) (remaining : List (Frame index)) (cached : List (Key index))
      (exact_source : cached++remaining.flatMap (keysOf index) = rawSpec (pool := pool) index)
  | rawKeys (index : Index prepared) (remaining : List (Key index)) (tailFrames : List (Frame index)) (cached : List (Key index))
      (exact_source : cached++remaining++tailFrames.flatMap (keysOf index) = rawSpec (pool := pool) index)
  | deduplicate (index : Index prepared) (remaining cached : List (Key index))
      (exact_source : cached++remaining.dedup = keySpec (pool := pool) index)
  | tables (index : Index prepared) (remaining : TableQueue (pool := pool) index)
abbrev Queue := List (Task (pool := pool))
def start : Queue (pool := pool) := (keys prepared).map fun index => .scope index pool [] rfl
def Task.denote : Task (pool := pool) → List (Probe pool)
  | .scope index .. | .frames index .. | .rawFrames index .. | .rawKeys index .. | .deduplicate index .. => indexProbes (pool := pool) index
  | .tables index remaining => Product.denote (fun _ : Key index => Reaction.moves (code index)) remaining
def denote (queue : Queue (pool := pool)) := queue.flatMap Task.denote
def probes (pool : List (Offer (prepared := prepared) (position := position))) := (keys prepared).flatMap (indexProbes pool)

theorem initial_denote : denote (start (pool := pool)) = probes pool := by
  simp only [denote,start,List.flatMap_map,Task.denote,probes,indexProbes]
  rfl

def restCost (index : Index prepared) := rawCost index (frameSpec (pool := pool) index)+(rawSpec (pool := pool) index).length+tableCost (pool := pool) index+3
def Task.rank : Task (pool := pool) → Nat
  | .scope index remaining .. => remaining.length+(scopes pool index).length+restCost (pool := pool) index+2
  | .frames index remaining .. => remaining.length+restCost (pool := pool) index+1
  | .rawFrames index remaining .. => rawCost index remaining+(rawSpec (pool := pool) index).length+tableCost (pool := pool) index+3
  | .rawKeys index remaining tailFrames .. => remaining.length+rawCost index tailFrames+(rawSpec (pool := pool) index).length+tableCost (pool := pool) index+4
  | .deduplicate index remaining .. => remaining.length+tableCost (pool := pool) index+2
  | .tables index remaining => Product.rank (fun _ : Key index => Reaction.moves (code index)) remaining+1
def rank (queue : Queue (pool := pool)) := (queue.map Task.rank).sum

inductive Event where
  | scope (index : Index prepared) (item : Offer (prepared := prepared) (position := position))
  | scopeComplete (index : Index prepared)
  | frame (index : Index prepared) (scope : ScopeAt index)
  | framesComplete (index : Index prepared)
  | rawFrame (index : Index prepared) (frame : Frame index)
  | rawKey (index : Index prepared) (key : Key index)
  | frameComplete (index : Index prepared)
  | rawComplete (index : Index prepared)
  | duplicate (index : Index prepared) (key : Key index)
  | distinct (index : Index prepared) (key : Key index)
  | beginTables (index : Index prepared)
  | table (index : Index prepared) (event : Product.Event (Key := Key index)
      (Value := fun _ => Reaction.Move (code index)) (Output := Probe pool))
  | tablesComplete (index : Index prepared)

def step : Queue (pool := pool) → Option (Queue (pool := pool) × Option (Probe pool) × Event (pool := pool))
  | [] => none
  | .scope index [] emitted exact_source::rest =>
      let complete : emitted = scopes pool index := by simpa only [List.map_nil,List.append_nil] using exact_source
      some (.frames index emitted [] (by rw [complete];rfl)::rest,none,.scopeComplete index)
  | .scope index (item::remaining) emitted exact_source::rest =>
      some (.scope index remaining (emitted++[(item.view index).scope]) (by
        simpa only [List.map_cons,List.append_assoc,List.singleton_append] using exact_source)::rest,none,.scope index item)
  | .frames index [] cached exact_source::rest =>
      some (.rawFrames index cached [] (by
        have complete : cached = frameSpec (pool := pool) index := by simpa only [List.flatMap_nil,List.append_nil] using exact_source
        rw [complete];rfl)::rest,none,.framesComplete index)
  | .frames index (cell::remaining) cached exact_source::rest =>
      some (.frames index remaining (cached++frameOf index cell) (by simpa only [List.flatMap_cons,List.append_assoc] using exact_source)::rest,
        none,.frame index cell)
  | .rawFrames index [] cached exact_source::rest =>
      some (.deduplicate index cached [] (by
        have complete : cached = rawSpec (pool := pool) index := by simpa only [List.flatMap_nil,List.append_nil] using exact_source
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
      let complete : cached = keySpec (pool := pool) index := by simpa only [List.dedup_nil,List.append_nil] using exact_source
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

theorem one_step_conserves {before after : Queue (pool := pool)} {yielded : Option (Probe pool)} {event : Event (pool := pool)}
    (observed : step before = some (after,yielded,event)) : denote before = yielded.toList++denote after := by
  cases before with
  | nil => cases observed
  | cons task rest =>
    cases task with
    | scope index remaining emitted exact_source =>
      cases remaining <;> cases Option.some.inj observed <;> rfl
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

theorem step_decreases_rank {before after : Queue (pool := pool)} {yielded : Option (Probe pool)} {event : Event (pool := pool)}
    (observed : step before = some (after,yielded,event)) : rank after+1 = rank before := by
  cases before with
  | nil => cases observed
  | cons task rest =>
    cases task with
    | scope index remaining emitted exact_source =>
      cases remaining with
      | nil =>
        cases Option.some.inj observed
        have complete : emitted = scopes pool index := by simpa only [List.map_nil,List.append_nil] using exact_source
        simp only [rank,List.map_cons,List.sum_cons,Task.rank,List.length_nil,complete];omega
      | cons item remaining =>
        cases Option.some.inj observed
        simp only [rank,List.map_cons,List.sum_cons,Task.rank,List.length_cons];omega
    | frames index remaining cached exact_source =>
      cases remaining with
      | nil =>
        cases Option.some.inj observed
        have complete : cached = frameSpec (pool := pool) index := by simpa only [List.flatMap_nil,List.append_nil] using exact_source
        simp only [rank,List.map_cons,List.sum_cons,Task.rank,List.length_nil,restCost,complete];omega
      | cons cell remaining =>
        cases Option.some.inj observed
        simp only [rank,List.map_cons,List.sum_cons,Task.rank,List.length_cons];omega
    | rawFrames index remaining cached exact_source =>
      cases remaining with
      | nil =>
        cases Option.some.inj observed
        have complete : cached = rawSpec (pool := pool) index := by simpa only [List.flatMap_nil,List.append_nil] using exact_source
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

theorem stopped_iff_empty (before : Queue (pool := pool)) : step before = none ↔ before = [] := by
  cases before with
  | nil => simp [step]
  | cons task rest =>
    cases task with
    | scope index remaining emitted exact_source => cases remaining <;> simp [step]
    | frames index remaining cached exact_source => cases remaining <;> simp [step]
    | rawFrames index remaining cached exact_source => cases remaining <;> simp [step]
    | rawKeys index remaining tailFrames cached exact_source => cases remaining <;> simp [step]
    | deduplicate index remaining cached exact_source => cases remaining <;> dsimp only [step];all_goals first | (split <;> simp) | simp
    | tables index remaining => dsimp only [step];split <;> simp

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.Operand.Tables
