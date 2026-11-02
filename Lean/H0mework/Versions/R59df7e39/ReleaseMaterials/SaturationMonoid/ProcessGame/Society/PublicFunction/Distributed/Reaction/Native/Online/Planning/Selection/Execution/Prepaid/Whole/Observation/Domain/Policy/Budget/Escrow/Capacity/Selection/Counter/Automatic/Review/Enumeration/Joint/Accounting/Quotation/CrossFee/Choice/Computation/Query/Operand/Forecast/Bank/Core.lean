import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.Operand.Forecast.Restoration
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Window.Report.Manifest
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.Operand.Forecast.WholeTarget
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {driver : Feedback.Input seed.source.code} {cursor : Online.Cursor seed driver}
  {pricing : Future.Recovery.Pricing (Future.Recovery.Action cursor.model)} {n : Nat}
  {reference : Term cursor} {actor : P} {position : Nat}
  (scope : Whole.Scope cursor pricing n reference actor position) (span : Nat)
  (intent : Whole.Intent scope) (rival : Opponent cursor.source.val.code)

def boundFor (emitted : Future.Recovery.SameCodeTarget cursor.model) : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I) :=
  ⟨seed.base,seed.scope,emitted.val,emitted.indexed.property.1,emitted.indexed.property.2⟩
def fieldBound (completed : Done scope span intent rival) : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I) :=
  boundFor (source scope span intent rival completed)
abbrev FieldCursor (completed : Done scope span intent rival) :=
  Window.Report.Manifest.Cursor (fieldBound scope span intent rival completed) cursor.depth (Whole.extent scope span intent)
abbrev FieldDone (completed : Done scope span intent rival) :=
  Window.Report.Manifest.Completed (fieldBound scope span intent rival completed) cursor.depth (Whole.extent scope span intent)
def fields (completed : Done scope span intent rival) : FieldCursor scope span intent rival completed :=
  Window.Report.Manifest.initial _ _ _
-- This measure is used by proof fields only; ticket execution never evaluates the target.
noncomputable def fieldCost :=
  Window.Report.Manifest.capacity (boundFor (Whole.target scope span intent rival)) cursor.depth (Whole.extent scope span intent)
theorem fields_rank (completed : Done scope span intent rival) :
    (fields scope span intent rival completed).rank = fieldCost scope span intent rival := by
  rw [fields,Window.Report.Manifest.initial_rank]
  unfold fieldBound fieldCost
  rw [source_exact scope span intent rival completed]

abbrev RestoreCursor (completed : Done scope span intent rival) :=
  Restoration.Cursor cursor pricing (source scope span intent rival completed) (Whole.count scope span intent)
abbrev RestoreDone (completed : Done scope span intent rival) :=
  Restoration.Completed cursor pricing (source scope span intent rival completed) (Whole.count scope span intent)
abbrev RestoreEvent (completed : Done scope span intent rival) :=
  Restoration.Event cursor pricing (source scope span intent rival completed) (Whole.count scope span intent)
def restores (completed : Done scope span intent rival) : RestoreCursor scope span intent rival completed :=
  Restoration.initial cursor pricing (source scope span intent rival completed) (Whole.count scope span intent)
noncomputable def restoreCost :=
  Restoration.capacity cursor pricing (Whole.target scope span intent rival) (Whole.count scope span intent)
theorem restores_rank (completed : Done scope span intent rival) :
    (restores scope span intent rival completed).rank = restoreCost scope span intent rival := by
  rw [restores,Restoration.initial_rank]
  unfold restoreCost
  rw [source_exact scope span intent rival completed]

def fieldTensor (completed : Done scope span intent rival) (cache : FieldDone scope span intent rival completed)
    (recovery : RestoreDone scope span intent rival completed) : Planning.Tensor cursor :=
  let emitted := source scope span intent rival completed
  ⟨emitted.property ▸ cache.evaluation,recovery.read⟩
theorem fieldTensor_exact (completed : Done scope span intent rival) (cache : FieldDone scope span intent rival completed)
    (recovery : RestoreDone scope span intent rival completed) :
    fieldTensor scope span intent rival completed cache recovery = Whole.tensor scope span intent rival := by
  have restoration : recovery.read = Whole.restoration (pricing := pricing) (source scope span intent rival completed) (Whole.count scope span intent) :=
    funext fun word => recovery.read_exact word
  unfold fieldTensor
  rw [restoration,cache.evaluation_exact]
  exact tensor_exact scope span intent rival completed

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.Operand.Forecast.WholeTarget

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.Operand.Forecast.Bank
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {position : Nat}
  {pool : List (Offer (prepared := prepared) (position := position))}
  (tables : Tables.Completed pool)
abbrev Key := (index : Index prepared) × Forecast.Address tables index
instance addressDecidableEq (index : Index prepared) : DecidableEq (Forecast.Address tables index) :=
  fun a b => decidable_of_iff (a.table = b.table ∧ a.policy = b.policy) (by cases a;cases b;simp)
instance : DecidableEq (Key tables) := inferInstanceAs (DecidableEq (Sigma _))
def addresses : List (Key tables) := (keys prepared).flatMap fun index =>
  (List.finRange (tables.at index).length).flatMap fun table =>
    (List.finRange pool.length).map fun policy => ⟨index,⟨table,policy⟩⟩

theorem every_address (key : Key tables) : key ∈ addresses tables := by
  rcases key with ⟨index,⟨table,policy⟩⟩
  exact List.mem_flatMap.mpr ⟨index,List.mem_finRange _,List.mem_flatMap.mpr
    ⟨table,List.mem_finRange _,List.mem_map.mpr ⟨policy,List.mem_finRange _,rfl⟩⟩⟩

structure Value (key : Key tables) where
  private mk ::
  source : key.2.Done
  window : WholeTarget.FieldDone key.2.view.scope input.span key.2.view.intent key.2.rival source
  recovery : WholeTarget.RestoreDone key.2.view.scope input.span key.2.view.intent key.2.rival source
namespace Value
variable {tables} {key : Key tables}
def tensor (value : Value tables key) : Planning.Tensor (Policy.initial input prepared.saved[key.1].point) :=
  WholeTarget.fieldTensor key.2.view.scope input.span key.2.view.intent key.2.rival value.source value.window value.recovery
theorem exact_tensor (value : Value tables key) : value.tensor = (key.2.pick.view key.1).tensor key.2.rival :=
  WholeTarget.fieldTensor_exact key.2.view.scope input.span key.2.view.intent key.2.rival value.source value.window value.recovery
theorem restoration_from_cache (value : Value tables key)
    (word : List (Future.Recovery.Action (Policy.initial input prepared.saved[key.1].point).model))
    (inside : word ∈ Future.Recovery.capabilities (Policy.initial input prepared.saved[key.1].point).model (Policy.initial input prepared.saved[key.1].point).depth) :
    value.tensor.restoration word = (value.recovery.at word inside).value := value.recovery.read_from_cache word inside
theorem future_from_cache (value : Value tables key)
    (word : List (Future.Recovery.Action (Policy.initial input prepared.saved[key.1].point).model))
    (inside : word ∈ Future.Recovery.capabilities (Policy.initial input prepared.saved[key.1].point).model (Policy.initial input prepared.saved[key.1].point).depth) :
    value.tensor.future _ word = (value.recovery.at word inside).value.map Prod.fst := value.recovery.cached_future word inside
theorem funding_from_cache (value : Value tables key)
    (word : List (Future.Recovery.Action (Policy.initial input prepared.saved[key.1].point).model))
    (inside : word ∈ Future.Recovery.capabilities (Policy.initial input prepared.saved[key.1].point).model (Policy.initial input prepared.saved[key.1].point).depth) :
    value.tensor.funding _ word = (value.recovery.at word inside).value.bind Prod.snd := value.recovery.cached_funding word inside
end Value
abbrev Entry := (key : Key tables) × Value tables key
inductive Stage (key : Key tables) where
  | forecast (state : key.2.Start)
  | window (source : key.2.Done) (state : WholeTarget.FieldCursor key.2.view.scope input.span key.2.view.intent key.2.rival source)
  | restoring (source : key.2.Done) (window : WholeTarget.FieldDone key.2.view.scope input.span key.2.view.intent key.2.rival source)
      (state : WholeTarget.RestoreCursor key.2.view.scope input.span key.2.view.intent key.2.rival source)
structure Job where
  key : Key tables
  state : Stage tables key

def Job.initial (key : Key tables) : Job tables := ⟨key,.forecast key.2.start⟩
noncomputable def Stage.rank {key : Key tables} : Stage tables key → Nat
  | .forecast state => state.rank+WholeTarget.fieldCost key.2.view.scope input.span key.2.view.intent key.2.rival+WholeTarget.restoreCost key.2.view.scope input.span key.2.view.intent key.2.rival+3
  | .window _ state => state.rank+WholeTarget.restoreCost key.2.view.scope input.span key.2.view.intent key.2.rival+2
  | .restoring _ _ state => state.rank+1
noncomputable def Job.rank (job : Job tables) := job.state.rank
theorem Job.positive (job : Job tables) : 0 < job.rank := by
  rcases job with ⟨key,state⟩;cases state <;> dsimp only [Job.rank,Stage.rank] <;> omega
structure Completed where
  private mk ::
  items : List (Entry tables)
  exact_keys : items.map Sigma.fst = addresses tables
structure Cursor where
  private mk ::
  remaining : List (Job tables)
  cached : List (Entry tables)
  coherent : cached.map Sigma.fst++remaining.map Job.key = addresses tables

def initial : Cursor tables := ⟨(addresses tables).map (Job.initial tables),[],by simp [Function.comp_def,Job.initial]⟩
variable {tables}
noncomputable def Cursor.rank (cursor : Cursor tables) := (cursor.remaining.map (Job.rank tables)).sum
abbrev NativeEvent (key : Key tables) := Forecast.Event
  (code := (Policy.initial input prepared.saved[key.1].point).source.val.code)
  (schedule := WholeTarget.control key.2.view.scope key.2.view.intent)
  (input := WholeTarget.driving key.2.view.scope key.2.view.intent key.2.rival)
inductive Event (tables : Tables.Completed pool) where
  | advance (key : Key tables) (event : NativeEvent key)
  | begin (key : Key tables)
  | windowEvent (key : Key tables) (source : key.2.Done)
      (event : Window.Report.Manifest.Event (WholeTarget.fieldBound key.2.view.scope input.span key.2.view.intent key.2.rival source)
        (Policy.initial input prepared.saved[key.1].point).depth (Whole.extent key.2.view.scope input.span key.2.view.intent))
  | beginRestoration (key : Key tables)
  | restorationEvent (key : Key tables) (source : key.2.Done)
      (event : WholeTarget.RestoreEvent key.2.view.scope input.span key.2.view.intent key.2.rival source)
  | emit (key : Key tables)

def Cursor.move (cursor : Cursor tables) : Option (Event tables × Cursor tables) :=
  match remaining_actual : cursor.remaining with
  | [] => none
  | job::rest => match job.state with
    | .forecast state => match done : state.completed with
      | some made => some (.begin job.key,⟨⟨job.key,.window made (WholeTarget.fields job.key.2.view.scope input.span job.key.2.view.intent job.key.2.rival made)⟩::rest,cursor.cached,by
          have coherent := cursor.coherent;rw [remaining_actual] at coherent;simpa only [List.map_cons] using coherent⟩)
      | none => match moved : state.move with
        | none => False.elim (by have finished := (Forecast.Cursor.completed_iff_stopped state).mpr moved;rw [done] at finished;cases finished)
        | some (event,next) => some (.advance job.key event,⟨⟨job.key,.forecast next⟩::rest,cursor.cached,by
            have coherent := cursor.coherent;rw [remaining_actual] at coherent;simpa only [List.map_cons] using coherent⟩)
    | .window source state => match done : state.completed with
      | some window => some (.beginRestoration job.key,⟨⟨job.key,.restoring source window
          (WholeTarget.restores job.key.2.view.scope input.span job.key.2.view.intent job.key.2.rival source)⟩::rest,cursor.cached,by
          have coherent := cursor.coherent;rw [remaining_actual] at coherent;simpa only [List.map_cons] using coherent⟩)
      | none => match moved : state.move with
        | none => False.elim (by have finished := (Window.Report.Manifest.Cursor.completed_iff_stopped state).mpr moved;rw [done] at finished;cases finished)
        | some (event,next) =>
            let emitted := Event.windowEvent job.key source event
            some (emitted,⟨⟨job.key,.window source next⟩::rest,cursor.cached,by
              have coherent := cursor.coherent;rw [remaining_actual] at coherent;simpa only [List.map_cons] using coherent⟩)
    | .restoring source report state => match done : state.completed with
      | some recovery =>
          let value : Value tables job.key := ⟨source,report,recovery⟩
          some (.emit job.key,⟨rest,cursor.cached++[⟨job.key,value⟩],by
            have coherent := cursor.coherent;rw [remaining_actual] at coherent
            simpa only [List.map_append,List.map_cons,List.map_nil,List.append_assoc,List.cons_append,List.nil_append] using coherent⟩)
      | none => match moved : state.move with
        | none => False.elim (by have finished := (Restoration.Cursor.completed_iff_stopped state).mpr moved;rw [done] at finished;cases finished)
        | some (event,next) => some (.restorationEvent job.key source event,⟨⟨job.key,.restoring source report next⟩::rest,cursor.cached,by
            have coherent := cursor.coherent;rw [remaining_actual] at coherent;simpa only [List.map_cons] using coherent⟩)

def Cursor.completed (cursor : Cursor tables) : Option (Completed tables) :=
  match actual : cursor.remaining with
  | [] => some ⟨cursor.cached,by simpa only [actual,List.map_nil,List.append_nil] using cursor.coherent⟩
  | _::_ => none

theorem Cursor.move_decreases {before after : Cursor tables} {event : Event tables}
    (actual : before.move = some (event,after)) : after.rank+1 = before.rank := by
  rcases before with ⟨remaining,cached,coherent⟩
  cases remaining with
  | nil => cases actual
  | cons job rest =>
    rcases job with ⟨key,state⟩
    cases state with
    | forecast state =>
      dsimp only [Cursor.move] at actual
      split at actual
      · rename_i made done
        cases actual
        have zero := (Forecast.Cursor.stopped_iff_zero state).mp ((Forecast.Cursor.completed_iff_stopped _).mp (by rw [done];rfl))
        simp only [Cursor.rank,List.map_cons,List.sum_cons,Job.rank,Stage.rank,WholeTarget.fields_rank,zero];omega
      · rename_i done
        split at actual
        · rename_i stopped
          have complete := (Forecast.Cursor.completed_iff_stopped state).mpr stopped;rw [done] at complete;cases complete
        · rename_i native next moved
          cases actual;have decrease := Forecast.Cursor.move_decreases moved
          simp only [Cursor.rank,List.map_cons,List.sum_cons,Job.rank,Stage.rank];omega
    | window source state =>
      dsimp only [Cursor.move] at actual
      split at actual
      · rename_i made done
        cases actual
        have zero := (Window.Report.Manifest.Cursor.stopped_iff_zero state).mp ((Window.Report.Manifest.Cursor.completed_iff_stopped _).mp (by rw [done];rfl))
        simp only [Cursor.rank,List.map_cons,List.sum_cons,Job.rank,Stage.rank,WholeTarget.restores_rank,zero];omega
      · rename_i done
        split at actual
        · rename_i stopped
          have complete := (Window.Report.Manifest.Cursor.completed_iff_stopped state).mpr stopped;rw [done] at complete;cases complete
        · rename_i native next moved
          cases actual;have decrease := Window.Report.Manifest.Cursor.move_decreases moved
          simp only [Cursor.rank,List.map_cons,List.sum_cons,Job.rank,Stage.rank];omega
    | restoring source report state =>
      dsimp only [Cursor.move] at actual
      split at actual
      · rename_i made done;cases actual
        have zero := (Restoration.Cursor.stopped_iff_zero state).mp ((Restoration.Cursor.completed_iff_stopped _).mp (by rw [done];rfl))
        simp only [Cursor.rank,List.map_cons,List.sum_cons,Job.rank,Stage.rank,zero];omega
      · rename_i done;split at actual
        · rename_i stopped
          have complete := (Restoration.Cursor.completed_iff_stopped state).mpr stopped;rw [done] at complete;cases complete
        · rename_i native next moved;cases actual
          have decrease := Restoration.Cursor.move_decreases moved
          simp only [Cursor.rank,List.map_cons,List.sum_cons,Job.rank,Stage.rank];omega

theorem Cursor.completed_iff_stopped (cursor : Cursor tables) : cursor.completed.isSome = true ↔ cursor.move = none := by
  rcases cursor with ⟨remaining,cached,coherent⟩
  cases remaining with
  | nil => simp [Cursor.completed,Cursor.move]
  | cons job rest =>
    simp only [Cursor.completed,Option.isSome_none,Bool.false_eq_true,false_iff]
    rcases job with ⟨key,state⟩
    cases state with
    | forecast state =>
      dsimp only [Cursor.move]
      split
      · simp
      · rename_i pending
        split
        · rename_i stopped
          have complete := (Forecast.Cursor.completed_iff_stopped state).mpr stopped;rw [pending] at complete;cases complete
        · simp
    | window source state =>
      dsimp only [Cursor.move]
      split
      · simp
      · rename_i pending
        split
        · rename_i stopped
          have complete := (Window.Report.Manifest.Cursor.completed_iff_stopped state).mpr stopped;rw [pending] at complete;cases complete
        · simp
    | restoring source report state =>
      dsimp only [Cursor.move];split
      · simp
      · rename_i pending;split
        · rename_i stopped
          have complete := (Restoration.Cursor.completed_iff_stopped state).mpr stopped;rw [pending] at complete;cases complete
        · simp

theorem Cursor.stopped_iff_zero (cursor : Cursor tables) : cursor.move = none ↔ cursor.rank = 0 := by
  have finished := cursor.completed_iff_stopped
  rcases cursor with ⟨remaining,cached,coherent⟩
  cases remaining with
  | nil => simp [Cursor.move,Cursor.rank]
  | cons job rest =>
    have active : (⟨job::rest,cached,coherent⟩ : Cursor tables).move ≠ none := by
      intro stopped
      have impossible := finished.mpr stopped
      simp [Cursor.completed] at impossible
    have positive := Job.positive tables job
    simp only [active,false_iff,Cursor.rank,List.map_cons,List.sum_cons]
    omega

inductive History : Cursor tables → Cursor tables → List (Event tables) → Prop
  | nil (before) : History before before []
  | step {before middle after event work} (actual : before.move = some (event,middle))
      (later : History middle after work) : History before after (event::work)
structure Run (before : Cursor tables) (capacity : Nat) where
  private mk ::
  endpoint : Cursor tables
  work : List (Event tables)
  history : History before endpoint work
  covered : work.length ≤ capacity
  exhausted : endpoint.move = none ∨ work.length = capacity
  conservation : endpoint.rank+work.length = before.rank

def run : (capacity : Nat) → (before : Cursor tables) → Run before capacity
  | 0,before => ⟨before,[],.nil before,Nat.le_refl _,Or.inr rfl,by simp⟩
  | capacity+1,before => match actual : before.move with
    | none => ⟨before,[],.nil before,by simp,Or.inl actual,by simp⟩
    | some (event,next) =>
        let later := run capacity next
        ⟨later.endpoint,event::later.work,.step actual later.history,by have := later.covered;simp only [List.length_cons];omega,
          later.exhausted.imp_right (fun same => by simp only [List.length_cons,same]),by
            have := later.conservation;have := Cursor.move_decreases actual;simp only [List.length_cons];omega⟩

theorem run_sufficient (before : Cursor tables) (capacity : Nat) (enough : before.rank ≤ capacity) :
    (run capacity before).endpoint.completed.isSome = true := by
  apply (Cursor.completed_iff_stopped _).mpr
  rcases (run capacity before).exhausted with stopped | full
  · exact stopped
  apply (Cursor.stopped_iff_zero _).mpr
  have := (run capacity before).conservation;omega

def lookup (key : Key tables) : (items : List (Entry tables)) → key ∈ items.map Sigma.fst → Value tables key
  | [],inside => False.elim (List.not_mem_nil inside)
  | head::tail,inside => if same : head.1 = key then same ▸ head.2 else
      lookup key tail (by simpa only [List.map_cons,List.mem_cons,eq_comm (a := key) (b := head.1),same,false_or] using inside)

def Completed.at (cache : Completed tables) (key : Key tables) : Value tables key :=
  lookup key cache.items (by rw [cache.exact_keys];exact every_address tables key)

def Completed.tensor (cache : Completed tables) (index : Index prepared)
    (table : Fin (tables.at index).length) (policy : Fin pool.length) := (cache.at ⟨index,⟨table,policy⟩⟩).tensor

theorem Completed.tensor_exact (cache : Completed tables) (index : Index prepared)
    (table : Fin (tables.at index).length) (policy : Fin pool.length) :
    cache.tensor index table policy = ((pool[policy]).view index).tensor (Choice.rival pool index ((tables.at index)[table])) :=
  (cache.at ⟨index,⟨table,policy⟩⟩).exact_tensor
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.Operand.Forecast.Bank
