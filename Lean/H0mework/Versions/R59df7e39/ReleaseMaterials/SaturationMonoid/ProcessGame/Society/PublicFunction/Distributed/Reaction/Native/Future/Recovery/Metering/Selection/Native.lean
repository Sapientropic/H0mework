import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering.Selection.Catalogue
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering.Selection.Paid
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering.NativeProgram
open Institutions.Capitalism.Universal.Source.Program
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {old : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {R : Type}
def leaf (before : Current old) (requests : List (Action old)) :
    Mandate.Replay.Program.Code old.base old.scope (Mandate.Replay.Materialized old.base old.scope before requests) 1 :=
  .replay before requests (fun cache => .done cache)
inductive Code (R : Type) : Nat → Type where
  | done {depth} (value : R) : Code R depth
  | replay {depth} (before : Current old) (requests : List (Action old))
      (next : Mandate.Replay.Materialized old.base old.scope before requests → Code R depth) : Code R (depth+1)
  | catalogue {depth} (input : CatalogueSource.Input (Action old))
      (next : CatalogueSource.Execution input → Code R depth) : Code R (depth+1)
inductive Event (old : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)) where
  | replay (event : Mandate.Replay.Program.Event old.base old.scope)
  | catalogue (event : CatalogueSource.Event (Action old))
  | comparison (event : SearchSource.Selection.Event)
  | finish
def Event.search : SearchPaid.Event old → Event old
  | .replay event => .replay event
  | .comparison event => .comparison event
inductive Execution : {depth : Nat} → Code (old := old) R depth → Type where
  | private done {depth} (value : R) : Execution (.done value : Code R depth)
  | private replay {depth before requests} {next : Mandate.Replay.Materialized old.base old.scope before requests → Code R depth}
      (first : Mandate.Replay.Program.Execution (leaf (old := old) before requests)) (later : Execution (next first.value)) : Execution (.replay before requests next)
  | private catalogue {depth input} {next : CatalogueSource.Execution input → Code R depth}
      (first : CatalogueSource.Execution input) (later : Execution (next first)) : Execution (.catalogue input next)
def execute : {depth : Nat} → (code : Code (old := old) R depth) → Execution code
  | _,.done value => .done value
  | _,.replay before requests next =>
      let first := Mandate.Replay.Program.execute (leaf (old := old) before requests)
      .replay first (execute (next first.value))
  | _,.catalogue input next =>
      let first := CatalogueSource.execute input
      .catalogue first (execute (next first))
termination_by depth _ => depth
def Execution.value : {depth : Nat} → {code : Code (old := old) R depth} → Execution code → R
  | _,_,.done value => value
  | _,_,.replay _ later => later.value
  | _,_,.catalogue _ later => later.value
def Execution.work : {depth : Nat} → {code : Code (old := old) R depth} → Execution code → List (Event old)
  | _,_,.done _ => [.finish]
  | _,_,.replay first later => first.work.map Event.replay++later.work
  | _,_,.catalogue first later => first.work.map Event.catalogue++later.work
theorem Execution.unique : {depth : Nat} → {code : Code (old := old) R depth} → (first second : Execution code) → first = second
  | _,_,.done _,.done _ => rfl
  | _,_,.replay first later,.replay second rest => by
      cases first.unique second
      cases Execution.unique later rest;rfl
  | _,_,.catalogue first later,.catalogue second rest => by
      cases first.unique second
      cases Execution.unique later rest;rfl
termination_by depth _ _ _ => depth

inductive Cursor : {depth : Nat} → Code (old := old) R depth → Type where
  | ready {depth} (code : Code R depth) : Cursor code
  | replaying {depth before requests} {next : Mandate.Replay.Materialized old.base old.scope before requests → Code R depth}
      (session : Mandate.Replay.Program.Session (leaf (old := old) before requests)) : Cursor (.replay before requests next)
  | replayed {depth before requests} {next : Mandate.Replay.Materialized old.base old.scope before requests → Code R depth}
      (first : Mandate.Replay.Program.Execution (leaf (old := old) before requests)) (later : Cursor (next first.value)) : Cursor (.replay before requests next)
  | cataloguing {depth input} {next : CatalogueSource.Execution input → Code R depth}
      (session : CatalogueSource.Session input) : Cursor (.catalogue input next)
  | catalogued {depth input} {next : CatalogueSource.Execution input → Code R depth}
      (first : CatalogueSource.Execution input) (later : Cursor (next first)) : Cursor (.catalogue input next)
  | done {depth} (value : R) : Cursor (.done value : Code R depth)
def Cursor.work : {depth : Nat} → {code : Code (old := old) R depth} → Cursor code → List (Event old)
  | _,_,.ready _ => []
  | _,_,.replaying session => session.work.map Event.replay
  | _,_,.replayed first later => first.work.map Event.replay++later.work
  | _,_,.cataloguing session => session.work.map Event.catalogue
  | _,_,.catalogued first later => first.work.map Event.catalogue++later.work
  | _,_,.done _ => [.finish]
def Cursor.completed : {depth : Nat} → {code : Code (old := old) R depth} → Cursor code → Option (Execution code)
  | _,_,.ready _ => none
  | _,_,.replaying _ => none
  | _,_,.replayed first later => later.completed.map (Execution.replay first)
  | _,_,.cataloguing _ => none
  | _,_,.catalogued first later => later.completed.map (Execution.catalogue first)
  | _,_,.done value => some (.done value)
def Cursor.move : {depth : Nat} → {code : Code (old := old) R depth} → Cursor code → Option (Event old × Cursor code)
  | _,_,.ready (.done value) => some (.finish,.done value)
  | _,_,.ready (.replay before requests _) =>
      match (Mandate.Replay.Program.Session.initial (leaf (old := old) before requests)).move with
      | none => none
      | some (event,next) => some (.replay event,.replaying next)
  | _,_,.ready (.catalogue input _) =>
      match (CatalogueSource.Session.initial input).move with
      | none => none
      | some (event,next) => some (.catalogue event,.cataloguing next)
  | _,_,.replaying (next := next) session => match session.completed with
      | none => match session.move with
        | none => none
        | some (event,after) => some (.replay event,.replaying after)
      | some first => match (Cursor.ready (next first.value)).move with
        | none => none
        | some (event,after) => some (event,.replayed first after)
  | _,_,.replayed first later => match later.move with
      | none => none
      | some (event,after) => some (event,.replayed first after)
  | _,_,.cataloguing (next := next) session => match session.completed with
      | none => match session.move with
        | none => none
        | some (event,after) => some (.catalogue event,.cataloguing after)
      | some first => match (Cursor.ready (next first)).move with
        | none => none
        | some (event,after) => some (event,.catalogued first after)
  | _,_,.catalogued first later => match later.move with
      | none => none
      | some (event,after) => some (event,.catalogued first after)
  | _,_,.done _ => none
termination_by depth _ _ => depth
noncomputable def Cursor.rank : {depth : Nat} → {code : Code (old := old) R depth} → Cursor code → Nat
  | _,_,.ready code => (execute code).work.length
  | _,_,.replaying (next := next) session => session.rank+(execute (next (Mandate.Replay.Program.execute (leaf (old := old) _ _)).value)).work.length
  | _,_,.replayed _ later => later.rank
  | _,_,.cataloguing (next := next) session => session.rank+(execute (next (CatalogueSource.execute _))).work.length
  | _,_,.catalogued _ later => later.rank
  | _,_,.done _ => 0

theorem Cursor.conservation {depth : Nat} {code : Code (old := old) R depth} (current : Cursor code) :
    current.rank+current.work.length = (execute code).work.length := by
  cases current with
  | ready body => simp [Cursor.rank,Cursor.work]
  | done value => simp [Cursor.rank,Cursor.work,execute,Execution.work]
  | replaying session =>
    have paid := session.conservation
    simp only [Cursor.rank,Cursor.work,execute,Execution.work,List.length_append,List.length_map]
    omega
  | replayed first later =>
    cases first.unique (Mandate.Replay.Program.execute (leaf (old := old) _ _))
    have paid := Cursor.conservation later
    simp only [Cursor.rank,Cursor.work,execute,Execution.work,List.length_append,List.length_map]
    omega
  | cataloguing session =>
    have paid := session.conservation
    rw [←CatalogueSource.Execution.work_length (CatalogueSource.execute _)] at paid
    simp only [Cursor.rank,Cursor.work,execute,Execution.work,List.length_append,List.length_map]
    omega
  | catalogued first later =>
    cases first.unique (CatalogueSource.execute _)
    have paid := Cursor.conservation later
    simp only [Cursor.rank,Cursor.work,execute,Execution.work,List.length_append,List.length_map]
    omega
termination_by depth
private theorem replay_initial_moving (before : Current old) (requests : List (Action old)) :
    (Mandate.Replay.Program.Session.initial (leaf (old := old) before requests)).move ≠ none := by
  intro stopped
  have done := (Mandate.Replay.Program.Session.initial (leaf (old := old) before requests)).completed_iff_stopped.mpr stopped
  change false = true at done;cases done
private theorem catalogue_initial_moving (input : CatalogueSource.Input (Action old)) :
    (CatalogueSource.Session.initial input).move ≠ none := by
  intro stopped
  have done := (CatalogueSource.Session.initial input).completed_iff_stopped.mpr stopped
  change false = true at done;cases done
theorem Cursor.ready_moving {depth : Nat} (code : Code (old := old) R depth) : (Cursor.ready code).move ≠ none := by
  cases code with
  | done value => intro bad;simp only [Cursor.move] at bad;cases bad
  | replay before requests next =>
    have moving := replay_initial_moving before requests
    simp only [Cursor.move]
    split <;> simp_all
  | catalogue input next =>
    have moving := catalogue_initial_moving input
    simp only [Cursor.move]
    split <;> simp_all

theorem Cursor.move_appends {depth : Nat} {code : Code (old := old) R depth} {before after : Cursor code} {event : Event old}
    (actual : before.move = some (event,after)) : after.work = before.work++[event] := by
  cases before with
  | ready =>
    cases code with
    | done value => simp only [Cursor.move] at actual;cases actual;rfl
    | replay before requests next =>
      simp only [Cursor.move] at actual
      split at actual
      · cases actual
      · rename_i emitted after moved
        cases actual
        have appended := Mandate.Replay.Program.Session.move_appends moved
        have empty : (Mandate.Replay.Program.Session.initial (leaf (old := old) before requests)).work = [] := rfl
        rw [empty] at appended
        simpa only [Cursor.work,List.nil_append,List.map_cons,List.map_nil] using congrArg (List.map Event.replay) appended
    | catalogue input next =>
      simp only [Cursor.move] at actual
      split at actual
      · cases actual
      · rename_i emitted after moved
        cases actual
        have appended := CatalogueSource.Session.move_appends moved
        have empty : (CatalogueSource.Session.initial input).work = [] := rfl
        rw [empty] at appended
        simpa only [Cursor.work,List.nil_append,List.map_cons,List.map_nil] using congrArg (List.map Event.catalogue) appended
  | replaying session =>
    simp only [Cursor.move] at actual
    split at actual
    · split at actual
      · cases actual
      · rename_i emitted after moved
        cases actual
        simpa only [Cursor.work,List.map_append,List.map_cons,List.map_nil] using
          congrArg (List.map Event.replay) (Mandate.Replay.Program.Session.move_appends moved)
    · rename_i first done
      split at actual
      · cases actual
      · rename_i emitted after moved
        cases actual
        have origin := Mandate.Replay.Program.Session.completed_work done
        have appended := Cursor.move_appends moved
        dsimp only [Cursor.work] at appended ⊢
        rw [origin,appended];rfl
  | replayed first later =>
    simp only [Cursor.move] at actual
    split at actual
    · cases actual
    · rename_i emitted after moved
      cases actual
      dsimp only [Cursor.work]
      rw [Cursor.move_appends moved,List.append_assoc]
  | cataloguing session =>
    simp only [Cursor.move] at actual
    split at actual
    · split at actual
      · cases actual
      · rename_i emitted after moved
        cases actual
        simpa only [Cursor.work,List.map_append,List.map_cons,List.map_nil] using
          congrArg (List.map Event.catalogue) (CatalogueSource.Session.move_appends moved)
    · rename_i first done
      split at actual
      · cases actual
      · rename_i emitted after moved
        cases actual
        have origin := CatalogueSource.Session.completed_work done
        have appended := Cursor.move_appends moved
        dsimp only [Cursor.work] at appended ⊢
        rw [origin,appended];rfl
  | catalogued first later =>
    simp only [Cursor.move] at actual
    split at actual
    · cases actual
    · rename_i emitted after moved
      cases actual
      dsimp only [Cursor.work]
      rw [Cursor.move_appends moved,List.append_assoc]
  | done value => simp only [Cursor.move] at actual;cases actual
termination_by depth

theorem Cursor.move_decreases {depth : Nat} {code : Code (old := old) R depth} {before after : Cursor code} {event : Event old}
    (actual : before.move = some (event,after)) : after.rank+1 = before.rank := by
  have first := before.conservation
  have second := after.conservation
  have appended := congrArg List.length (Cursor.move_appends actual)
  simp only [List.length_append,List.length_singleton] at appended
  omega
theorem Cursor.completed_work {depth : Nat} {code : Code (old := old) R depth} {current : Cursor code} {made : Execution code}
    (actual : current.completed = some made) : made.work = current.work := by
  cases current with
  | ready body => cases actual
  | replaying session => cases actual
  | cataloguing session => cases actual
  | done value => cases actual;rfl
  | replayed first later =>
    dsimp only [Cursor.completed] at actual
    cases done : later.completed with
    | none => rw [done] at actual;cases actual
    | some result =>
      rw [done] at actual;cases actual
      dsimp only [Execution.work,Cursor.work]
      rw [Cursor.completed_work done]
  | catalogued first later =>
    dsimp only [Cursor.completed] at actual
    cases done : later.completed with
    | none => rw [done] at actual;cases actual
    | some result =>
      rw [done] at actual;cases actual
      dsimp only [Execution.work,Cursor.work]
      rw [Cursor.completed_work done]
termination_by depth

theorem Cursor.completed_iff_stopped {depth : Nat} {code : Code (old := old) R depth} (current : Cursor code) :
    current.completed.isSome = true ↔ current.move = none := by
  cases current with
  | ready =>
    have moving := Cursor.ready_moving code
    simp only [Cursor.completed,Option.isSome_none,Bool.false_eq_true,false_iff]
    exact moving
  | done value => simp [Cursor.completed,Cursor.move]
  | @replaying childDepth before requests next session =>
    simp only [Cursor.completed,Cursor.move]
    cases done : session.completed with
    | none =>
      have native := session.completed_iff_stopped
      cases moved : session.move <;> simp_all
    | some first =>
      have moving := Cursor.ready_moving (next first.value)
      cases moved : (Cursor.ready (next first.value)).move <;> simp_all
  | @cataloguing childDepth input next session =>
    simp only [Cursor.completed,Cursor.move]
    cases done : session.completed with
    | none =>
      have native := session.completed_iff_stopped
      cases moved : session.move <;> simp_all
    | some first =>
      have moving := Cursor.ready_moving (next first)
      cases moved : (Cursor.ready (next first)).move <;> simp_all
  | replayed first later =>
    have native := Cursor.completed_iff_stopped later
    simp only [Cursor.completed,Cursor.move]
    cases done : later.completed <;> cases moved : later.move <;> simp_all
  | catalogued first later =>
    have native := Cursor.completed_iff_stopped later
    simp only [Cursor.completed,Cursor.move]
    cases done : later.completed <;> cases moved : later.move <;> simp_all
termination_by depth

theorem Cursor.completed_zero {depth : Nat} {code : Code (old := old) R depth} {current : Cursor code} {made : Execution code}
    (actual : current.completed = some made) : current.rank = 0 := by
  have balance := current.conservation
  have work := Cursor.completed_work actual
  have unique := made.unique (execute code)
  rw [←work,unique] at balance
  omega
theorem Cursor.stopped_iff_zero {depth : Nat} {code : Code (old := old) R depth} (current : Cursor code) : current.move = none ↔ current.rank = 0 := by
  constructor
  · intro stopped
    have complete := current.completed_iff_stopped.mpr stopped
    cases done : current.completed with
    | none => rw [done] at complete;cases complete
    | some made => exact Cursor.completed_zero done
  · intro zero
    cases moved : current.move with
    | none => rfl
    | some event => have smaller := Cursor.move_decreases moved;rw [zero] at smaller;omega
variable {depth : Nat} {code : Code (old := old) R depth}
def initial (code : Code (old := old) R depth) : Cursor code := .ready code
theorem initial_rank : (initial code).rank = (execute code).work.length := rfl

inductive History : Cursor code → Cursor code → List (Event (old := old)) → Prop
  | nil (before) : History before before []
  | step {before middle after event work} (actual : before.move = some (event,middle))
      (later : History middle after work) : History before after (event::work)
theorem History.append : {before middle after : Cursor code} → {left right : List (Event (old := old))} →
    History before middle left → History middle after right → History before after (left++right)
  | _,_,_,_,_,.nil _,later => later
  | _,_,_,_,_,.step actual past,later => .step actual (History.append past later)
theorem History.conservation {before after : Cursor code} {work : List (Event (old := old))}
    (history : History before after work) : after.rank+work.length = before.rank := by
  induction history with
  | nil => simp
  | step actual _ ih => have := Cursor.move_decreases actual;simp only [List.length_cons];omega
structure Session (code : Code (old := old) R depth) where
  private mk ::
  current : Cursor code
  history : History (initial code) current current.work
def Session.initial (code : Code (old := old) R depth) : Session code := ⟨NativeProgram.initial code,.nil _⟩
abbrev Session.work (session : Session code) := session.current.work
noncomputable def Session.rank (session : Session code) := session.current.rank
def Session.completed (session : Session code) := session.current.completed
def Session.move (session : Session code) : Option (Event (old := old) × Session code) :=
  match actual : session.current.move with
  | none => none
  | some (event,next) => some (event,⟨next,by
      rw [Cursor.move_appends actual]
      exact session.history.append (.step actual (.nil _))⟩)
theorem Session.initial_rank : (Session.initial code).rank = (execute code).work.length := NativeProgram.initial_rank
theorem Session.move_appends {before after : Session code} {event : Event (old := old)}
    (actual : before.move = some (event,after)) : after.work = before.work++[event] := by
  dsimp only [Session.move] at actual
  split at actual
  · cases actual
  · rename_i emitted next moved
    cases actual;exact Cursor.move_appends moved
theorem Session.move_decreases {before after : Session code} {event : Event (old := old)}
    (actual : before.move = some (event,after)) : after.rank+1 = before.rank := by
  dsimp only [Session.move] at actual
  split at actual
  · cases actual
  · rename_i emitted next moved
    cases actual;exact Cursor.move_decreases moved
theorem Session.completed_work {session : Session code} {made : Execution code}
    (actual : session.completed = some made) : made.work = session.work := Cursor.completed_work actual
theorem Session.completed_iff_stopped (session : Session code) : session.completed.isSome = true ↔ session.move = none := by
  have native := session.current.completed_iff_stopped
  unfold Session.completed Session.move
  split <;> simp_all
theorem Session.stopped_iff_zero (session : Session code) : session.move = none ↔ session.rank = 0 := by
  have native := session.current.stopped_iff_zero
  unfold Session.move Session.rank
  split <;> simp_all
theorem Session.conservation (session : Session code) : session.rank+session.work.length = (execute code).work.length := by
  have balance := session.history.conservation
  rw [NativeProgram.initial_rank] at balance
  exact balance
theorem Session.covered (session : Session code) : session.work.length ≤ (execute code).work.length := by
  have balance := session.conservation;omega

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering.NativeProgram
