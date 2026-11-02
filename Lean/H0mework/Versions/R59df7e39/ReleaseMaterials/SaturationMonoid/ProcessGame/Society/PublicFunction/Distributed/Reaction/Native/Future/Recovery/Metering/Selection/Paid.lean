import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering.Selection.Comparison
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering.SearchPaid
open Institutions.Capitalism.Universal.Source.Program
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {old : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {oldDepth : Nat} {word : List (Action old)}
  {stage : SearchSource.Point (old := old) (oldDepth := oldDepth) (word := word)}
  {catalogue : List (List (Action old))}
inductive Event (old : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)) where
  | replay (event : Mandate.Replay.Program.Event old.base old.scope)
  | comparison (event : SearchSource.Selection.Event)
structure Execution (stage : SearchSource.Point (old := old) (oldDepth := oldDepth) (word := word)) (catalogue : List (List (Action old))) where
  private mk ::
  source : SearchSource.Execution stage catalogue
  selected : SearchSource.Selection.Execution source.value
def execute (stage : SearchSource.Point (old := old) (oldDepth := oldDepth) (word := word)) (catalogue : List (List (Action old))) : Execution stage catalogue :=
  let first := SearchSource.execute stage catalogue
  ⟨first,SearchSource.Selection.execute first.value⟩
def Execution.value (made : Execution stage catalogue) := made.source.value
def Execution.winner (made : Execution stage catalogue) := made.selected.winner
def Execution.endpoint (made : Execution stage catalogue) := made.selected.endpoint
def Execution.work (made : Execution stage catalogue) : List (Event old) :=
  made.source.work.map Event.replay++made.selected.work.map Event.comparison
def Event.replayed : Event old → Option (Mandate.Replay.Program.Event old.base old.scope)
  | .replay event => some event
  | .comparison _ => none
def Event.compared : Event old → Option SearchSource.Selection.Event
  | .replay _ => none
  | .comparison event => some event
theorem Execution.replay_work (made : Execution stage catalogue) : made.work.filterMap Event.replayed = made.source.work := by
  simp [Execution.work,Event.replayed,List.filterMap_map]
theorem Execution.comparison_work (made : Execution stage catalogue) : made.work.filterMap Event.compared = made.selected.work := by
  simp [Execution.work,Event.compared,List.filterMap_map]
theorem Execution.comparison_count (made : Execution stage catalogue) : (made.work.filterMap Event.compared).length = catalogue.length := by
  rw [made.comparison_work,made.selected.work_length]
theorem Execution.work_length (made : Execution stage catalogue) : made.work.length = made.source.work.length+catalogue.length := by
  simp only [Execution.work,List.length_append,List.length_map,made.selected.work_length]
theorem Execution.chosen (made : Execution stage catalogue) : made.winner.row.proposal = choose stage catalogue := made.selected.chosen
theorem Execution.endpoint_exact (made : Execution stage catalogue) : made.endpoint = restored stage catalogue := made.selected.endpoint_exact
theorem Execution.unique (first second : Execution stage catalogue) : first = second := by
  rcases first with ⟨a,x⟩;rcases second with ⟨b,y⟩
  cases a.unique b;cases x.unique y;rfl

inductive Cursor (stage : SearchSource.Point (old := old) (oldDepth := oldDepth) (word := word)) (catalogue : List (List (Action old))) where
  | scoring (session : SearchSource.Session stage catalogue)
  | selecting (source : SearchSource.Execution stage catalogue) (session : SearchSource.Selection.Session source.value)
def initial (stage : SearchSource.Point (old := old) (oldDepth := oldDepth) (word := word)) (catalogue : List (List (Action old))) : Cursor stage catalogue :=
  .scoring (Mandate.Replay.Program.Session.initial (SearchSource.program stage catalogue))
def Cursor.work : Cursor stage catalogue → List (Event old)
  | .scoring session => session.work.map Event.replay
  | .selecting source session => source.work.map Event.replay++session.work.map Event.comparison
def Cursor.completed : Cursor stage catalogue → Option (Execution stage catalogue)
  | .scoring session => match session.completed with
    | none => none
    | some source => match (SearchSource.Selection.Session.initial source.value).completed with
      | none => none
      | some selected => some ⟨source,selected⟩
  | .selecting source session => match session.completed with
    | none => none
    | some selected => some ⟨source,selected⟩
def Cursor.move : Cursor stage catalogue → Option (Event old × Cursor stage catalogue)
  | .scoring session => match session.completed with
    | none => match session.move with
      | some (event,next) => some (.replay event,.scoring next)
      | none => none
    | some source => match (SearchSource.Selection.Session.initial source.value).move with
      | none => none
      | some (event,next) => some (.comparison event,.selecting source next)
  | .selecting source session => match session.move with
    | none => none
    | some (event,next) => some (.comparison event,.selecting source next)
noncomputable def Cursor.rank : Cursor stage catalogue → Nat
  | .scoring session => session.rank+catalogue.length
  | .selecting _ session => session.rank
theorem Cursor.move_decreases {before after : Cursor stage catalogue} {event : Event old}
    (actual : before.move = some (event,after)) : after.rank+1 = before.rank := by
  cases before with
  | scoring session =>
    dsimp only [Cursor.move] at actual
    split at actual
    · rename_i pending
      split at actual
      · rename_i emitted next moved
        cases actual
        have smaller := Mandate.Replay.Program.Session.move_decreases moved
        dsimp only [Cursor.rank];omega
      · rename_i stopped
        have complete := session.completed_iff_stopped.mpr stopped;rw [pending] at complete;cases complete
    · rename_i source done
      split at actual
      · cases actual
      · rename_i emitted next moved
        cases actual
        have zero := session.stopped_iff_zero.mp (session.completed_iff_stopped.mp (by rw [done];rfl))
        have smaller := SearchSource.Selection.Session.move_decreases moved
        have bound := (SearchSource.Selection.Session.initial source.value).conservation
        change (SearchSource.Selection.Session.initial source.value).rank+0 = catalogue.length at bound
        dsimp only [Cursor.rank];omega
  | selecting source session =>
    dsimp only [Cursor.move] at actual
    split at actual
    · cases actual
    · rename_i emitted next moved
      cases actual;exact SearchSource.Selection.Session.move_decreases moved

theorem Cursor.move_appends {before after : Cursor stage catalogue} {event : Event old}
    (actual : before.move = some (event,after)) : after.work = before.work++[event] := by
  cases before with
  | scoring session =>
    dsimp only [Cursor.move] at actual
    split at actual
    · rename_i pending
      split at actual
      · rename_i emitted next moved
        cases actual
        change next.work.map Event.replay = session.work.map Event.replay++[Event.replay emitted]
        rw [Mandate.Replay.Program.Session.move_appends moved,List.map_append];rfl
      · rename_i stopped
        have complete := session.completed_iff_stopped.mpr stopped;rw [pending] at complete;cases complete
    · rename_i source done
      split at actual
      · cases actual
      · rename_i emitted next moved
        cases actual
        have original := Mandate.Replay.Program.Session.completed_work done
        have appended := SearchSource.Selection.Session.move_appends moved
        change source.work.map Event.replay++next.work.map Event.comparison = session.work.map Event.replay++[Event.comparison emitted]
        rw [original,appended];rfl
  | selecting source session =>
    dsimp only [Cursor.move] at actual
    split at actual
    · cases actual
    · rename_i emitted next moved
      cases actual
      change source.work.map Event.replay++next.work.map Event.comparison = (source.work.map Event.replay++session.work.map Event.comparison)++[Event.comparison emitted]
      rw [SearchSource.Selection.Session.move_appends moved,List.map_append,List.append_assoc];rfl

theorem Cursor.completed_work {current : Cursor stage catalogue} {made : Execution stage catalogue}
    (actual : current.completed = some made) : made.work = current.work := by
  cases current with
  | scoring session =>
    dsimp only [Cursor.completed] at actual
    split at actual
    · cases actual
    · rename_i source done
      split at actual
      · cases actual
      · rename_i selected chosen
        cases actual
        dsimp only [Execution.work,Cursor.work]
        rw [Mandate.Replay.Program.Session.completed_work done,SearchSource.Selection.Session.completed_work chosen]
        simp only [SearchSource.Selection.Session.initial,List.map_nil,List.append_nil]
  | selecting source session =>
    dsimp only [Cursor.completed] at actual
    split at actual
    · cases actual
    · rename_i selected chosen
      cases actual
      dsimp only [Execution.work,Cursor.work]
      rw [SearchSource.Selection.Session.completed_work chosen]
theorem Cursor.completed_iff_stopped (current : Cursor stage catalogue) : current.completed.isSome = true ↔ current.move = none := by
  cases current with
  | scoring session =>
    cases done : session.completed with
    | none =>
      have native := session.completed_iff_stopped
      cases moved : session.move with
      | none => rw [done] at native;simp only [Option.isSome_none,Bool.false_eq_true,false_iff] at native;exact False.elim (native moved)
      | some emitted => simp only [Cursor.completed,Cursor.move,done,moved,Option.isSome_none,Bool.false_eq_true,Option.some_ne_none]
    | some source =>
      have native := (SearchSource.Selection.Session.initial source.value).completed_iff_stopped
      simp only [Cursor.completed,Cursor.move,done]
      cases chosen : (SearchSource.Selection.Session.initial source.value).completed <;>
        cases moved : (SearchSource.Selection.Session.initial source.value).move <;> simp_all
  | selecting source session =>
    have native := session.completed_iff_stopped
    dsimp only [Cursor.completed,Cursor.move]
    split <;> split <;> simp_all
theorem Cursor.completed_zero {current : Cursor stage catalogue} {made : Execution stage catalogue}
    (actual : current.completed = some made) : current.rank = 0 := by
  cases current with
  | scoring session =>
    dsimp only [Cursor.completed] at actual
    split at actual
    · cases actual
    · rename_i source done
      split at actual
      · cases actual
      · rename_i selected chosen
        cases actual
        have zero := session.stopped_iff_zero.mp (session.completed_iff_stopped.mp (by rw [done];rfl))
        have empty := (SearchSource.Selection.Session.initial source.value).stopped_iff_zero.mp ((SearchSource.Selection.Session.initial source.value).completed_iff_stopped.mp (by rw [chosen];rfl))
        have bound := (SearchSource.Selection.Session.initial source.value).conservation
        change (SearchSource.Selection.Session.initial source.value).rank+0 = catalogue.length at bound
        dsimp only [Cursor.rank];omega
  | selecting source session =>
    dsimp only [Cursor.completed] at actual
    split at actual
    · cases actual
    · rename_i selected chosen
      cases actual
      exact session.stopped_iff_zero.mp (session.completed_iff_stopped.mp (by rw [chosen];rfl))
theorem Cursor.stopped_iff_zero (current : Cursor stage catalogue) : current.move = none ↔ current.rank = 0 := by
  constructor
  · intro stopped
    have complete := current.completed_iff_stopped.mpr stopped
    cases actual : current.completed with
    | none => rw [actual] at complete;cases complete
    | some made => exact Cursor.completed_zero actual
  · intro zero
    cases actual : current.move with
    | none => rfl
    | some emitted => have smaller := Cursor.move_decreases actual;rw [zero] at smaller;omega
theorem initial_rank : (initial stage catalogue).rank = (execute stage catalogue).work.length := by
  change (Mandate.Replay.Program.Session.initial (SearchSource.program stage catalogue)).rank+catalogue.length = _
  rw [Mandate.Replay.Program.Session.initial_rank]
  dsimp only [execute,Execution.work]
  rw [List.length_append,List.length_map,List.length_map,SearchSource.Selection.Execution.work_length]
  rfl
inductive History : Cursor stage catalogue → Cursor stage catalogue → List (Event old) → Prop
  | nil (before) : History before before []
  | step {before middle after event work} (actual : before.move = some (event,middle))
      (later : History middle after work) : History before after (event::work)
theorem History.append : {before middle after : Cursor stage catalogue} → {left right : List (Event old)} →
    History before middle left → History middle after right → History before after (left++right)
  | _,_,_,_,_,.nil _,later => later
  | _,_,_,_,_,.step actual past,later => .step actual (History.append past later)
theorem History.conservation {before after : Cursor stage catalogue} {work : List (Event old)}
    (history : History before after work) : after.rank+work.length = before.rank := by
  induction history with
  | nil => simp
  | step actual _ ih => have := Cursor.move_decreases actual;simp only [List.length_cons];omega
structure Session (stage : SearchSource.Point (old := old) (oldDepth := oldDepth) (word := word)) (catalogue : List (List (Action old))) where
  private mk ::
  current : Cursor stage catalogue
  history : History (initial stage catalogue) current current.work
def Session.initial (stage : SearchSource.Point (old := old) (oldDepth := oldDepth) (word := word)) (catalogue : List (List (Action old))) : Session stage catalogue := ⟨SearchPaid.initial stage catalogue,.nil _⟩
abbrev Session.work (session : Session stage catalogue) := session.current.work
noncomputable def Session.rank (session : Session stage catalogue) := session.current.rank
def Session.completed (session : Session stage catalogue) := session.current.completed
def Session.move (session : Session stage catalogue) : Option (Event old × Session stage catalogue) :=
  match actual : session.current.move with
  | none => none
  | some (event,next) => some (event,⟨next,by rw [Cursor.move_appends actual];exact session.history.append (.step actual (.nil _))⟩)
theorem Session.initial_rank : (Session.initial stage catalogue).rank = (execute stage catalogue).work.length := SearchPaid.initial_rank
theorem Session.move_appends {before after : Session stage catalogue} {event : Event old}
    (actual : before.move = some (event,after)) : after.work = before.work++[event] := by
  dsimp only [Session.move] at actual
  split at actual
  · cases actual
  · rename_i emitted next moved
    cases actual;exact Cursor.move_appends moved
theorem Session.move_decreases {before after : Session stage catalogue} {event : Event old}
    (actual : before.move = some (event,after)) : after.rank+1 = before.rank := by
  dsimp only [Session.move] at actual
  split at actual
  · cases actual
  · rename_i emitted next moved
    cases actual;exact Cursor.move_decreases moved
theorem Session.completed_work {session : Session stage catalogue} {made : Execution stage catalogue}
    (actual : session.completed = some made) : made.work = session.work := Cursor.completed_work actual
theorem Session.completed_iff_stopped (session : Session stage catalogue) : session.completed.isSome = true ↔ session.move = none := by
  have native := session.current.completed_iff_stopped
  unfold Session.completed Session.move
  split <;> simp_all
theorem Session.stopped_iff_zero (session : Session stage catalogue) : session.move = none ↔ session.rank = 0 := by
  have native := session.current.stopped_iff_zero
  unfold Session.move Session.rank
  split <;> simp_all
theorem Session.conservation (session : Session stage catalogue) : session.rank+session.work.length = (execute stage catalogue).work.length := by
  have balance := session.history.conservation
  rw [SearchPaid.initial_rank] at balance
  exact balance
theorem Session.covered (session : Session stage catalogue) : session.work.length ≤ (execute stage catalogue).work.length := by
  have balance := session.conservation;omega
structure Archive (old : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)) (oldDepth : Nat) (word : List (Action old)) where
  stage : Recovery.Cursor old oldDepth word
  catalogue : List (List (Action old))
  execution : Execution stage catalogue
def Archive.endpoint (archive : Archive old oldDepth word) := archive.execution.endpoint
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering.SearchPaid
