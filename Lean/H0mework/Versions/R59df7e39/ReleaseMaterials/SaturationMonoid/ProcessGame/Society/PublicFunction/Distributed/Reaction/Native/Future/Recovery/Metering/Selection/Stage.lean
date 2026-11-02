import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering.Selection.Native
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering.StageProgram
open Institutions.Capitalism.Universal.Source.Program
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {old : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {oldDepth : Nat} {word : List (Action old)} {R : Type}
structure Tail (R : Type) where
  stage : Recovery.Cursor old oldDepth word
  catalogue : List (List (Action old))
  finish : SearchPaid.Execution stage catalogue → R
inductive Choice (R : Type) where
  | finished (value : R)
  | search (tail : Tail (old := old) (oldDepth := oldDepth) (word := word) R)
abbrev Code (R : Type) := NativeProgram.Code (old := old) (Choice (old := old) (oldDepth := oldDepth) (word := word) R) 3
abbrev Event := NativeProgram.Event old
variable {code : Code (old := old) (oldDepth := oldDepth) (word := word) R}
inductive Execution (code : Code (old := old) (oldDepth := oldDepth) (word := word) R) where
  | private finished (first : NativeProgram.Execution code) (value : R) (same : first.value = .finished value)
  | private searched (first : NativeProgram.Execution code) (tail : Tail R) (same : first.value = .search tail)
      (later : SearchPaid.Execution tail.stage tail.catalogue)
def execute (code : Code (old := old) (oldDepth := oldDepth) (word := word) R) : Execution code :=
  let first := NativeProgram.execute code
  match same : first.value with
  | .finished value => .finished first value same
  | .search tail => .searched first tail same (SearchPaid.execute tail.stage tail.catalogue)
def Execution.value : Execution code → R
  | .finished _ value _ => value
  | .searched _ tail _ later => tail.finish later
def Execution.work : Execution code → List (Event (old := old))
  | .finished first _ _ => first.work
  | .searched first _ _ later => first.work++later.work.map NativeProgram.Event.search
theorem Execution.unique (first second : Execution code) : first = second := by
  rcases first with ⟨a,x,hx⟩ | ⟨a,tail,hx,later⟩
  · rcases second with ⟨b,y,hy⟩ | ⟨b,other,hy,result⟩
    · cases a.unique b
      have same := hx.symm.trans hy
      cases Choice.finished.inj same;rfl
    · cases a.unique b
      have same := hx.symm.trans hy;cases same
  · rcases second with ⟨b,y,hy⟩ | ⟨b,other,hy,result⟩
    · cases a.unique b
      have same := hx.symm.trans hy;cases same
    · cases a.unique b
      have same := Choice.search.inj (hx.symm.trans hy)
      cases same
      cases later.unique result;rfl

inductive Cursor (code : Code (old := old) (oldDepth := oldDepth) (word := word) R) where
  | invoice (session : NativeProgram.Session code)
  | searching (first : NativeProgram.Execution code) (tail : Tail R) (same : first.value = .search tail)
      (session : SearchPaid.Session tail.stage tail.catalogue)
def initial (code : Code (old := old) (oldDepth := oldDepth) (word := word) R) : Cursor code :=
  .invoice (NativeProgram.Session.initial code)
def Cursor.work : Cursor code → List (Event (old := old))
  | .invoice session => session.work
  | .searching first _ _ session => first.work++session.work.map NativeProgram.Event.search
def Cursor.completed : Cursor code → Option (Execution code)
  | .invoice session => match _done : session.completed with
    | none => none
    | some first => match same : first.value with
      | .finished value => some (.finished first value same)
      | .search _ => none
  | .searching first tail same session => match session.completed with
    | none => none
    | some later => some (.searched first tail same later)
private theorem search_initial_moving (stage : Recovery.Cursor old oldDepth word) (catalogue : List (List (Action old))) :
    (SearchPaid.Session.initial stage catalogue).move ≠ none := by
  intro stopped
  have done := (SearchPaid.Session.initial stage catalogue).completed_iff_stopped.mpr stopped
  change false = true at done;cases done
def Cursor.move : Cursor code → Option (Event (old := old) × Cursor code)
  | .invoice session => match done : session.completed with
    | none => match actual : session.move with
      | some (event,next) => some (event,.invoice next)
      | none => False.elim (by have complete := session.completed_iff_stopped.mpr actual;rw [done] at complete;cases complete)
    | some first => match same : first.value with
      | .finished _ => none
      | .search tail => match actual : (SearchPaid.Session.initial tail.stage tail.catalogue).move with
        | some (event,next) => some (NativeProgram.Event.search event,.searching first tail same next)
        | none => False.elim (search_initial_moving _ _ actual)
  | .searching first tail same session => match session.move with
    | none => none
    | some (event,next) => some (NativeProgram.Event.search event,.searching first tail same next)
noncomputable def tailWork : Choice (old := old) (oldDepth := oldDepth) (word := word) R → Nat
  | .finished _ => 0
  | .search tail => (SearchPaid.execute tail.stage tail.catalogue).work.length
noncomputable def Cursor.rank : Cursor code → Nat
  | .invoice session => session.rank+tailWork (NativeProgram.execute code).value
  | .searching _ _ _ session => session.rank
theorem Cursor.move_decreases {before after : Cursor code} {event : Event (old := old)}
    (actual : before.move = some (event,after)) : after.rank+1 = before.rank := by
  cases before with
  | invoice session =>
    dsimp only [Cursor.move] at actual
    split at actual
    · rename_i pending
      split at actual
      · rename_i emitted next moved
        cases actual
        have smaller := NativeProgram.Session.move_decreases moved
        dsimp only [Cursor.rank];omega
      · rename_i stopped
        have complete := session.completed_iff_stopped.mpr stopped;rw [pending] at complete;cases complete
    · rename_i first done
      split at actual
      · cases actual
      · rename_i tail same
        split at actual
        · rename_i emitted next moved
          cases actual
          have zero := session.stopped_iff_zero.mp (session.completed_iff_stopped.mp (by rw [done];rfl))
          have recognized : (NativeProgram.execute code).value = .search tail := by
            rw [←first.unique (NativeProgram.execute code)];exact same
          have smaller := SearchPaid.Session.move_decreases moved
          rw [SearchPaid.Session.initial_rank] at smaller
          dsimp only [Cursor.rank]
          rw [zero,recognized]
          simpa only [tailWork,Nat.zero_add,SearchPaid.execute] using smaller
        · rename_i stopped
          exact False.elim (search_initial_moving _ _ stopped)
  | searching first tail same session =>
    dsimp only [Cursor.move] at actual
    split at actual
    · cases actual
    · rename_i emitted next moved
      cases actual
      exact SearchPaid.Session.move_decreases moved
theorem Cursor.move_appends {before after : Cursor code} {event : Event (old := old)}
    (actual : before.move = some (event,after)) : after.work = before.work++[event] := by
  cases before with
  | invoice session =>
    dsimp only [Cursor.move] at actual
    split at actual
    · rename_i pending
      split at actual
      · rename_i emitted next moved
        cases actual
        exact NativeProgram.Session.move_appends moved
      · rename_i stopped
        have complete := session.completed_iff_stopped.mpr stopped;rw [pending] at complete;cases complete
    · rename_i first done
      split at actual
      · cases actual
      · rename_i tail same
        split at actual
        · rename_i emitted next moved
          cases actual
          have original := NativeProgram.Session.completed_work done
          have appended := SearchPaid.Session.move_appends moved
          change first.work++next.work.map NativeProgram.Event.search = session.work++[NativeProgram.Event.search emitted]
          rw [original,appended,List.map_append];rfl
        · rename_i stopped
          exact False.elim (search_initial_moving _ _ stopped)
  | searching first tail same session =>
    dsimp only [Cursor.move] at actual
    split at actual
    · cases actual
    · rename_i emitted next moved
      cases actual
      change first.work++next.work.map NativeProgram.Event.search = (first.work++session.work.map NativeProgram.Event.search)++[NativeProgram.Event.search emitted]
      rw [SearchPaid.Session.move_appends moved,List.map_append,List.append_assoc];rfl
theorem Cursor.completed_work {current : Cursor code} {made : Execution code}
    (actual : current.completed = some made) : made.work = current.work := by
  cases current with
  | invoice session =>
    dsimp only [Cursor.completed] at actual
    split at actual
    · cases actual
    · rename_i first done
      split at actual
      · cases actual
        exact NativeProgram.Session.completed_work done
      · cases actual
  | searching first tail same session =>
    dsimp only [Cursor.completed] at actual
    split at actual
    · cases actual
    · rename_i later done
      cases actual
      change first.work++later.work.map NativeProgram.Event.search = first.work++session.work.map NativeProgram.Event.search
      rw [SearchPaid.Session.completed_work done]
theorem Cursor.completed_iff_stopped (current : Cursor code) : current.completed.isSome = true ↔ current.move = none := by
  cases current with
  | invoice session =>
    dsimp only [Cursor.completed,Cursor.move]
    split
    · rename_i pending
      split
      · simp
      · rename_i stopped
        have complete := session.completed_iff_stopped.mpr stopped;rw [pending] at complete;cases complete
    · rename_i first done
      split
      · simp
      · rename_i tail same
        split
        · simp
        · rename_i stopped
          exact False.elim (search_initial_moving _ _ stopped)
  | searching first tail same session =>
    have native := session.completed_iff_stopped
    dsimp only [Cursor.completed,Cursor.move]
    split <;> split <;> simp_all
theorem Cursor.completed_zero {current : Cursor code} {made : Execution code}
    (actual : current.completed = some made) : current.rank = 0 := by
  cases current with
  | invoice session =>
    dsimp only [Cursor.completed] at actual
    split at actual
    · cases actual
    · rename_i first done
      split at actual
      · rename_i value same
        cases actual
        have zero := session.stopped_iff_zero.mp (session.completed_iff_stopped.mp (by rw [done];rfl))
        have recognized : (NativeProgram.execute code).value = .finished value := by
          rw [←first.unique (NativeProgram.execute code)];exact same
        dsimp only [Cursor.rank];rw [zero,recognized];rfl
      · cases actual
  | searching first tail same session =>
    dsimp only [Cursor.completed] at actual
    split at actual
    · cases actual
    · rename_i later done
      cases actual
      exact session.stopped_iff_zero.mp (session.completed_iff_stopped.mp (by rw [done];rfl))
theorem Cursor.stopped_iff_zero (current : Cursor code) : current.move = none ↔ current.rank = 0 := by
  constructor
  · intro stopped
    have complete := current.completed_iff_stopped.mpr stopped
    cases actual : current.completed with
    | none => rw [actual] at complete;cases complete
    | some made => exact Cursor.completed_zero actual
  · intro zero
    cases actual : current.move with
    | none => rfl
    | some emitted =>
      have smaller := Cursor.move_decreases actual
      rw [zero] at smaller;omega
theorem initial_rank : (initial code).rank = (execute code).work.length := by
  change (NativeProgram.Session.initial code).rank+tailWork (NativeProgram.execute code).value = _
  rw [NativeProgram.Session.initial_rank]
  dsimp only [execute]
  split
  · rename_i value recognized
    simp only [Execution.work,recognized,tailWork,Nat.add_zero]
  · rename_i tail recognized
    simp only [Execution.work,List.length_append,List.length_map,recognized,tailWork,SearchPaid.execute]

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
structure Session (code : Code (old := old) (oldDepth := oldDepth) (word := word) R) where
  private mk ::
  current : Cursor code
  history : History (initial code) current current.work
def Session.initial (code : Code (old := old) (oldDepth := oldDepth) (word := word) R) : Session code := ⟨StageProgram.initial code,.nil _⟩
abbrev Session.work (session : Session code) := session.current.work
noncomputable def Session.rank (session : Session code) := session.current.rank
def Session.completed (session : Session code) := session.current.completed
def Session.move (session : Session code) : Option (Event (old := old) × Session code) :=
  match actual : session.current.move with
  | none => none
  | some (event,next) => some (event,⟨next,by
      rw [Cursor.move_appends actual]
      exact session.history.append (.step actual (.nil _))⟩)
theorem Session.initial_rank : (Session.initial code).rank = (execute code).work.length := StageProgram.initial_rank
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
  rw [StageProgram.initial_rank] at balance
  exact balance
theorem Session.covered (session : Session code) : session.work.length ≤ (execute code).work.length := by
  have balance := session.conservation;omega
def Execution.invoice : Execution code → NativeProgram.Execution code
  | .finished first _ _ | .searched first _ _ _ => first
def Execution.search : Execution code → Option (SearchPaid.Archive old oldDepth word)
  | .finished .. => none
  | .searched _ tail _ later => some ⟨tail.stage,tail.catalogue,later⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering.StageProgram
