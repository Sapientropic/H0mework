import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Replay.Program
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Replay.Program
open Institutions.Capitalism.Universal.Source.Program
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {base : RawLaw P G O T I} {scope : Scope (Party := P) (Good := G) (Port := O)} {R : Type} {depth : Nat}
  {code : Code base scope R depth}
theorem Cursor.completed_iff_stopped (state : Cursor base scope R) : state.completed.isSome = true ↔ state.move = none := by
  cases state with
  | done value => simp [Cursor.completed,Cursor.move]
  | ready code => cases code <;> simp [Cursor.completed,Cursor.move]
  | reading before word child next =>
    apply iff_of_false (by change ¬ false = true;exact Bool.false_ne_true)
    intro stopped
    dsimp only [Cursor.move] at stopped
    split at stopped
    · cases stopped
    · rename_i pending
      split at stopped
      · cases stopped
      · rename_i actual
        have done := child.completed_iff_stopped.mpr actual
        rw [pending] at done;cases done

theorem History.factor {first middle : Cursor base scope R} {pastWork total : List (Event base scope)} {value : R}
    (past : History first middle pastWork) (whole : History first (.done value) total) :
    ∃ tail, History middle (.done value) tail ∧ total = pastWork++tail := by
  induction past generalizing total with
  | nil => exact ⟨total,whole,rfl⟩
  | step moved _ ih =>
    cases whole with
    | nil => cases moved
    | step same later =>
      have equal := Option.some.inj (moved.symm.trans same)
      rcases Prod.mk.inj equal with ⟨rfl,rfl⟩
      obtain ⟨tail,history,split⟩ := ih later
      exact ⟨tail,history,by simp only [List.cons_append,split]⟩
theorem History.empty {first last : Cursor base scope R} (actual : History first last []) : first = last := by
  cases actual;rfl
theorem History.done {left right : R} {work : List (Event base scope)}
    (actual : History (Cursor.done (base := base) (scope := scope) left) (.done right) work) : left = right ∧ work = [] := by
  cases actual with
  | nil => exact ⟨rfl,rfl⟩
  | step moved => cases moved

theorem Execution.unique (left right : Execution code) : left = right := by
  obtain ⟨tail,later,split⟩ := left.history.factor right.history
  obtain ⟨same,empty⟩ := later.done
  rw [empty,List.append_nil] at split
  rcases left with ⟨value,work,history⟩
  rcases right with ⟨other,rest,trace⟩
  dsimp only at same split
  cases same;cases split;rfl
structure Session (code : Code base scope R depth) where
  private mk ::
  current : Cursor base scope R
  work : List (Event base scope)
  history : History (.ready code) current work
def Session.initial (code : Code base scope R depth) : Session code := ⟨.ready code,[],.nil _⟩
def Session.move (session : Session code) : Option (Event base scope × Session code) :=
  match actual : session.current.move with
  | none => none
  | some (event,next) => some (event,⟨next,session.work++[event],session.history.append (.step actual (.nil next))⟩)
def Session.completed (session : Session code) : Option (Execution code) :=
  match done : session.current.completed with
  | none => none
  | some value => some (Execution.fromHistory session.current session.work session.history value done)
noncomputable def Session.rank (session : Session code) : Nat := (execute code).work.length-session.work.length

theorem Session.suffix (session : Session code) : ∃ tail, History session.current (.done (execute code).value) tail ∧
    (execute code).work = session.work++tail := session.history.factor (execute code).history
theorem Session.covered (session : Session code) : session.work.length ≤ (execute code).work.length := by
  obtain ⟨tail,_,split⟩ := session.suffix
  have size := congrArg List.length split
  simp only [List.length_append] at size;omega
theorem Session.move_appends {before after : Session code} {event : Event base scope}
    (actual : before.move = some (event,after)) : after.work = before.work++[event] := by
  dsimp only [Session.move] at actual
  split at actual
  · cases actual
  · cases actual;rfl
theorem Session.move_decreases {before after : Session code} {event : Event base scope}
    (actual : before.move = some (event,after)) : after.rank+1 = before.rank := by
  have size := congrArg List.length (Session.move_appends actual)
  have covered := after.covered
  simp only [List.length_append,List.length_singleton] at size
  dsimp only [Session.rank];omega
theorem Session.completed_work {session : Session code} {made : Execution code}
    (done : session.completed = some made) : made.work = session.work := by
  dsimp only [Session.completed] at done
  split at done
  · cases done
  · cases done;rfl
theorem Session.completed_iff_stopped (session : Session code) : session.completed.isSome = true ↔ session.move = none := by
  have native := session.current.completed_iff_stopped
  unfold Session.completed Session.move
  split <;> split <;> simp_all

theorem Session.stopped_iff_zero (session : Session code) : session.move = none ↔ session.rank = 0 := by
  constructor
  · intro stopped
    have complete := session.completed_iff_stopped.mpr stopped
    cases done : session.completed with
    | none => rw [done] at complete;cases complete
    | some made =>
      have same := made.unique (execute code)
      have work := Session.completed_work done
      rw [same] at work
      dsimp only [Session.rank];rw [←work,Nat.sub_self]
  · intro zero
    obtain ⟨tail,later,split⟩ := session.suffix
    have size := congrArg List.length split
    simp only [List.length_append] at size
    dsimp only [Session.rank] at zero
    have empty : tail = [] := List.length_eq_zero_iff.mp (by omega)
    rw [empty] at later
    have same := History.empty later
    have stopped : session.current.move = none := by rw [same];rfl
    unfold Session.move
    split
    · rfl
    · rename_i event next actual
      rw [stopped] at actual;cases actual

theorem Session.initial_rank : (Session.initial code).rank = (execute code).work.length := by simp [Session.initial,Session.rank]
theorem Session.conservation (session : Session code) : session.rank+session.work.length = (execute code).work.length := by
  have covered := session.covered
  dsimp only [Session.rank];omega
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Replay.Program
