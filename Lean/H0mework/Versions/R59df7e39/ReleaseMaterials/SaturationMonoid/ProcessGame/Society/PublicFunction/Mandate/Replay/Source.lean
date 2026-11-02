import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Replay
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Replay.Source
open Institutions.Capitalism.Universal.Source.Program
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
abbrev Point := RawCurrent P G (State P T) I
abbrev Action := Request P G O (State P T) I
variable (base : RawLaw P G O T I) (scope : Scope (Party := P) (Good := G) (Port := O))
inductive Spine (origin : Point (P := P) (G := G) (T := T) (I := I)) (original : List (Action (P := P) (G := G) (O := O) (T := T) (I := I))) :
    Point (P := P) (G := G) (T := T) (I := I) → List (Action (P := P) (G := G) (O := O) (T := T) (I := I)) → Type where
  | nil : Spine origin original origin original
  | accepted {before head tail} (earlier : Spine origin original before (head::tail))
      (emitted : Action (P := P) (G := G) (O := O) (T := T) (I := I))
      (rebased : emitted = rebase scope before head) (valid : (Mandate.law base scope).Valid before emitted) :
      Spine origin original ((Mandate.law base scope).step before emitted) tail
variable {base scope}
def Spine.length {origin original before remaining} : Spine base scope origin original before remaining → Nat
  | .nil => 0
  | .accepted earlier _ _ _ => earlier.length+1
variable (base scope) (origin : Point (P := P) (G := G) (T := T) (I := I)) (original : List (Action (P := P) (G := G) (O := O) (T := T) (I := I)))
inductive Focus where
  | reading (before : Point (P := P) (G := G) (T := T) (I := I)) (remaining : List (Action (P := P) (G := G) (O := O) (T := T) (I := I)))
      (spine : Spine base scope origin original before remaining)
  | building (before : Point (P := P) (G := G) (T := T) (I := I)) (remaining : List (Action (P := P) (G := G) (O := O) (T := T) (I := I)))
      (spine : Spine base scope origin original before remaining) (made : Materialized base scope before remaining)
  | done (made : Materialized base scope origin original)
inductive Event where
  | accepted (before : Point (P := P) (G := G) (T := T) (I := I)) (head : Action (P := P) (G := G) (O := O) (T := T) (I := I)) (tail : List (Action (P := P) (G := G) (O := O) (T := T) (I := I)))
      (emitted : Action (P := P) (G := G) (O := O) (T := T) (I := I))
      (rebased : emitted = rebase scope before head) (valid : (Mandate.law base scope).Valid before emitted)
  | refused (before : Point (P := P) (G := G) (T := T) (I := I)) (head : Action (P := P) (G := G) (O := O) (T := T) (I := I)) (tail : List (Action (P := P) (G := G) (O := O) (T := T) (I := I)))
      (emitted : Action (P := P) (G := G) (O := O) (T := T) (I := I))
      (rebased : emitted = rebase scope before head) (failure : ¬ (Mandate.law base scope).Valid before emitted)
  | empty (before : Point (P := P) (G := G) (T := T) (I := I))
  | unwind (before : Point (P := P) (G := G) (T := T) (I := I)) (head emitted : Action (P := P) (G := G) (O := O) (T := T) (I := I))
  | finish
variable {base scope origin original}
def Event.released : Event base scope → Nat
  | .refused _ _ tail _ _ _ => 2*(tail.length+1)
  | _ => 0
def Focus.rank : Focus base scope origin original → Nat
  | .reading _ remaining spine => 2*remaining.length+spine.length+2
  | .building _ _ spine _ => spine.length+1
  | .done _ => 0
def Focus.move (state : Focus base scope origin original) : Option (Event base scope × Focus base scope origin original) := by
  cases state with
  | reading before remaining spine =>
    cases remaining with
    | nil => exact some (.empty before,.building before [] spine (Materialized.empty base scope before))
    | cons head tail =>
      let emitted := rebase scope before head
      exact if valid : (Mandate.law base scope).Valid before emitted then
        some (.accepted before head tail emitted rfl valid,
          .reading ((Mandate.law base scope).step before emitted) tail (.accepted spine emitted rfl valid))
      else some (.refused before head tail emitted rfl valid,
          .building before (head::tail) spine (Materialized.refused base scope before head tail emitted rfl valid))
  | building before remaining spine made =>
    cases spine with
    | nil => exact some (.finish,.done made)
    | @accepted before head tail earlier emitted rebased valid =>
      exact some (.unwind before head emitted,.building before (head::_) earlier
        (Materialized.accepted base scope before head _ emitted rebased valid made))
  | done _ => exact none

theorem Focus.move_conserves {before after : Focus base scope origin original} {event : Event base scope}
    (actual : before.move = some (event,after)) : after.rank+1+event.released = before.rank := by
  cases before with
  | reading point remaining spine =>
    cases remaining with
    | nil => cases actual;simp only [Focus.rank,Event.released,List.length_nil];omega
    | cons head tail =>
      dsimp only [Focus.move] at actual
      split at actual <;> cases actual <;> simp only [Focus.rank,Spine.length,Event.released,List.length_cons] <;> omega
  | building point remaining spine made =>
    cases spine <;> cases actual <;> simp only [Focus.rank,Spine.length,Event.released]
  | done _ => cases actual
structure Cursor (base : RawLaw P G O T I) (scope : Scope (Party := P) (Good := G) (Port := O))
    (origin : Point (P := P) (G := G) (T := T) (I := I)) (original : List (Action (P := P) (G := G) (O := O) (T := T) (I := I))) where
  private mk ::
  current : Focus base scope origin original
variable (base scope origin original)
def initial : Cursor base scope origin original := ⟨.reading origin original .nil⟩
def capacity : Nat := 2*original.length+2
variable {base scope origin original}
def Cursor.rank (state : Cursor base scope origin original) := state.current.rank
def Cursor.move (state : Cursor base scope origin original) : Option (Event base scope × Cursor base scope origin original) :=
  state.current.move.map fun (event,next) => (event,⟨next⟩)
def Cursor.completed (state : Cursor base scope origin original) : Option (Materialized base scope origin original) :=
  match state.current with
  | .done made => some made
  | _ => none
theorem initial_rank : (initial base scope origin original).rank = capacity (P := P) (G := G) (O := O) (T := T) (I := I) original := rfl
theorem Cursor.move_conserves {before after : Cursor base scope origin original} {event : Event base scope}
    (actual : before.move = some (event,after)) : after.rank+1+event.released = before.rank := by
  dsimp only [Cursor.move] at actual
  cases moved : before.current.move with
  | none => simp only [moved,Option.map_none,reduceCtorEq] at actual
  | some pair => rcases pair with ⟨native,next⟩;rw [moved] at actual;cases actual;exact Focus.move_conserves moved
theorem Cursor.completed_iff_stopped (state : Cursor base scope origin original) : state.completed.isSome = true ↔ state.move = none := by
  rcases state with ⟨focus⟩
  cases focus with
  | done _ => simp [Cursor.completed,Cursor.move,Focus.move]
  | reading point remaining spine => cases remaining <;> simp [Cursor.completed,Cursor.move,Focus.move];split <;> simp
  | building point remaining spine made => cases spine <;> simp [Cursor.completed,Cursor.move,Focus.move]
theorem Cursor.stopped_iff_zero (state : Cursor base scope origin original) : state.move = none ↔ state.rank = 0 := by
  rcases state with ⟨focus⟩
  cases focus with
  | done _ => simp [Cursor.move,Focus.move,Cursor.rank,Focus.rank]
  | reading point remaining spine =>
    have active : (⟨.reading point remaining spine⟩ : Cursor base scope origin original).move ≠ none := by
      intro stopped;have complete := (Cursor.completed_iff_stopped _).mpr stopped;cases complete
    exact iff_of_false active (by change 2*remaining.length+spine.length+2 ≠ 0;omega)
  | building point remaining spine made =>
    have active : (⟨.building point remaining spine made⟩ : Cursor base scope origin original).move ≠ none := by
      intro stopped;have complete := (Cursor.completed_iff_stopped _).mpr stopped;cases complete
    exact iff_of_false active (by change spine.length+1 ≠ 0;omega)
inductive History : Cursor base scope origin original → Cursor base scope origin original → List (Event base scope) → Prop
  | nil (before) : History before before []
  | step {before middle after event work} (actual : before.move = some (event,middle))
      (later : History middle after work) : History before after (event::work)
def released (work : List (Event base scope)) : Nat := (work.map Event.released).sum
structure Run (before : Cursor base scope origin original) (capacity : Nat) where
  private mk ::
  endpoint : Cursor base scope origin original
  work : List (Event base scope)
  history : History before endpoint work
  covered : work.length ≤ capacity
  exhausted : endpoint.move = none ∨ work.length = capacity
  conservation : endpoint.rank+work.length+released work = before.rank

def run : (capacity : Nat) → (before : Cursor base scope origin original) → Run before capacity
  | 0,before => ⟨before,[],.nil before,Nat.le_refl _,Or.inr rfl,by simp [released]⟩
  | capacity+1,before => match actual : before.move with
    | none => ⟨before,[],.nil before,by simp,Or.inl actual,by simp [released]⟩
    | some (event,next) =>
        let later := run capacity next
        ⟨later.endpoint,event::later.work,.step actual later.history,by have := later.covered;simp only [List.length_cons];omega,
          later.exhausted.imp_right (fun same => by simp only [List.length_cons,same]),by
            have := later.conservation;have := Cursor.move_conserves actual
            simp only [List.length_cons,released,List.map_cons,List.sum_cons] at *;omega⟩
theorem run_sufficient (before : Cursor base scope origin original) (capacity : Nat) (enough : before.rank ≤ capacity) :
    (run capacity before).endpoint.completed.isSome = true := by
  apply (Cursor.completed_iff_stopped _).mpr
  rcases (run capacity before).exhausted with stopped | full
  · exact stopped
  apply (Cursor.stopped_iff_zero _).mpr
  have := (run capacity before).conservation;omega
structure Execution (base : RawLaw P G O T I) (scope : Scope (Party := P) (Good := G) (Port := O))
    (origin : Point (P := P) (G := G) (T := T) (I := I)) (original : List (Action (P := P) (G := G) (O := O) (T := T) (I := I))) where
  private mk ::
  run : Run (initial base scope origin original) (capacity original)
  cache : Materialized base scope origin original
  completed : run.endpoint.completed = some cache
variable (base scope origin original)
def execute : Execution base scope origin original :=
  let walked := run (capacity original) (initial base scope origin original)
  match actual : walked.endpoint.completed with
  | some cache => ⟨walked,cache,actual⟩
  | none => False.elim (by
      have complete := run_sufficient (initial base scope origin original) (capacity original) (Nat.le_refl _)
      rw [actual] at complete;cases complete)
variable {base scope origin original}
theorem Execution.path_exact (made : Execution base scope origin original) : made.cache.path = compile base scope origin original := made.cache.path_exact
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Replay.Source
