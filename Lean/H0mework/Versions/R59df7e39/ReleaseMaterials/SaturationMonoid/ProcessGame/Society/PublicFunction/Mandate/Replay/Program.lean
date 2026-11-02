import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Replay.Source
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Replay.Program
open Institutions.Capitalism.Universal.Source.Program
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
abbrev Point := Source.Point (P := P) (G := G) (T := T) (I := I)
abbrev Action := Source.Action (P := P) (G := G) (O := O) (T := T) (I := I)
variable (base : RawLaw P G O T I) (scope : Scope (Party := P) (Good := G) (Port := O))
inductive Code (Result : Type) : Nat → Type where
  | done {depth} (value : Result) : Code Result depth
  | replay {depth} (before : Point (P := P) (G := G) (T := T) (I := I))
      (word : List (Action (P := P) (G := G) (O := O) (T := T) (I := I)))
      (next : Materialized base scope before word → Code Result depth) : Code Result (depth+1)
inductive Event where
  | begin (before : Point (P := P) (G := G) (T := T) (I := I))
      (word : List (Action (P := P) (G := G) (O := O) (T := T) (I := I)))
  | request (before : Point (P := P) (G := G) (T := T) (I := I))
      (word : List (Action (P := P) (G := G) (O := O) (T := T) (I := I))) (native : Source.Event base scope)
  | collect (before : Point (P := P) (G := G) (T := T) (I := I))
      (word : List (Action (P := P) (G := G) (O := O) (T := T) (I := I))) (cache : Materialized base scope before word)
  | finish
inductive Cursor (Result : Type) where
  | ready {depth} (code : Code base scope Result depth)
  | reading {depth} (before : Point (P := P) (G := G) (T := T) (I := I))
      (word : List (Action (P := P) (G := G) (O := O) (T := T) (I := I)))
      (child : Source.Cursor base scope before word)
      (next : Materialized base scope before word → Code base scope Result depth)
  | done (value : Result)
variable {base scope} {Result : Type}
def Cursor.completed : Cursor base scope Result → Option Result
  | .done value => some value
  | _ => none
private theorem pending_of_move {before : Point (P := P) (G := G) (T := T) (I := I)}
    {word : List (Action (P := P) (G := G) (O := O) (T := T) (I := I))}
    {child after : Source.Cursor base scope before word} {event : Source.Event base scope}
    (actual : child.move = some (event,after)) : child.completed = none := by
  cases complete : child.completed with
  | none => rfl
  | some cache =>
    have stopped := (child.completed_iff_stopped).mp (by rw [complete];rfl)
    rw [actual] at stopped;cases stopped

def Cursor.move : Cursor base scope Result → Option (Event base scope × Cursor base scope Result)
  | .done _ => none
  | .ready (.done value) => some (.finish,.done value)
  | .ready (.replay before word next) => some (.begin before word,.reading before word (Source.initial base scope before word) next)
  | .reading before word child next => match complete : child.completed with
    | some cache => some (.collect before word cache,.ready (next cache))
    | none => match actual : child.move with
      | some (event,after) => some (.request before word event,.reading before word after next)
      | none => False.elim (by
          have done := (child.completed_iff_stopped).mpr actual
          rw [complete] at done;cases done)
inductive History : Cursor base scope Result → Cursor base scope Result → List (Event base scope) → Prop
  | nil (before) : History before before []
  | step {before middle after event work} (actual : before.move = some (event,middle))
      (later : History middle after work) : History before after (event::work)
theorem History.append {first middle last : Cursor base scope Result} {left right : List (Event base scope)}
    (earlier : History first middle left) (later : History middle last right) : History first last (left++right) := by
  induction earlier with
  | nil => exact later
  | step actual _ ih => exact .step actual (ih later)
theorem History.child {depth : Nat} {before : Point (P := P) (G := G) (T := T) (I := I)}
    {word : List (Action (P := P) (G := G) (O := O) (T := T) (I := I))}
    {first last : Source.Cursor base scope before word} {work : List (Source.Event base scope)}
    (next : Materialized base scope before word → Code base scope Result depth)
    (history : Source.History first last work) : History (.reading before word first next) (.reading before word last next)
      (work.map (Event.request before word)) := by
  induction history with
  | nil => exact .nil _
  | step actual _ ih =>
    apply History.step (event := .request before word _) (middle := .reading before word _ next)
    · dsimp only [Cursor.move]
      split
      · rename_i cache complete
        rw [pending_of_move actual] at complete;cases complete
      · split
        · rename_i native middle moved
          have same := Option.some.inj (moved.symm.trans actual)
          rcases Prod.mk.inj same with ⟨rfl,rfl⟩
          rfl
        · rename_i stopped
          rw [actual] at stopped;cases stopped
    · exact ih
structure Run (before : Cursor base scope Result) (available : Nat) where
  private mk ::
  endpoint : Cursor base scope Result
  work : List (Event base scope)
  history : History before endpoint work
  covered : work.length ≤ available
  exhausted : endpoint.move = none ∨ work.length = available
def run : (available : Nat) → (before : Cursor base scope Result) → Run before available
  | 0,before => ⟨before,[],.nil before,Nat.le_refl _,Or.inr rfl⟩
  | available+1,before => match actual : before.move with
    | none => ⟨before,[],.nil before,by simp,Or.inl actual⟩
    | some (event,after) =>
      let later := run available after
      ⟨later.endpoint,event::later.work,.step actual later.history,by have := later.covered;simp only [List.length_cons];omega,
        later.exhausted.imp_right (fun same => by simp only [List.length_cons,same])⟩
theorem History.run_exact {first last : Cursor base scope Result} {work : List (Event base scope)}
    (history : History first last work) : (run work.length first).endpoint = last := by
  induction history with
  | nil => rfl
  | step actual _ ih =>
    simp only [List.length_cons]
    unfold run
    split
    · rename_i stopped
      rw [actual] at stopped;cases stopped
    · rename_i native after moved
      have same := Option.some.inj (moved.symm.trans actual)
      rcases Prod.mk.inj same with ⟨rfl,rfl⟩
      exact ih
structure Execution {depth : Nat} (code : Code base scope Result depth) where
  private mk ::
  value : Result
  work : List (Event base scope)
  history : History (.ready code) (.done value) work

def execute : {depth : Nat} → (code : Code base scope Result depth) → Execution code
  | _,.done value => ⟨value,[.finish],.step rfl (.nil _)⟩
  | _,.replay before word next =>
    let child := Source.execute base scope before word
    let later := execute (next child.cache)
    ⟨later.value,.begin before word::(child.run.work.map (Event.request before word)++(.collect before word child.cache::later.work)),
      .step rfl ((History.child next child.run.history).append (.step (by
        dsimp only [Cursor.move]
        split
        · rename_i cache complete
          have same := Option.some.inj (complete.symm.trans child.completed)
          cases same;rfl
        · rename_i pending
          rw [child.completed] at pending;cases pending) later.history))⟩
termination_by depth _ => depth

theorem Execution.replayed {depth : Nat} {code : Code base scope Result depth} (made : Execution code) :
    (run made.work.length (.ready code)).endpoint.completed = some made.value := by
  rw [made.history.run_exact];rfl
variable {depth : Nat} {code : Code base scope Result depth}
def Execution.fromHistory (endpoint : Cursor base scope Result) (work : List (Event base scope))
    (history : History (.ready code) endpoint work) (value : Result) (done : endpoint.completed = some value) : Execution code :=
  ⟨value,work,by cases endpoint <;> cases done;exact history⟩
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Replay.Program
