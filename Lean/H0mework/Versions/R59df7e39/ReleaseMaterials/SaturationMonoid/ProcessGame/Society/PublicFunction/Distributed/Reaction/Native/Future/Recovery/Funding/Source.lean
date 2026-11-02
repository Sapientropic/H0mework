import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Funding
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Source.Stepper
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Funding.Source
open Institutions.Capitalism.Universal.Source.Program
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {old : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {oldDepth : Nat} {word : List (Action old)}
abbrev Point := Recovery.Cursor old oldDepth word
inductive Focus where
  | walking (point : Point (old := old) (oldDepth := oldDepth) (word := word)) (walk : Walk point)
  | done (value : Option (Failure old oldDepth word))
-- Inspecting a saved node does not perform its original recovery action again.
inductive Event where
  | inspect (node : Stepper.Event (old := old) (oldDepth := oldDepth) (word := word))
def Focus.value : Focus (old := old) (oldDepth := oldDepth) (word := word) → Option (Failure old oldDepth word)
  | .walking _ walk => ofWalk walk
  | .done value => value
noncomputable def Focus.rank : Focus (old := old) (oldDepth := oldDepth) (word := word) → Nat
  | .walking _ walk => Stepper.steps walk
  | .done _ => 0
def Focus.move : Focus (old := old) (oldDepth := oldDepth) (word := word) →
    Option (Event (old := old) (oldDepth := oldDepth) (word := word) × Focus (old := old) (oldDepth := oldDepth) (word := word))
  | .done _ => none
  | .walking _ walk =>
    let next := match walk with
      | .finished .. | .blocked .. => Focus.done none
      | .unsupported point fee outside => .done (some (.unsupported point fee outside))
      | .unpaid point fee supported refused => .done (some (.unpaid point fee supported refused))
      | .billed _ _ _ _ later | .advanced _ _ _ _ _ later => .walking _ later
      | .workloadAdvanced _ _ _ _ later | .quotedAdvanced _ _ _ _ later => .walking _ later
      | .workloadStopped point position made _ =>
          .done (if failed : made.result.FundingFailed then some (.workload point position made failed) else none)
      | .quotedStopped point fees made _ =>
          .done (if failed : made.result.FundingFailed then some (.quoted point fees made failed) else none)
    some (.inspect (Stepper.headEvent walk),next)
theorem Focus.move_preserves {before after : Focus (old := old) (oldDepth := oldDepth) (word := word)}
    {event : Event (old := old) (oldDepth := oldDepth) (word := word)} (actual : before.move = some (event,after)) :
    after.value = before.value := by
  cases before with
  | done value => cases actual
  | walking point walk => cases walk <;> cases actual <;> rfl
theorem Focus.move_decreases {before after : Focus (old := old) (oldDepth := oldDepth) (word := word)}
    {event : Event (old := old) (oldDepth := oldDepth) (word := word)} (actual : before.move = some (event,after)) :
    after.rank+1 = before.rank := by
  cases before with
  | done value => cases actual
  | walking point walk => cases walk <;> cases actual <;> rfl
structure Cursor {point : Point (old := old) (oldDepth := oldDepth) (word := word)} (original : Walk point) where
  private mk ::
  current : Focus (old := old) (oldDepth := oldDepth) (word := word)
  coherent : current.value = ofWalk original
variable {point : Point (old := old) (oldDepth := oldDepth) (word := word)} (original : Walk point)
def initial : Cursor original := ⟨.walking point original,rfl⟩
variable {original}
noncomputable def Cursor.rank (state : Cursor original) := state.current.rank
def Cursor.move (state : Cursor original) : Option (Event (old := old) (oldDepth := oldDepth) (word := word) × Cursor original) :=
  match actual : state.current.move with
  | none => none
  | some (event,next) => some (event,⟨next,(Focus.move_preserves actual).trans state.coherent⟩)
structure Completed (original : Walk point) where
  private mk ::
  value : Option (Failure old oldDepth word)
  exact_value : value = ofWalk original
def Cursor.completed (state : Cursor original) : Option (Completed original) :=
  match actual : state.current with
  | .walking _ _ => none
  | .done value => some ⟨value,by have known := state.coherent;rw [actual] at known;exact known⟩
theorem initial_rank : (initial original).rank = Stepper.steps original := rfl
theorem Cursor.move_decreases {before after : Cursor original} {event : Event (old := old) (oldDepth := oldDepth) (word := word)}
    (actual : before.move = some (event,after)) : after.rank+1 = before.rank := by
  dsimp only [Cursor.move] at actual
  split at actual
  · cases actual
  · rename_i event next moved
    cases actual
    exact Focus.move_decreases moved
theorem Cursor.completed_iff_stopped (state : Cursor original) : state.completed.isSome = true ↔ state.move = none := by
  rcases state with ⟨focus,coherent⟩
  cases focus with
  | done value => simp [Cursor.completed,Cursor.move,Focus.move]
  | walking currentPoint walk => cases walk <;> simp [Cursor.completed,Cursor.move,Focus.move]
theorem Cursor.stopped_iff_zero (state : Cursor original) : state.move = none ↔ state.rank = 0 := by
  rcases state with ⟨focus,coherent⟩
  cases focus with
  | done value => simp [Cursor.move,Focus.move,Cursor.rank,Focus.rank]
  | walking currentPoint walk =>
    have notStopped : (⟨.walking currentPoint walk,coherent⟩ : Cursor original).move ≠ none := by
      intro stopped
      have complete := (Cursor.completed_iff_stopped _).mpr stopped
      cases complete
    have notZero : (⟨.walking currentPoint walk,coherent⟩ : Cursor original).rank ≠ 0 :=
      Nat.ne_of_gt (Stepper.steps_positive walk)
    exact iff_of_false notStopped notZero

inductive History : Cursor original → Cursor original → List (Event (old := old) (oldDepth := oldDepth) (word := word)) → Prop
  | nil (before) : History before before []
  | step {before middle after event work} (actual : before.move = some (event,middle))
      (later : History middle after work) : History before after (event::work)
structure Run (before : Cursor original) (capacity : Nat) where
  private mk ::
  endpoint : Cursor original
  work : List (Event (old := old) (oldDepth := oldDepth) (word := word))
  history : History before endpoint work
  covered : work.length ≤ capacity
  exhausted : endpoint.move = none ∨ work.length = capacity
  conservation : endpoint.rank+work.length = before.rank

def run : (capacity : Nat) → (before : Cursor original) → Run before capacity
  | 0,before => ⟨before,[],.nil before,Nat.le_refl _,Or.inr rfl,by simp⟩
  | capacity+1,before => match actual : before.move with
    | none => ⟨before,[],.nil before,by simp,Or.inl actual,by simp⟩
    | some (event,next) =>
        let later := run capacity next
        ⟨later.endpoint,event::later.work,.step actual later.history,by have := later.covered;simp only [List.length_cons];omega,
          later.exhausted.imp_right (fun same => by simp only [List.length_cons,same]),by
            have := later.conservation;have := Cursor.move_decreases actual;simp only [List.length_cons];omega⟩

theorem run_sufficient (before : Cursor original) (capacity : Nat) (enough : before.rank ≤ capacity) :
    (run capacity before).endpoint.completed.isSome = true := by
  apply (Cursor.completed_iff_stopped _).mpr
  rcases (run capacity before).exhausted with stopped | full
  · exact stopped
  apply (Cursor.stopped_iff_zero _).mpr
  have := (run capacity before).conservation;omega

theorem run_work_exact (before : Cursor original) (available : Nat) :
    (run available before).work.length = min available before.rank := by
  have covered := (run available before).covered
  have conserved := (run available before).conservation
  rcases (run available before).exhausted with stopped | full
  · have zero := (Cursor.stopped_iff_zero _).mp stopped
    rw [zero] at conserved
    have same : (run available before).work.length = before.rank := by omega
    rw [same,Nat.min_eq_right (by omega)]
  · rw [full,Nat.min_eq_left (by omega)]
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Funding.Source
