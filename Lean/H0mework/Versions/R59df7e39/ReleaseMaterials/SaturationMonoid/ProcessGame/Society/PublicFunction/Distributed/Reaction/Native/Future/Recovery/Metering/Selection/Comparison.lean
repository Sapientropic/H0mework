import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering.Selection.Source
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering.SearchSource.Selection
open Institutions.Capitalism.Universal.Source.Program
namespace Primitive
-- The upper Query kernel imports Recovery; keep this native Nat atom below that cycle.
inductive Event where
  | naturalLe (left right : Nat) (answer : Bool)
def compare (left right : Nat) : Decidable (left+1 ≤ right) × Event :=
  let answer := inferInstanceAs (Decidable (left+1 ≤ right))
  (answer,.naturalLe (left+1) right (@decide _ answer))
end Primitive
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {old : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {oldDepth : Nat} {word : List (Action old)}
  {stage : Point (old := old) (oldDepth := oldDepth) (word := word)}
abbrev Event := Primitive.Event
def compare (left right : Winner stage) : Winner stage × Event :=
  let made := Primitive.compare left.row.value right.row.value
  (@ite _ (left.row.value+1 ≤ right.row.value) made.1 right left,made.2)
theorem compare_winner (left right : Winner stage) : (compare left right).1 = left.prefer right := by
  unfold compare Primitive.compare Winner.prefer
  dsimp only
  simp only [Nat.add_one_le_iff]

theorem compare_event (left right : Winner stage) : (compare left right).2 =
    .naturalLe (left.row.value+1) right.row.value (decide (left.row.value < right.row.value)) := by
  unfold compare Primitive.compare
  dsimp only
  congr 1

inductive Cursor (stage : Point (old := old) (oldDepth := oldDepth) (word := word)) where
  | state {preparations : List (List (Action old))} (pending : Scores stage preparations) (winner : Winner stage)
def Cursor.value : Cursor stage → Winner stage
  | .state pending winner => pending.fold winner
def Cursor.rank : Cursor stage → Nat
  | .state (preparations := preparations) _ _ => preparations.length
def Cursor.completed : Cursor stage → Option (Winner stage)
  | .state .nil winner => some winner
  | .state (.cons ..) _ => none
def Cursor.move : Cursor stage → Option (Event × Cursor stage)
  | .state .nil _ => none
  | .state (.cons head tail) winner =>
      let made := compare winner ⟨_,head⟩
      some (made.2,.state tail made.1)
theorem Cursor.move_value {before after : Cursor stage} {event : Event}
    (actual : before.move = some (event,after)) : after.value = before.value := by
  cases before with
  | state pending winner =>
    cases pending with
    | nil => cases actual
    | cons head tail =>
      cases actual
      simp only [Cursor.value,compare_winner,Scores.fold]
theorem Cursor.move_decreases {before after : Cursor stage} {event : Event}
    (actual : before.move = some (event,after)) : after.rank+1 = before.rank := by
  cases before with
  | state pending winner =>
    cases pending with
    | nil => cases actual
    | cons => cases actual;rfl
theorem Cursor.completed_value {current : Cursor stage} {winner : Winner stage}
    (actual : current.completed = some winner) : winner = current.value := by
  cases current with
  | state pending start =>
    cases pending with
    | nil => cases actual;rfl
    | cons => cases actual
theorem Cursor.completed_iff_stopped (current : Cursor stage) : current.completed.isSome = true ↔ current.move = none := by
  cases current with
  | state pending winner => cases pending <;> simp [Cursor.completed,Cursor.move]
theorem Cursor.stopped_iff_zero (current : Cursor stage) : current.move = none ↔ current.rank = 0 := by
  cases current with
  | state pending winner => cases pending <;> simp [Cursor.move,Cursor.rank]

inductive History : Cursor stage → Cursor stage → List Event → Prop
  | nil (before) : History before before []
  | step {before middle after event work} (actual : before.move = some (event,middle))
      (later : History middle after work) : History before after (event::work)
theorem History.append : {before middle after : Cursor stage} → {left right : List Event} →
    History before middle left → History middle after right → History before after (left++right)
  | _,_,_,_,_,.nil _,later => later
  | _,_,_,_,_,.step actual past,later => .step actual (History.append past later)
theorem History.value {before after : Cursor stage} {work : List Event} (history : History before after work) : after.value = before.value := by
  induction history with
  | nil => rfl
  | step actual _ ih => exact ih.trans (Cursor.move_value actual)
theorem History.conservation {before after : Cursor stage} {work : List Event} (history : History before after work) :
    after.rank+work.length = before.rank := by
  induction history with
  | nil => simp
  | step actual _ ih => have smaller := Cursor.move_decreases actual;simp only [List.length_cons];omega

def initial {catalogue : List (List (Action old))} : Scores stage ([]::catalogue) → Cursor stage
  | .cons baseline tail => .state tail ⟨[],baseline⟩
variable {catalogue : List (List (Action old))}
structure Execution (scores : Scores stage ([]::catalogue)) where
  private mk ::
  winner : Winner stage
  work : List Event
  history : History (initial scores) (.state .nil winner) work
private def foldExecution {preparations : List (List (Action old))} (pending : Scores stage preparations) (start : Winner stage) :
    {result : Winner stage × List Event // History (.state pending start) (.state .nil result.1) result.2} :=
  match pending with
  | .nil => ⟨(start,[]),.nil _⟩
  | .cons head tail =>
      let made := compare start ⟨_,head⟩
      let later := foldExecution tail made.1
      ⟨(later.val.1,made.2::later.val.2),.step rfl later.property⟩
def execute {catalogue : List (List (Action old))} (scores : Scores stage ([]::catalogue)) : Execution scores :=
  match scores with
  | .cons baseline tail =>
      let made := foldExecution tail ⟨[],baseline⟩
      ⟨made.val.1,made.val.2,made.property⟩
variable {catalogue : List (List (Action old))} {scores : Scores stage ([]::catalogue)}
theorem Execution.winner_exact (execution : Execution scores) : execution.winner = scores.winner := by
  have same := execution.history.value
  cases scores
  exact same

theorem Execution.work_length (execution : Execution scores) : execution.work.length = catalogue.length := by
  have paid := execution.history.conservation
  cases scores
  simpa only [Cursor.rank,initial,List.length_nil,Nat.zero_add] using paid
private theorem History.unique_complete {before first second : Cursor stage} {left right : List Event}
    (a : History before first left) (b : History before second right) (doneA : first.move = none) (doneB : second.move = none) :
    first = second ∧ left = right := by
  induction a generalizing second right with
  | nil =>
    cases b with
    | nil => exact ⟨rfl,rfl⟩
    | step actual later => rw [doneA] at actual;cases actual
  | step actual later ih =>
    cases b with
    | nil => rw [doneB] at actual;cases actual
    | step other rest =>
      have same := Option.some.inj (actual.symm.trans other)
      cases same
      obtain ⟨endpoint,work⟩ := ih rest doneA doneB
      exact ⟨endpoint,by rw [work]⟩
theorem Execution.unique (first second : Execution scores) : first = second := by
  obtain ⟨same,work⟩ := History.unique_complete first.history second.history rfl rfl
  cases first;cases second;cases same;cases work;rfl

structure Session (scores : Scores stage ([]::catalogue)) where
  private mk ::
  current : Cursor stage
  work : List Event
  history : History (initial scores) current work
def Session.initial (scores : Scores stage ([]::catalogue)) : Session scores := ⟨Selection.initial scores,[],.nil _⟩
def Session.rank (session : Session scores) := session.current.rank
def Session.move (session : Session scores) : Option (Event × Session scores) :=
  match actual : session.current.move with
  | none => none
  | some (event,next) => some (event,⟨next,session.work++[event],session.history.append (.step actual (.nil _))⟩)
def Session.completed (session : Session scores) : Option (Execution scores) :=
  match same : session.current with
  | .state .nil winner => some ⟨winner,session.work,by have h := session.history;rw [same] at h;exact h⟩
  | .state (.cons ..) _ => none
theorem Session.move_appends {before after : Session scores} {event : Event} (actual : before.move = some (event,after)) :
    after.work = before.work++[event] := by
  dsimp only [Session.move] at actual
  split at actual
  · cases actual
  · cases actual;rfl
theorem Session.move_decreases {before after : Session scores} {event : Event} (actual : before.move = some (event,after)) :
    after.rank+1 = before.rank := by
  dsimp only [Session.move] at actual
  split at actual
  · cases actual
  · rename_i event next moved
    cases actual;exact Cursor.move_decreases moved
theorem Session.completed_work {session : Session scores} {execution : Execution scores}
    (actual : session.completed = some execution) : execution.work = session.work := by
  dsimp only [Session.completed] at actual
  split at actual
  · cases actual;rfl
  · cases actual
theorem Session.completed_iff_stopped (session : Session scores) : session.completed.isSome = true ↔ session.move = none := by
  rcases session with ⟨current,work,history⟩
  cases current with
  | state pending winner =>
    cases pending with
    | nil => constructor <;> intro _ <;> rfl
    | cons head tail => constructor <;> intro impossible <;> cases impossible
theorem Session.stopped_iff_zero (session : Session scores) : session.move = none ↔ session.rank = 0 := by
  have native := session.current.stopped_iff_zero
  unfold Session.move Session.rank
  split <;> simp_all

theorem Session.conservation (session : Session scores) : session.rank+session.work.length = catalogue.length := by
  have paid := session.history.conservation
  cases scores
  exact paid
theorem Session.initial_rank : (Session.initial scores).rank = (execute scores).work.length := by
  rw [Execution.work_length]
  cases scores;rfl

def Execution.endpoint (execution : Execution scores) := execution.winner.scored.endpoint
theorem Execution.chosen (execution : Execution scores) : execution.winner.row.proposal = choose stage catalogue := by
  rw [execution.winner_exact]
  exact congrArg Ranked.proposal scores.winner_exact
theorem Execution.endpoint_exact (execution : Execution scores) : execution.endpoint = restored stage catalogue := by
  unfold Execution.endpoint
  rw [execution.winner.scored.endpoint_exact]
  have chosen := congrArg Search.Proposal.preparation execution.chosen
  change execution.winner.preparation = (choose stage catalogue).preparation at chosen
  rw [chosen];rfl
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering.SearchSource.Selection
