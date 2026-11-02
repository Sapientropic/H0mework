import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.Operand.Tables.Source
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.Operand.Forecast
open Institutions.Capitalism.Universal.Source.Program
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq I]
  (code : Distributed.Code P G O T I)
  (schedule : Feedback.Residual.Schedule code) (input : Feedback.Input code) (seed : Feedback.State code) (horizon : Nat)

structure Completed where
  private mk ::
  state : Feedback.State code
  words : List (RawEvent P G O T I)
  state_exact : state = Feedback.Residual.run code schedule input seed horizon
  words_exact : words = Online.forecastWords code schedule input seed horizon
structure Cursor where
  private mk ::
  offset : Nat
  bounded : offset ≤ horizon
  state : Feedback.State code
  words : List (RawEvent P G O T I)
  state_exact : state = Feedback.Residual.run code schedule input seed offset
  words_exact : words = Online.forecastWords code schedule input seed offset

def initial : Cursor code schedule input seed horizon := ⟨0,Nat.zero_le _,seed,[],rfl,rfl⟩
variable {code schedule input seed horizon}
def Cursor.rank (cursor : Cursor code schedule input seed horizon) := horizon-cursor.offset
structure Event where
  offset : Nat
  before : Feedback.State code
  submitted : RawEvent P G O T I
  after : Feedback.State code
  word_actual : submitted = Feedback.word code (schedule offset) input before
  step_actual : after = Feedback.advance code (schedule offset) input before

def Cursor.move (cursor : Cursor code schedule input seed horizon) :
    Option (Event (code := code) (schedule := schedule) (input := input) × Cursor code schedule input seed horizon) :=
  if active : cursor.offset < horizon then
    let submitted := Feedback.word code (schedule cursor.offset) input cursor.state
    let next := Feedback.advance code (schedule cursor.offset) input cursor.state
    some (⟨cursor.offset,cursor.state,submitted,next,rfl,rfl⟩,
      ⟨cursor.offset+1,by omega,next,cursor.words++[submitted],by
        dsimp only [next];rw [cursor.state_exact];rfl,by dsimp only [submitted];rw [cursor.words_exact,cursor.state_exact];rfl⟩)
  else none

def Cursor.completed (cursor : Cursor code schedule input seed horizon) : Option (Completed code schedule input seed horizon) :=
  if done : cursor.offset = horizon then some ⟨cursor.state,cursor.words,
    by simpa only [done] using cursor.state_exact,by simpa only [done] using cursor.words_exact⟩ else none

theorem Cursor.move_decreases {before after : Cursor code schedule input seed horizon}
    {event : Event (code := code) (schedule := schedule) (input := input)}
    (actual : before.move = some (event,after)) : after.rank+1 = before.rank := by
  unfold Cursor.move at actual
  split at actual
  · rename_i active
    cases actual
    dsimp only [Cursor.rank]
    omega
  · cases actual

theorem Cursor.stopped_iff_zero (cursor : Cursor code schedule input seed horizon) : cursor.move = none ↔ cursor.rank = 0 := by
  unfold Cursor.move Cursor.rank
  split <;> simp_all
  omega

theorem Cursor.completed_iff_stopped (cursor : Cursor code schedule input seed horizon) :
    cursor.completed.isSome = true ↔ cursor.move = none := by
  have bounded := cursor.bounded
  unfold Cursor.completed Cursor.move
  split <;> split <;> simp_all
  all_goals omega

inductive History : Cursor code schedule input seed horizon → Cursor code schedule input seed horizon →
    List (Event (code := code) (schedule := schedule) (input := input)) → Prop
  | nil (before) : History before before []
  | step {before middle after event work} (actual : before.move = some (event,middle))
      (later : History middle after work) : History before after (event::work)
structure Run (before : Cursor code schedule input seed horizon) (capacity : Nat) where
  private mk ::
  endpoint : Cursor code schedule input seed horizon
  work : List (Event (code := code) (schedule := schedule) (input := input))
  history : History before endpoint work
  covered : work.length ≤ capacity
  exhausted : endpoint.move = none ∨ work.length = capacity
  conservation : endpoint.rank+work.length = before.rank

def run : (capacity : Nat) → (before : Cursor code schedule input seed horizon) → Run before capacity
  | 0,before => ⟨before,[],.nil before,Nat.le_refl _,Or.inr rfl,by simp⟩
  | capacity+1,before => match actual : before.move with
    | none => ⟨before,[],.nil before,by simp,Or.inl actual,by simp⟩
    | some (event,next) =>
        let later := run capacity next
        ⟨later.endpoint,event::later.work,.step actual later.history,by have := later.covered;simp only [List.length_cons];omega,
          later.exhausted.imp_right (fun same => by simp only [List.length_cons,same]),by
            have := later.conservation;have := Cursor.move_decreases actual;simp only [List.length_cons];omega⟩

theorem run_sufficient (before : Cursor code schedule input seed horizon) (capacity : Nat) (enough : before.rank ≤ capacity) :
    (run capacity before).endpoint.completed.isSome = true := by
  apply (Cursor.completed_iff_stopped _).mpr
  rcases (run capacity before).exhausted with stopped | full
  · exact stopped
  apply (Cursor.stopped_iff_zero _).mpr
  have := (run capacity before).conservation;omega

theorem run_work_exact (before : Cursor code schedule input seed horizon) (capacity : Nat) :
    (run capacity before).work.length = min capacity before.rank := by
  have bounded := (run capacity before).covered
  have conserved := (run capacity before).conservation
  rcases (run capacity before).exhausted with stopped | full
  · have zero := (Cursor.stopped_iff_zero _).mp stopped;omega
  · omega

theorem initial_rank : (initial code schedule input seed horizon).rank = horizon := rfl

theorem History.offsets {before after : Cursor code schedule input seed horizon}
    {work : List (Event (code := code) (schedule := schedule) (input := input))}
    (history : History before after work) : after.offset = before.offset+work.length := by
  induction history with
  | nil before => simp
  | @step before middle after event work actual later ih =>
      unfold Cursor.move at actual
      split at actual
      · cases actual
        simp only [List.length_cons] at *
        omega
      · cases actual

theorem Run.words_are_actual_history (before : Cursor code schedule input seed horizon) (capacity : Nat) :
    (run capacity before).endpoint.state.history = seed.history++(run capacity before).endpoint.words := by
  rw [(run capacity before).endpoint.state_exact,(run capacity before).endpoint.words_exact]
  exact Online.forecast_is_the_generated_history_suffix _ _ _ _ _

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.Operand.Forecast
