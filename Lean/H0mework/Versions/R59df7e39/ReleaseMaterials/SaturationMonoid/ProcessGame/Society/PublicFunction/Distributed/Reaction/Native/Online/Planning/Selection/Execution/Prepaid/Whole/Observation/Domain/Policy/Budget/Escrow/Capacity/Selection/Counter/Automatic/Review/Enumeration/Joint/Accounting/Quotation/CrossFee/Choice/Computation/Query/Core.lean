import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Payment.Collection
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query

inductive Kind where
  | truth (claim : Prop)
  | number (claim : Nat → Prop)
def Value : Kind → Type
  | .truth claim => Decidable claim
  | .number claim => {value : Nat // claim value}

inductive Atom (Key : Type) : Kind → Type where
  | boolean (value : Bool) : Atom Key (.truth (value = true))
  | equal (left right : Key) : Atom Key (.truth (left = right))
  | natural (left right : Nat) : Atom Key (.truth (left ≤ right))
  | rational (left right : ℚ) : Atom Key (.truth (left ≤ right))
  | increment (before : Nat) : Atom Key (.number (fun after => after = before+1))

variable {Key : Type} [DecidableEq Key] {kind goal : Kind}
def Atom.perform : {kind : Kind} → (query : Atom Key kind) → Value kind × NativeBenefit.Event Key
  | _,.boolean value => (inferInstanceAs (Decidable (value = true)),.boolean value)
  | _,.equal left right =>
      let answer := inferInstanceAs (Decidable (left = right))
      (answer,.keyEqual left right (@decide _ answer))
  | _,.natural left right =>
      let answer := inferInstanceAs (Decidable (left ≤ right))
      (answer,.naturalLe left right (@decide _ answer))
  | _,.rational left right =>
      let answer := inferInstanceAs (Decidable (left ≤ right))
      (answer,.rationalLe left right (@decide _ answer))
  | _,.increment before => (⟨before+1,rfl⟩,.increment before)

inductive Code (Key : Type) : Kind → Type where
  | pure {kind : Kind} (value : Value kind) : Code Key kind
  | atom {kind : Kind} (query : Atom Key kind) : Code Key kind
  | bind {first last : Kind} (body : Code Key first) (later : Value first → Code Key last) : Code Key last

-- This evaluator is only the denotation used by the coherence proof.
def Code.eval : {kind : Kind} → Code Key kind → Value kind
  | _,.pure value => value
  | _,.atom query => query.perform.1
  | _,.bind body later => (later body.eval).eval

-- This rank is a logical normalization measure, never a runtime quotation.
def Code.cost : {kind : Kind} → Code Key kind → Nat
  | _,.pure _ => 1
  | _,.atom _ => 2
  | _,.bind body later => 1 + body.cost + (later body.eval).cost

theorem Code.cost_positive (body : Code Key kind) : 0 < body.cost := by
  cases body <;> simp only [Code.cost] <;> omega

inductive Kont (Key : Type) : Kind → Kind → Type where
  | done {kind : Kind} : Kont Key kind kind
  | bind {first middle last : Kind} (later : Value first → Code Key middle) (rest : Kont Key middle last) : Kont Key first last

def Kont.apply : {kind goal : Kind} → Kont Key kind goal → Value kind → Value goal
  | _,_,.done,value => value
  | _,_,.bind later rest,value => rest.apply (later value).eval

def Kont.cost : {kind goal : Kind} → Kont Key kind goal → Value kind → Nat
  | _,_,.done,_ => 0
  | _,_,.bind later rest,value => (later value).cost + rest.cost (later value).eval

inductive Event (Key : Type) where
  | enter | resume | finish
  | query (event : NativeBenefit.Event Key)

inductive Phase (Key : Type) (goal : Kind) where
  | running {kind : Kind} (body : Code Key kind) (later : Kont Key kind goal)
  | done (value : Value goal)

def Phase.meaning : Phase Key goal → Value goal
  | .running body later => later.apply body.eval
  | .done value => value

def Phase.move : Phase Key goal → Option (Event Key × Phase Key goal)
  | .running (.pure value) .done => some (.finish,.done value)
  | .running (.pure value) (.bind later rest) => some (.resume,.running (later value) rest)
  | .running (.atom query) later =>
      let made := query.perform
      some (.query made.2,.running (.pure made.1) later)
  | .running (.bind body later) rest => some (.enter,.running body (.bind later rest))
  | .done _ => none

def Phase.rank : Phase Key goal → Nat
  | .running body later => body.cost + later.cost body.eval
  | .done _ => 0

theorem Phase.move_rank (phase next : Phase Key goal) (event : Event Key)
    (actual : phase.move = some (event,next)) : next.rank + 1 = phase.rank := by
  cases phase with
  | done _ => cases actual
  | running body later =>
      cases body with
      | pure value => cases later <;> cases actual <;> simp [Phase.rank,Code.cost,Code.eval,Kont.cost,Nat.add_comm]
      | atom query => cases actual;simp [Phase.rank,Code.cost,Code.eval];omega
      | bind body nextCode => cases actual;simp [Phase.rank,Code.cost,Code.eval,Kont.cost];omega

theorem Phase.stopped_iff_zero (phase : Phase Key goal) : phase.move = none ↔ phase.rank = 0 := by
  cases phase with
  | done _ => simp [Phase.move,Phase.rank]
  | running body later =>
      cases body with
      | pure value => cases later <;> simp [Phase.move,Phase.rank,Code.cost,Kont.cost]
      | atom query => simp [Phase.move,Phase.rank,Code.cost]
      | bind body nextCode => simp [Phase.move,Phase.rank,Code.cost]

theorem Phase.move_preserves (phase next : Phase Key goal) (event : Event Key) (actual : phase.move = some (event,next)) :
    next.meaning = phase.meaning := by
  cases phase with
  | done _ => cases actual
  | running body later =>
      cases body with
      | pure value => cases later <;> cases actual <;> rfl
      | atom query => cases actual;rfl
      | bind body nextCode => cases actual;rfl

structure State (original : Code Key goal) where
  private mk ::
  phase : Phase Key goal
  coherent : phase.meaning = original.eval

def initial (original : Code Key goal) : State original := ⟨.running original .done,rfl⟩
def State.move {original : Code Key goal} (state : State original) : Option (Event Key × State original) :=
  match actual : state.phase.move with
  | none => none
  | some (event,next) => some (event,⟨next,(Phase.move_preserves _ _ _ actual).trans state.coherent⟩)

def State.completed {original : Code Key goal} (state : State original) : Option (Value goal) :=
  match state.phase with | .done value => some value | _ => none

theorem State.completed_exact {original : Code Key goal} (state : State original) (value : Value goal)
    (actual : state.completed = some value) : value = original.eval := by
  unfold State.completed at actual
  split at actual
  · rename_i v shape
    cases actual
    have := state.coherent;rw [shape] at this;exact this
  · cases actual

theorem State.completed_iff_stopped {original : Code Key goal} (state : State original) :
    state.completed.isSome = true ↔ state.move = none := by
  rcases state with ⟨phase,coherent⟩
  cases phase with
  | done value => simp [State.completed,State.move,Phase.move]
  | running body later => cases body with
    | pure value => cases later <;> simp [State.completed,State.move,Phase.move]
    | atom query => simp [State.completed,State.move,Phase.move]
    | bind body nextCode => simp [State.completed,State.move,Phase.move]

def State.rank {original : Code Key goal} (state : State original) : Nat := state.phase.rank

theorem State.move_rank {original : Code Key goal} (state next : State original) (event : Event Key)
    (actual : state.move = some (event,next)) : next.rank + 1 = state.rank := by
  unfold State.move at actual
  split at actual
  · cases actual
  · rename_i ev stage moved
    simp only [Option.some.injEq,Prod.mk.injEq] at actual
    obtain ⟨rfl,rfl⟩ := actual
    exact Phase.move_rank _ _ _ moved

theorem State.stopped_iff_zero {original : Code Key goal} (state : State original) :
    state.move = none ↔ state.rank = 0 := by
  unfold State.move State.rank
  split
  · rename_i stopped
    simp only [true_iff]
    exact (Phase.stopped_iff_zero _).mp stopped
  · rename_i ev stage moved
    have positive := Phase.move_rank _ _ _ moved
    simp only [reduceCtorEq,false_iff]
    omega

structure Run {original : Code Key goal} (start : State original) (capacity : Nat) where
  private mk ::
  endpoint : State original
  work : List (Event Key)
  covered : work.length ≤ capacity
  exhausted : endpoint.move = none ∨ work.length = capacity
  conservation : endpoint.rank + work.length = start.rank

def run {original : Code Key goal} : (capacity : Nat) → (start : State original) → Run start capacity
  | 0,start => ⟨start,[],Nat.le_refl _,Or.inr rfl,by simp⟩
  | capacity+1,start =>
      match actual : start.move with
      | none => ⟨start,[],by simp,Or.inl actual,by simp⟩
      | some (event,next) =>
          let later := run capacity next
          ⟨later.endpoint,event::later.work,by have := later.covered;simp only [List.length_cons];omega,
            later.exhausted.imp_right (fun same => by simp only [List.length_cons,same]),by
              have := later.conservation
              have := State.move_rank _ _ _ actual
              simp only [List.length_cons];omega⟩

theorem run_sufficient {original : Code Key goal} (start : State original) (capacity : Nat)
    (enough : start.rank ≤ capacity) : (run capacity start).endpoint.completed.isSome = true := by
  apply (State.completed_iff_stopped _).mpr
  have finished := (run capacity start).exhausted
  rcases finished with stopped | exactCapacity
  · exact stopped
  · apply (State.stopped_iff_zero _).mpr
    have := (run capacity start).conservation
    omega

namespace Code
variable {P Q : Prop}
def transport (same : P ↔ Q) (body : Code Key (.truth P)) : Code Key (.truth Q) :=
  .bind body fun answer => .pure (match answer with
    | .isTrue yes => .isTrue (same.mp yes)
    | .isFalse no => .isFalse (fun yes => no (same.mpr yes)))
def conjunction (first : Code Key (.truth P)) (later : Unit → Code Key (.truth Q)) : Code Key (.truth (P ∧ Q)) :=
  .bind first fun answer => match answer with
  | .isFalse no => .pure (.isFalse (fun both => no both.1))
  | .isTrue yes => .bind (later ()) fun other => .pure (match other with
      | .isTrue proof => .isTrue ⟨yes,proof⟩
      | .isFalse no => .isFalse (fun both => no both.2))
def implication (first : Code Key (.truth P)) (later : Unit → Code Key (.truth Q)) : Code Key (.truth (P → Q)) :=
  .bind first fun answer => match answer with
  | .isFalse no => .pure (.isTrue (fun yes => False.elim (no yes)))
  | .isTrue yes => .bind (later ()) fun other => .pure (match other with
      | .isTrue proof => .isTrue (fun _ => proof)
      | .isFalse no => .isFalse (fun accepts => no (accepts yes)))
def negative (body : Code Key (.truth P)) : Code Key (.truth (¬P)) :=
  .bind body fun answer => .pure (match answer with
    | .isTrue yes => .isFalse (fun no => no yes)
    | .isFalse no => .isTrue no)
end Code

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query
