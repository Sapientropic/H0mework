import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {source : SourceQuota.Generated prepared}
  {catalogue : SourceQuota.Catalogue source.snapshot} (all : Candidates source catalogue)

abbrev Probe := Sigma fun index : Index prepared => Table all index
def probes : List (Probe all) := (keys prepared).flatMap fun index =>
  (tables all index).map fun table => ⟨index,table⟩
def Holds (left right : Offer all) (probe : Probe all) : Prop :=
  benefit (initial input prepared.saved[probe.1].point)
    ((left.view probe.1).tensor (rival all probe.1 probe.2))
    ((right.view probe.1).tensor (rival all probe.1 probe.2))
instance (left right : Offer all) (probe : Probe all) : Decidable (Holds all left right probe) := by unfold Holds;infer_instance

def Passed (left right : Offer all) (todo : List (Probe all)) : Prop :=
  ∀ probe ∈ todo,Holds all left right probe

theorem all_probes_are_the_original_benefit (left right : Offer all) :
    Passed all left right (probes all) ↔ Benefit all left right := by
  constructor
  · intro checked index table inside
    exact checked ⟨index,table⟩ (List.mem_flatMap.mpr ⟨index,List.mem_finRange _,List.mem_map.mpr ⟨table,inside,rfl⟩⟩)
  · intro valid probe inside
    obtain ⟨index,_,mapped⟩ := List.mem_flatMap.mp inside
    obtain ⟨table,listed,same⟩ := List.mem_map.mp mapped
    subst probe
    exact valid index table listed

def Strict (candidate other : Offer all) := Benefit all other candidate ∧ ¬ Benefit all candidate other
def Maximal (candidate : Offer all) := ∀ other ∈ offers all,¬ Strict all candidate other

def choice (candidate : Offer all) (maximal : Maximal all candidate) : Choice all :=
  ⟨candidate,every_paid_accepted_policy_is_retained all candidate,fun other inside strict =>
    maximal other inside ⟨(vector_iff all _ _).mp strict.1,fun reverse => strict.2 ((vector_iff all _ _).mpr reverse)⟩⟩

def Safe (candidate : Offer all) (remaining : List (Offer all)) :=
  (∀ other ∈ remaining,¬ Strict all candidate other) → Maximal all candidate

private theorem discard {candidate other : Offer all} {rest : List (Offer all)}
    (safe : Safe all candidate (other::rest)) (cleared : ¬ Strict all candidate other) : Safe all candidate rest := by
  intro later policy inside
  apply safe _ policy inside
  intro rival member
  rcases List.mem_cons.mp member with same | remaining
  · subst rival;exact cleared
  · exact later rival remaining

inductive Frame (candidate : Offer all) where
  | rivals (remaining : List (Offer all))
      (listed : ∀ other ∈ remaining,other ∈ offers all) (safe : Safe all candidate remaining)
  | forward (other : Offer all) (listed : other ∈ offers all) (rest : List (Offer all))
      (rest_listed : ∀ rival ∈ rest,rival ∈ offers all) (safe : Safe all candidate (other::rest))
      (todo : List (Probe all)) (within : ∀ probe ∈ todo,probe ∈ probes all)
      (passed : Passed all other candidate todo → Benefit all other candidate)
  | reverse (other : Offer all) (listed : other ∈ offers all) (rest : List (Offer all))
      (rest_listed : ∀ rival ∈ rest,rival ∈ offers all) (safe : Safe all candidate (other::rest))
      (forward : Benefit all other candidate)
      (todo : List (Probe all)) (within : ∀ probe ∈ todo,probe ∈ probes all)
      (passed : Passed all candidate other todo → Benefit all candidate other)
  | verified (maximal : Maximal all candidate)
  | dominated (other : Offer all) (listed : other ∈ offers all) (strict : Strict all candidate other)

def initial (candidate : Offer all) : Frame all candidate := .rivals (offers all) (fun _ member => member) (fun all => all)
def initialUsing (supplied : List (Offer all)) (exact_source : supplied = offers all) (candidate : Offer all) : Frame all candidate :=
  .rivals supplied (fun _ member => exact_source ▸ member) (by
    intro cleared other member
    exact cleared other (by rw [exact_source];exact member))

theorem initialUsing_eq (supplied : List (Offer all)) (exact_source : supplied = offers all) (candidate : Offer all) :
    initialUsing all supplied exact_source candidate = initial all candidate := by cases exact_source;rfl

inductive Control where | enter | forwardComplete | reverseComplete | complete
inductive Event where
  | control (operation : Control)
  | yes (left right : Offer all) (probe : Probe all) (valid : Holds all left right probe)
  | no (left right : Offer all) (probe : Probe all) (invalid : ¬ Holds all left right probe)

private theorem pass_cons {left right : Offer all} {head : Probe all} {tail : List (Probe all)}
    (head_passed : Holds all left right head) (later : Passed all left right tail) : Passed all left right (head::tail) := by
  intro probe member
  rcases List.mem_cons.mp member with same | inside
  · subst probe;exact head_passed
  · exact later probe inside

private theorem failed_probe {left right : Offer all} {probe : Probe all}
    (inside : probe ∈ probes all) (failed : ¬ Holds all left right probe) : ¬ Benefit all left right :=
  fun complete => failed ((all_probes_are_the_original_benefit all left right).mpr complete probe inside)

def advance {candidate : Offer all} : Frame all candidate → Option (Frame all candidate × Event all)
  | .verified _ | .dominated .. => none
  | .rivals [] _ safe => some (.verified (safe (by intro other inside;cases inside)),.control .complete)
  | .rivals (other::rest) listed safe => some
      (.forward other (listed other List.mem_cons_self) rest
        (fun rival member => listed rival (List.mem_cons_of_mem _ member)) safe
        (probes all) (fun _ member => member) ((all_probes_are_the_original_benefit all other candidate).mp),.control .enter)
  | .forward other listed rest rest_listed safe [] _ passed => some
      (.reverse other listed rest rest_listed safe (passed (by intro probe inside;cases inside))
        (probes all) (fun _ member => member) ((all_probes_are_the_original_benefit all candidate other).mp),.control .forwardComplete)
  | .forward other listed rest rest_listed safe (head::tail) within passed =>
      if valid : Holds all other candidate head then some
        (.forward other listed rest rest_listed safe tail
          (fun probe member => within probe (List.mem_cons_of_mem _ member))
          (fun later => passed (pass_cons all valid later)),.yes other candidate head valid)
      else some (.rivals rest rest_listed (discard all safe (fun strict =>
        failed_probe all (within head List.mem_cons_self) valid strict.1)),.no other candidate head valid)
  | .reverse other _ rest rest_listed safe forward [] _ passed => some
      (.rivals rest rest_listed (discard all safe (fun strict => strict.2 (passed (by intro probe inside;cases inside)))),.control .reverseComplete)
  | .reverse other listed rest rest_listed safe forward (head::tail) within passed =>
      if valid : Holds all candidate other head then some
        (.reverse other listed rest rest_listed safe forward tail
          (fun probe member => within probe (List.mem_cons_of_mem _ member))
          (fun later => passed (pass_cons all valid later)),.yes candidate other head valid)
      else some (.dominated other listed ⟨forward,failed_probe all (within head List.mem_cons_self) valid⟩,
        .no candidate other head valid)

def advanceUsing (supplied : List (Probe all)) (exact_source : supplied = probes all) {candidate : Offer all} : Frame all candidate → Option (Frame all candidate × Event all)
  | .verified _ | .dominated .. => none
  | .rivals [] _ safe => some (.verified (safe (by intro other inside;cases inside)),.control .complete)
  | .rivals (other::rest) listed safe => some
      (.forward other (listed other List.mem_cons_self) rest
        (fun rival member => listed rival (List.mem_cons_of_mem _ member)) safe
        supplied (fun _ member => exact_source ▸ member)
        (fun passed => (all_probes_are_the_original_benefit all other candidate).mp (by rw [←exact_source];exact passed)),.control .enter)
  | .forward other listed rest rest_listed safe [] _ passed => some
      (.reverse other listed rest rest_listed safe (passed (by intro probe inside;cases inside))
        supplied (fun _ member => exact_source ▸ member)
        (fun passed => (all_probes_are_the_original_benefit all candidate other).mp (by rw [←exact_source];exact passed)),.control .forwardComplete)
  | .forward other listed rest rest_listed safe (head::tail) within passed =>
      if valid : Holds all other candidate head then some
        (.forward other listed rest rest_listed safe tail
          (fun probe member => within probe (List.mem_cons_of_mem _ member))
          (fun later => passed (pass_cons all valid later)),.yes other candidate head valid)
      else some (.rivals rest rest_listed (discard all safe (fun strict =>
        failed_probe all (within head List.mem_cons_self) valid strict.1)),.no other candidate head valid)
  | .reverse other _ rest rest_listed safe forward [] _ passed => some
      (.rivals rest rest_listed (discard all safe (fun strict => strict.2 (passed (by intro probe inside;cases inside)))),.control .reverseComplete)
  | .reverse other listed rest rest_listed safe forward (head::tail) within passed =>
      if valid : Holds all candidate other head then some
        (.reverse other listed rest rest_listed safe forward tail
          (fun probe member => within probe (List.mem_cons_of_mem _ member))
          (fun later => passed (pass_cons all valid later)),.yes candidate other head valid)
      else some (.dominated other listed ⟨forward,failed_probe all (within head List.mem_cons_self) valid⟩,
        .no candidate other head valid)

theorem advanceUsing_eq (supplied : List (Probe all)) (exact_source : supplied = probes all)
    {candidate : Offer all} (before : Frame all candidate) : advanceUsing all supplied exact_source before = advance all before := by
  cases exact_source;rfl

def Frame.finished {candidate : Offer all} : Frame all candidate → Bool
  | .verified _ | .dominated .. => true
  | _ => false

def Frame.rank {candidate : Offer all} : Frame all candidate → Nat
  | .rivals remaining .. => 1+remaining.length*(2*(probes all).length+3)
  | .forward _ _ rest _ _ todo .. => rest.length*(2*(probes all).length+3)+todo.length+(probes all).length+3
  | .reverse _ _ rest _ _ _ todo .. => rest.length*(2*(probes all).length+3)+todo.length+2
  | .verified _ | .dominated .. => 0

theorem unfinished_has_an_actual_next {candidate : Offer all} (before : Frame all candidate) :
    advance all before = none ↔ before.finished all = true := by
  cases before with
  | rivals remaining listed safe => cases remaining <;> simp [advance,Frame.finished]
  | forward other listed rest rest_listed safe todo within passed =>
    cases todo with
    | nil => simp [advance,Frame.finished]
    | cons head tail => dsimp only [advance,Frame.finished];split <;> simp
  | reverse other listed rest rest_listed safe forward todo within passed =>
    cases todo with
    | nil => simp [advance,Frame.finished]
    | cons head tail => dsimp only [advance,Frame.finished];split <;> simp
  | verified | dominated => simp [advance,Frame.finished]

theorem each_actual_step_decreases_the_source_rank {candidate : Offer all} {before after : Frame all candidate}
    {event : Event all} (step : advance all before = some (after,event)) : after.rank all < before.rank all := by
  cases before with
  | verified | dominated => cases step
  | rivals remaining listed safe =>
    cases remaining <;> dsimp only [advance] at step
    all_goals cases Option.some.inj step
    all_goals (simp only [Frame.rank,List.length_cons,List.length_nil,Nat.add_mul,Nat.one_mul]; omega)
  | forward other listed rest rest_listed safe todo within passed =>
    cases todo with
    | nil =>
      dsimp only [advance] at step;cases Option.some.inj step
      simp only [Frame.rank,List.length_nil];omega
    | cons head tail =>
      dsimp only [advance] at step;split at step
      all_goals cases Option.some.inj step
      all_goals (simp only [Frame.rank,List.length_cons]; omega)
  | reverse other listed rest rest_listed safe forward todo within passed =>
    cases todo with
    | nil =>
      dsimp only [advance] at step;cases Option.some.inj step
      simp only [Frame.rank,List.length_nil];omega
    | cons head tail =>
      dsimp only [advance] at step;split at step
      all_goals cases Option.some.inj step
      all_goals (simp only [Frame.rank,List.length_cons]; omega)

inductive Trace {candidate : Offer all} : Frame all candidate → Frame all candidate → List (Event all) → Prop
  | nil (before) : Trace before before []
  | step {before middle after event work} (observed : advance all before = some (middle,event))
      (later : Trace middle after work) : Trace before after (event::work)

structure Run {candidate : Offer all} (before : Frame all candidate) (capacity : Nat) where
  private mk ::
  endpoint : Frame all candidate
  work : List (Event all)
  trace : Trace all before endpoint work
  fits : work.length ≤ capacity

def execute {candidate : Offer all} : (capacity : Nat) → (before : Frame all candidate) → Run all before capacity
  | 0,before => ⟨before,[],.nil before,by rfl⟩
  | capacity+1,before => match step : advance all before with
    | none => ⟨before,[],.nil before,Nat.zero_le _⟩
    | some (after,event) =>
        let later := execute capacity after
        ⟨later.endpoint,event::later.work,.step step later.trace,by have := later.fits;simpa only [List.length_cons] using Nat.succ_le_succ this⟩

theorem zero_credit_does_not_evaluate_any_probe {candidate : Offer all} (before : Frame all candidate) :
    (execute all 0 before).endpoint = before ∧ (execute all 0 before).work = [] := ⟨rfl,rfl⟩

theorem source_rank_capacity_completes {candidate : Offer all} (capacity : Nat) (before : Frame all candidate)
    (enough : before.rank all ≤ capacity) : (execute all capacity before).endpoint.finished all = true := by
  induction capacity generalizing before with
  | zero =>
    cases before <;> simp_all [Frame.rank,Frame.finished,execute]
  | succ capacity ih =>
    unfold execute
    split
    · rename_i stopped
      exact (unfinished_has_an_actual_next all before).mp stopped
    · rename_i after event step
      exact ih after (by have smaller := each_actual_step_decreases_the_source_rank all step;omega)

namespace Trace
variable {all}
theorem append {candidate : Offer all} {first middle last : Frame all candidate} {front back : List (Event all)}
    (one : Trace all first middle front) (two : Trace all middle last back) : Trace all first last (front++back) := by
  induction one with
  | nil => exact two
  | step observed later ih => exact .step observed (ih two)
end Trace

def Run.resume {candidate : Offer all} {before : Frame all candidate} {capacity : Nat}
    (paid : Run all before capacity) (more : Nat) : Run all before (capacity+more) :=
  let later := execute all more paid.endpoint
  ⟨later.endpoint,paid.work++later.work,paid.trace.append later.trace,by
    have first := paid.fits;have second := later.fits;rw [List.length_append];omega⟩

theorem resumption_keeps_the_entire_paid_prefix {candidate : Offer all} {before : Frame all candidate} {capacity : Nat}
    (paid : Run all before capacity) (more : Nat) :
    (paid.resume all more).work = paid.work++(execute all more paid.endpoint).work := rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review
