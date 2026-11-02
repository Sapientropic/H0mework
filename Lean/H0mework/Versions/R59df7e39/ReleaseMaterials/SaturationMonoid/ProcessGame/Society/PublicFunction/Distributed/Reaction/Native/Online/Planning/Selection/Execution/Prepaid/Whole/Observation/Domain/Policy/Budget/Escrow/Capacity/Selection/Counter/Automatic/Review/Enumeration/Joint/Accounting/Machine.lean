import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Joint.Accounting.Choice
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Machine
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input}
  {source : SourceQuota.Generated prepared} {catalogue : SourceQuota.Catalogue source.snapshot}
  {all : Candidates source catalogue}
namespace Scanner
variable (domain : List (Candidate all))
def Holds (_domain : List (Candidate all)) (left right : Candidate all) (axis : Axis all) := cost left axis ≤ cost right axis
instance (left right : Candidate all) (axis : Axis all) : Decidable (Holds domain left right axis) := inferInstanceAs (Decidable (_ ≤ _))
def Passed (left right : Candidate all) (todo : List (Axis all)) := ∀ axis ∈ todo,Holds domain left right axis
theorem all_probes_are_the_original_benefit (left right : Candidate all) : Passed domain left right (axes all) ↔ Distributed.NoWorse (axes all) cost left right := Iff.rfl
def Strict (_domain : List (Candidate all)) (candidate other : Candidate all) := Distributed.Improves (axes all) cost candidate other
def Maximal (candidate : Candidate all) := ∀ other ∈ domain,¬ Strict domain candidate other
def Safe (candidate : Candidate all) (remaining : List (Candidate all)) :=
  (∀ other ∈ remaining,¬ Strict domain candidate other) → Maximal domain candidate

private theorem discard {candidate other : Candidate all} {rest : List (Candidate all)}
    (safe : Safe domain candidate (other::rest)) (cleared : ¬ Strict domain candidate other) : Safe domain candidate rest := by
  intro later policy inside
  apply safe _ policy inside
  intro rival member
  rcases List.mem_cons.mp member with same | remaining
  · subst rival;exact cleared
  · exact later rival remaining

inductive Frame (candidate : Candidate all) where
  | rivals (remaining : List (Candidate all))
      (listed : ∀ other ∈ remaining,other ∈ domain) (safe : Safe domain candidate remaining)
  | forward (other : Candidate all) (listed : other ∈ domain) (rest : List (Candidate all))
      (rest_listed : ∀ rival ∈ rest,rival ∈ domain) (safe : Safe domain candidate (other::rest))
      (todo : List (Axis all)) (within : ∀ probe ∈ todo,probe ∈ (axes all))
      (passed : Passed domain other candidate todo → Distributed.NoWorse (axes all) cost other candidate)
  | reverse (other : Candidate all) (listed : other ∈ domain) (rest : List (Candidate all))
      (rest_listed : ∀ rival ∈ rest,rival ∈ domain) (safe : Safe domain candidate (other::rest))
      (forward : Distributed.NoWorse (axes all) cost other candidate)
      (todo : List (Axis all)) (within : ∀ probe ∈ todo,probe ∈ (axes all))
      (passed : Passed domain candidate other todo → Distributed.NoWorse (axes all) cost candidate other)
  | verified (maximal : Maximal domain candidate)
  | dominated (other : Candidate all) (listed : other ∈ domain) (strict : Strict domain candidate other)

def initial (candidate : Candidate all) : Frame domain candidate := .rivals domain (fun _ member => member) (fun domain => domain)
inductive Control where | enter | forwardComplete | reverseComplete | complete
inductive Event where
  | control (operation : Control)
  | yes (left right : Candidate all) (probe : Axis all) (valid : Holds domain left right probe)
  | no (left right : Candidate all) (probe : Axis all) (invalid : ¬ Holds domain left right probe)

private theorem pass_cons {left right : Candidate all} {head : Axis all} {tail : List (Axis all)}
    (head_passed : Holds domain left right head) (later : Passed domain left right tail) : Passed domain left right (head::tail) := by
  intro probe member
  rcases List.mem_cons.mp member with same | inside
  · subst probe;exact head_passed
  · exact later probe inside

private theorem failed_probe {left right : Candidate all} {probe : Axis all}
    (inside : probe ∈ (axes all)) (failed : ¬ Holds domain left right probe) : ¬ Distributed.NoWorse (axes all) cost left right :=
  fun complete => failed ((all_probes_are_the_original_benefit domain left right).mpr complete probe inside)

def advance {candidate : Candidate all} : Frame domain candidate → Option (Frame domain candidate × Event domain)
  | .verified _ | .dominated .. => none
  | .rivals [] _ safe => some (.verified (safe (by intro other inside;cases inside)),.control .complete)
  | .rivals (other::rest) listed safe => some
      (.forward other (listed other List.mem_cons_self) rest
        (fun rival member => listed rival (List.mem_cons_of_mem _ member)) safe
        (axes all) (fun _ member => member) ((all_probes_are_the_original_benefit domain other candidate).mp),.control .enter)
  | .forward other listed rest rest_listed safe [] _ passed => some
      (.reverse other listed rest rest_listed safe (passed (by intro probe inside;cases inside))
        (axes all) (fun _ member => member) ((all_probes_are_the_original_benefit domain candidate other).mp),.control .forwardComplete)
  | .forward other listed rest rest_listed safe (head::tail) within passed =>
      if valid : Holds domain other candidate head then some
        (.forward other listed rest rest_listed safe tail
          (fun probe member => within probe (List.mem_cons_of_mem _ member))
          (fun later => passed (pass_cons domain valid later)),.yes other candidate head valid)
      else some (.rivals rest rest_listed (discard domain safe (fun strict =>
        failed_probe domain (within head List.mem_cons_self) valid strict.1)),.no other candidate head valid)
  | .reverse other _ rest rest_listed safe forward [] _ passed => some
      (.rivals rest rest_listed (discard domain safe (fun strict => strict.2 (passed (by intro probe inside;cases inside)))),.control .reverseComplete)
  | .reverse other listed rest rest_listed safe forward (head::tail) within passed =>
      if valid : Holds domain candidate other head then some
        (.reverse other listed rest rest_listed safe forward tail
          (fun probe member => within probe (List.mem_cons_of_mem _ member))
          (fun later => passed (pass_cons domain valid later)),.yes candidate other head valid)
      else some (.dominated other listed ⟨forward,failed_probe domain (within head List.mem_cons_self) valid⟩,
        .no candidate other head valid)

def Frame.finished {candidate : Candidate all} : Frame domain candidate → Bool
  | .verified _ | .dominated .. => true
  | _ => false

def Frame.rank {candidate : Candidate all} : Frame domain candidate → Nat
  | .rivals remaining .. => 1+remaining.length*(2*(axes all).length+3)
  | .forward _ _ rest _ _ todo .. => rest.length*(2*(axes all).length+3)+todo.length+(axes all).length+3
  | .reverse _ _ rest _ _ _ todo .. => rest.length*(2*(axes all).length+3)+todo.length+2
  | .verified _ | .dominated .. => 0

theorem unfinished_has_an_actual_next {candidate : Candidate all} (before : Frame domain candidate) :
    advance domain before = none ↔ before.finished domain = true := by
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

theorem each_actual_step_decreases_the_source_rank {candidate : Candidate all} {before after : Frame domain candidate}
    {event : Event domain} (step : advance domain before = some (after,event)) : after.rank domain < before.rank domain := by
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

inductive Trace {candidate : Candidate all} : Frame domain candidate → Frame domain candidate → List (Event domain) → Prop
  | nil (before) : Trace before before []
  | step {before middle after event work} (observed : advance domain before = some (middle,event))
      (later : Trace middle after work) : Trace before after (event::work)

structure Run {candidate : Candidate all} (before : Frame domain candidate) (capacity : Nat) where
  private mk ::
  endpoint : Frame domain candidate
  work : List (Event domain)
  trace : Trace domain before endpoint work
  fits : work.length ≤ capacity

def execute {candidate : Candidate all} : (capacity : Nat) → (before : Frame domain candidate) → Run domain before capacity
  | 0,before => ⟨before,[],.nil before,by rfl⟩
  | capacity+1,before => match step : advance domain before with
    | none => ⟨before,[],.nil before,Nat.zero_le _⟩
    | some (after,event) =>
        let later := execute capacity after
        ⟨later.endpoint,event::later.work,.step step later.trace,by have := later.fits;simpa only [List.length_cons] using Nat.succ_le_succ this⟩

theorem zero_credit_does_not_evaluate_any_probe {candidate : Candidate all} (before : Frame domain candidate) :
    (execute domain 0 before).endpoint = before ∧ (execute domain 0 before).work = [] := ⟨rfl,rfl⟩

theorem source_rank_capacity_completes {candidate : Candidate all} (capacity : Nat) (before : Frame domain candidate)
    (enough : before.rank domain ≤ capacity) : (execute domain capacity before).endpoint.finished domain = true := by
  induction capacity generalizing before with
  | zero =>
    cases before <;> simp_all [Frame.rank,Frame.finished,execute]
  | succ capacity ih =>
    unfold execute
    split
    · rename_i stopped
      exact (unfinished_has_an_actual_next domain before).mp stopped
    · rename_i after event step
      exact ih after (by have smaller := each_actual_step_decreases_the_source_rank domain step;omega)

abbrev Owned := {candidate : Candidate all // candidate ∈ domain}
def offer (policy : Owned domain) := policy.val
def policies := domain.attach
def Rejected (policy : Owned domain) := ∃ other ∈ domain,Strict domain (offer domain policy) other
def Cleared (remaining : List (Owned domain)) := (∀ policy ∈ remaining,Rejected domain policy) → ∀ policy ∈ policies domain,Rejected domain policy
private theorem reject_head {head : Owned domain} {tail : List (Owned domain)}
    (safe : Cleared domain (head::tail)) (broken : Rejected domain head) : Cleared domain tail := by
  intro later
  apply safe
  intro policy member
  rcases List.mem_cons.mp member with same | inside
  · subst policy;exact broken
  · exact later policy inside

inductive Search where
  | candidates (remaining : List (Owned domain)) (safe : Cleared domain remaining)
  | checking (policy : Owned domain) (rest : List (Owned domain)) (safe : Cleared domain (policy::rest))
      (frame : Frame domain (offer domain policy))
  | released (policy : Owned domain) (maximal : Maximal domain (offer domain policy))
  | excluded (rejected : ∀ policy ∈ policies domain,Rejected domain policy)

def start : Search domain := .candidates (policies domain) (fun all => all)
inductive Action where
  | load | release | discard | empty
  | native (event : Event domain)

def move : Search domain → Option (Search domain × Action (domain := domain))
  | .released .. | .excluded _ => none
  | .candidates [] safe => some (.excluded (safe (by intro policy inside;cases inside)),.empty)
  | .candidates (head::tail) safe => some (.checking head tail safe (initial domain (offer domain head)),.load)
  | .checking policy rest safe frame => match looked : advance domain frame with
    | some (after,event) => some (.checking policy rest safe after,.native event)
    | none => match frame with
      | .verified maximal => some (.released policy maximal,.release)
      | .dominated other listed strict => some (.candidates rest (reject_head domain safe ⟨other,listed,strict⟩),.discard)
      | .rivals .. | .forward .. | .reverse .. => False.elim (by
          have impossible := (unfinished_has_an_actual_next domain _).mp looked
          cases impossible)

def Search.finished : Search domain → Bool
  | .released .. | .excluded _ => true
  | _ => false

def innerBound := 1+domain.length*(2*(axes all).length+3)
def Search.rank : Search domain → Nat
  | .candidates remaining _ => 1+remaining.length*(innerBound (domain := domain)+2)
  | .checking _ rest _ frame => rest.length*(innerBound (domain := domain)+2)+frame.rank domain+2
  | .released .. | .excluded _ => 0

theorem each_search_step_decreases_the_source_rank {before after : Search domain} {action : Action (domain := domain)}
    (step : move domain before = some (after,action)) : after.rank domain < before.rank domain := by
  cases before with
  | released | excluded => cases step
  | candidates remaining safe =>
    cases remaining <;> dsimp only [move] at step
    all_goals cases Option.some.inj step
    all_goals (simp only [Search.rank,initial,Frame.rank,innerBound,List.length_cons,List.length_nil,Nat.add_mul,Nat.one_mul]; omega)
  | checking policy rest safe frame =>
    dsimp only [move] at step
    split at step
    · rename_i after event observed
      cases Option.some.inj step
      have smaller := each_actual_step_decreases_the_source_rank domain observed
      simp only [Search.rank];omega
    · rename_i stopped
      cases frame with
      | verified | dominated =>
        dsimp only at step;cases Option.some.inj step
        simp only [Search.rank,Frame.rank];omega
      | rivals | forward | reverse =>
        have impossible := (unfinished_has_an_actual_next domain _).mp stopped
        cases impossible

inductive History : Search domain → Search domain → List (Action (domain := domain)) → Prop
  | nil (before) : History before before []
  | step {before middle after action work} (observed : move domain before = some (middle,action))
      (later : History middle after work) : History before after (action::work)

structure SearchRun (before : Search domain) (capacity : Nat) where
  private mk ::
  endpoint : Search domain
  work : List (Action (domain := domain))
  history : History domain before endpoint work
  fits : work.length ≤ capacity

def run : (capacity : Nat) → (before : Search domain) → SearchRun domain before capacity
  | 0,before => ⟨before,[],.nil before,by rfl⟩
  | capacity+1,before => match step : move domain before with
    | none => ⟨before,[],.nil before,Nat.zero_le _⟩
    | some (after,action) =>
      let later := run capacity after
      ⟨later.endpoint,action::later.work,.step step later.history,by
        have := later.fits;simpa only [List.length_cons] using Nat.succ_le_succ this⟩

theorem zero_credit_preserves_the_unread_search (before : Search domain) :
    (run domain 0 before).endpoint = before ∧ (run domain 0 before).work = [] := ⟨rfl,rfl⟩

theorem move_none_iff_finished (before : Search domain) : move domain before = none ↔ before.finished domain = true := by
  cases before with
  | released | excluded => simp [move,Search.finished]
  | candidates remaining safe => cases remaining <;> simp [move,Search.finished]
  | checking policy rest safe frame =>
    dsimp only [move,Search.finished]
    split
    · simp
    · rename_i stopped
      cases frame with
      | verified | dominated => simp
      | rivals | forward | reverse =>
        have impossible := (unfinished_has_an_actual_next domain _).mp stopped
        cases impossible

theorem source_rank_completes_the_entire_domain_search (capacity : Nat) (before : Search domain)
    (enough : before.rank domain ≤ capacity) : (run domain capacity before).endpoint.finished domain = true := by
  induction capacity generalizing before with
  | zero => cases before <;> simp_all [Search.rank,Search.finished,run]
  | succ capacity ih =>
    unfold run
    split
    · rename_i stopped;exact (move_none_iff_finished domain before).mp stopped
    · rename_i after action observed
      exact ih after (by have smaller := each_search_step_decreases_the_source_rank domain observed;omega)


def Search.selection : Search domain → Option (Distributed.Selected (axes all) cost domain)
  | .released policy maximal => some ⟨policy.val,policy.property,maximal⟩
  | _ => none

theorem Search.excluded_means_empty (rejected : ∀ policy ∈ policies domain,Rejected domain policy) : domain = [] := by
  cases found : Distributed.choose (axes all) cost domain with
  | none => exact (Distributed.choose_none_iff_empty _ _ _).mp found
  | some chosen =>
      obtain ⟨other,inside,strict⟩ := rejected ⟨chosen.policy,chosen.original⟩ (List.mem_attach _ _)
      exact False.elim (chosen.maximal other inside strict)
end Scanner


variable (items : List (Report all))
def accepted (rows : List (Row all)) := rows.filterMap fun row => row.2.accept?

inductive State where
  | reading (remaining : List (Report all)) (cached : List (Row all))
      (conserved : cached ++ directory remaining = directory items)
      (pool : List (Candidate all)) (pooled : pool = accepted cached)
  | searching (cached : List (Row all)) (complete : cached = directory items)
      (pool : List (Candidate all)) (pooled : pool = candidates items) (current : Scanner.Search pool)

def initial : State items := .reading items [] rfl [] rfl

inductive Event where
  | inspected (report : Report all) (entry : Entry report) (generated : entry = inspect report)
  | begin
  | search (pool : List (Candidate all)) (event : Scanner.Action (domain := pool))

def move : State items → Option (State items × Event (all := all))
  | .reading [] cached conserved pool pooled =>
      let complete : cached = directory items := by simpa only [directory,List.map_nil,List.append_nil] using conserved
      let exact : pool = candidates items := by rw [pooled,complete];rfl
      some (.searching cached complete pool exact (Scanner.start pool),.begin)
  | .reading (report::rest) cached conserved pool pooled =>
      let row : Row all := ⟨report,inspect report⟩
      some (.reading rest (cached++[row]) (by
          rw [List.append_assoc]
          exact conserved)
        (pool++row.2.accept?.toList) (by
          rw [pooled]
          simp only [accepted,List.filterMap_append,List.filterMap_cons,List.filterMap_nil]
          cases row.2.accept? <;> rfl),.inspected report row.2 rfl)
  | .searching cached complete pool pooled current =>
      match observed : Scanner.move pool current with
      | none => none
      | some (after,event) => some (.searching cached complete pool pooled after,.search pool event)

def State.finished : State items → Bool
  | .reading .. => false
  | .searching _ _ pool _ current => current.finished pool

def ceiling := 1+items.length*(1+items.length*(2*(axes all).length+3)+2)
def State.rank : State items → Nat
  | .reading remaining .. => remaining.length+ceiling items+1
  | .searching _ _ pool _ current => current.rank pool

theorem each_step_decreases_rank {before after : State items} {event : Event (all := all)}
    (actual : move items before = some (after,event)) : after.rank items < before.rank items := by
  cases before with
  | reading remaining cached conserved pool pooled =>
    cases remaining with
    | nil =>
      dsimp only [move] at actual
      cases Option.some.inj actual
      have bound : pool.length ≤ items.length := by
        rw [pooled]
        have small := List.length_filterMap_le (fun row : Row all => row.2.accept?) cached
        have lengths := congrArg List.length conserved
        simp only [List.length_append,directory,List.length_map,List.length_nil,Nat.add_zero] at lengths
        simpa only [accepted,directory,List.length_append,List.length_map,List.length_nil,Nat.add_zero] using small.trans (by omega : cached.length ≤ items.length)
      simp only [State.rank,Scanner.start,Scanner.Search.rank,Scanner.policies,List.length_attach,Scanner.innerBound,ceiling,List.length_nil]
      have a := Nat.mul_le_mul_right (2*(axes all).length+3) bound
      have b := Nat.mul_le_mul bound (Nat.add_le_add_right (Nat.add_le_add_left a 1) 2)
      omega
    | cons report rest =>
      dsimp only [move] at actual
      cases Option.some.inj actual
      simp only [State.rank,List.length_cons]
      omega
  | searching cached complete pool pooled current =>
    dsimp only [move] at actual
    split at actual
    · cases actual
    · rename_i after event observed
      cases Option.some.inj actual
      exact Scanner.each_search_step_decreases_the_source_rank pool observed

theorem stopped_iff_finished (before : State items) : move items before = none ↔ before.finished items = true := by
  cases before with
  | reading remaining cached conserved pool pooled => cases remaining <;> simp [move,State.finished]
  | searching cached complete pool pooled current =>
    dsimp only [move,State.finished]
    split
    · rename_i stopped
      simp only [true_iff]
      exact (Scanner.move_none_iff_finished pool current).mp stopped
    · rename_i after event observed
      simp only [reduceCtorEq,false_iff]
      intro finished
      have stopped := (Scanner.move_none_iff_finished pool current).mpr finished
      rw [stopped] at observed
      cases observed

inductive LedgerTrace (items : List (Report all)) : State items → State items → List (Event (all := all)) → Prop
  | nil (before) : LedgerTrace items before before []
  | step {before middle after event work} (actual : move items before = some (middle,event))
      (later : LedgerTrace items middle after work) : LedgerTrace items before after (event::work)

structure Computation (items : List (Report all)) (before : State items) (capacity : Nat) where
  private mk ::
  endpoint : State items
  work : List (Event (all := all))
  history : LedgerTrace items before endpoint work
  fits : work.length ≤ capacity

def execute : (capacity : Nat) → (before : State items) → Computation items before capacity
  | 0,before => ⟨before,[],.nil before,by rfl⟩
  | capacity+1,before => match actual : move items before with
    | none => ⟨before,[],.nil before,Nat.zero_le _⟩
    | some (after,event) =>
        let later := execute capacity after
        ⟨later.endpoint,event::later.work,.step actual later.history,by have := later.fits;simpa only [List.length_cons] using Nat.succ_le_succ this⟩

theorem zero_capacity_does_not_read_a_report (before : State items) :
    (execute items 0 before).endpoint = before ∧ (execute items 0 before).work = [] := ⟨rfl,rfl⟩

theorem source_rank_completes (capacity : Nat) (before : State items) (enough : before.rank items ≤ capacity) :
    (execute items capacity before).endpoint.finished items = true := by
  induction capacity generalizing before with
  | zero =>
    cases before with
    | reading => simp only [State.rank] at enough;omega
    | searching cached complete pool pooled current =>
      exact Scanner.source_rank_completes_the_entire_domain_search pool 0 current enough
  | succ capacity ih =>
    unfold execute
    split
    · rename_i stopped;exact (stopped_iff_finished items before).mp stopped
    · rename_i after event actual
      exact ih after (by have smaller := each_step_decreases_rank items actual;omega)

theorem unfinished_uses_the_entire_allowance (capacity : Nat) (before : State items)
    (unfinished : (execute items capacity before).endpoint.finished items = false) :
    (execute items capacity before).work.length = capacity := by
  induction capacity generalizing before with
  | zero => rfl
  | succ capacity ih =>
    unfold execute at unfinished ⊢
    split at unfinished
    · rename_i stopped
      have finished := (stopped_iff_finished items before).mp stopped
      rw [finished] at unfinished
      cases unfinished
    · rename_i after event actual
      exact congrArg Nat.succ (ih after unfinished)

def State.selection : State items → Option (Selected items)
  | .reading .. => none
  | .searching _ _ pool pooled current => match current.selection pool with
    | none => none
    | some chosen => some ⟨chosen.policy,(by rw [←pooled];exact chosen.original),by
        intro other inside strict
        exact chosen.maximal other (by rw [pooled];exact inside) strict⟩

def State.entries : State items → List (Row all)
  | .reading _ cached .. | .searching cached .. => cached

theorem finished_keeps_the_full_directory (state : State items) (finished : state.finished items = true) : state.entries items = directory items := by
  cases state with
  | reading => cases finished
  | searching cached complete => exact complete

theorem completed_without_selection_means_empty (state : State items)
    (finished : state.finished items = true) (empty : state.selection items = none) : candidates items = [] := by
  cases state with
  | reading => cases finished
  | searching cached complete pool pooled current =>
    cases current with
    | candidates | checking => cases finished
    | released => cases empty
    | excluded rejected => rw [←pooled];exact Scanner.Search.excluded_means_empty pool rejected

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Machine
