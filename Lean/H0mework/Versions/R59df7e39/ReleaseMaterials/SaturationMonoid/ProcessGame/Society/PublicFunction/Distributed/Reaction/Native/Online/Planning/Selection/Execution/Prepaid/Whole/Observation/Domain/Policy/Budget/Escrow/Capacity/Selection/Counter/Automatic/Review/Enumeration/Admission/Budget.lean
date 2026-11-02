import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Termination
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Admission.Budget
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {source : SourceQuota.Generated prepared}
  {catalogue : SourceQuota.Catalogue source.snapshot} {all : Candidates source catalogue} (owner : Ready all)
abbrev Term := Section owner.release.programme.actual.pool
abbrev Row := PublicPolicy.Row owner.release.programme.actual.pool
def sourceUnits := owner.release.value
def query (term : Term owner) (row : Row owner) : Work.Query owner.release.programme.actual.pool := .admission term row
def initial (term : Term owner) (row : Row owner) : Counter.Frame owner.release.programme.actual.pool :=
  .program [] [.expression (.source (.selection (query owner term row)))]

private theorem below_ceiling {α : Type} (budget : α → Nat) (items : List α) (item : α) (inside : item ∈ items) :
    budget item ≤ Policy.Work.ceiling budget items := by
  induction items with
  | nil => simp at inside
  | cons head tail ih =>
    rcases List.mem_cons.mp inside with same | later
    · subst item;exact Nat.le_max_left _ _
    · exact (ih later).trans (Nat.le_max_right _ _)

theorem atom_budget_strictly_below_the_original_source (term : Term owner) (row : Row owner) (inside : row ∈ PublicPolicy.rows owner.release.programme.actual.pool) :
    Work.atomBudget owner.release.programme.actual.pool (query owner term row) < sourceUnits owner := by
  let pool := owner.release.programme.actual.pool
  have member : query owner term row ∈ Work.queries pool :=
    List.mem_append_left _ (List.mem_flatMap.mpr ⟨term,every_section_is_generated pool term,List.mem_map.mpr ⟨row,inside,rfl⟩⟩)
  have bounded := below_ceiling (Work.atomBudget pool) (Work.queries pool) _ member
  change _ ≤ Work.atomCeiling pool at bounded
  have positiveRows : 0 < (PublicPolicy.rows pool).length := by simp [PublicPolicy.rows]
  have positiveTerms : 0 < (sections pool).length := List.length_pos_of_mem (every_section_is_generated pool term)
  have a : Work.atomCeiling pool < Work.admissionWorkBudget pool := by unfold Work.admissionWorkBudget;nlinarith
  have b : Work.admissionWorkBudget pool ≤ Work.workBudget pool := by unfold Work.workBudget;nlinarith
  dsimp only [sourceUnits]
  rw [owner.release.correct]
  change _ ≤ Body.units pool+Work.workBudget pool
  exact (bounded.trans_lt (a.trans_le b)).trans_le (Nat.le_add_left _ _)

theorem atom_budget_fits_the_original_source (term : Term owner) (row : Row owner) (inside : row ∈ PublicPolicy.rows owner.release.programme.actual.pool) :
    Work.atomBudget owner.release.programme.actual.pool (query owner term row) ≤ sourceUnits owner :=
  (atom_budget_strictly_below_the_original_source owner term row inside).le

variable {owner}
inductive History (owner : Ready all) (term : Term owner) (row : Row owner) : Counter.Frame owner.release.programme.actual.pool →
    List (Counter.Event owner.release.programme.actual.pool) → Prop where
  | start : History owner term row (initial owner term row) []
  | next {before work} (past : History owner term row before work)
      (update : Counter.Update owner.release.programme.actual.pool before)
      (actual : Counter.advance owner.release.programme.actual.pool before = .updated update) :
      History owner term row update.after (work++[update.event])

theorem History.meaning {owner : Ready all} {term : Term owner} {row : Row owner} {current work}
    (history : History owner term row current work) :
    current.meaning owner.release.programme.actual.pool = some [Work.atomBudget owner.release.programme.actual.pool (query owner term row)] := by
  induction history with
  | start => rfl
  | next past update actual ih => exact update.preserved.symm.trans ih

structure Cursor (owner : Ready all) (term : Term owner) (row : Row owner) where
  private mk ::
  current : Counter.Frame owner.release.programme.actual.pool
  work : List (Counter.Event owner.release.programme.actual.pool)
  history : History owner term row current work
def start (owner : Ready all) (term : Term owner) (row : Row owner) : Cursor owner term row := ⟨initial owner term row,[],.start⟩

structure Advance {owner : Ready all} {term : Term owner} {row : Row owner} (before : Cursor owner term row) where
  private mk ::
  update : Counter.Update owner.release.programme.actual.pool before.current
  actual : Counter.advance owner.release.programme.actual.pool before.current = .updated update
  after : Cursor owner term row
  current_exact : after.current = update.after
  work_exact : after.work = before.work++[update.event]
def advance {owner : Ready all} {term : Term owner} {row : Row owner} (before : Cursor owner term row) : Advance before :=
  match actual : Counter.advance owner.release.programme.actual.pool before.current with
  | .invalid broken => False.elim (by rw [before.history.meaning] at broken;cases broken)
  | .updated update => ⟨update,actual,⟨update.after,before.work++[update.event],.next before.history update actual⟩,rfl,rfl⟩

inductive Origin {owner : Ready all} {term : Term owner} {row : Row owner} (cursor : Cursor owner term row) (amount : Nat) : Prop where
  | completed (same : cursor.current = .program [amount] []) : Origin cursor amount
  | exhausted (same : amount = sourceUnits owner) (spent : cursor.work.length = sourceUnits owner) : Origin cursor amount
structure Quote (owner : Ready all) (term : Term owner) (row : Row owner) where
  private mk ::
  cursor : Cursor owner term row
  amount : Nat
  origin : Origin cursor amount
  covered : (Work.atom owner.release.programme.actual.pool (query owner term row)).work.length ≤ amount
  bounded : amount ≤ sourceUnits owner

private def completed {owner : Ready all} {term : Term owner} {row : Row owner} (cursor : Cursor owner term row)
    (inside : row ∈ PublicPolicy.rows owner.release.programme.actual.pool) (stack : List Nat)
    (same : cursor.current = .program stack []) : Quote owner term row :=
  let exactStack : stack = [Work.atomBudget owner.release.programme.actual.pool (query owner term row)] := by
    have semantics := cursor.history.meaning
    rw [same] at semantics
    exact Option.some.inj semantics
  let amount := stack.headD 0
  let correct : amount = Work.atomBudget owner.release.programme.actual.pool (query owner term row) := by dsimp only [amount];rw [exactStack];rfl
  ⟨cursor,amount,.completed (by rw [same,exactStack,correct]),by rw [correct];exact Work.atom_work_bound _ _,
    by rw [correct];exact atom_budget_fits_the_original_source owner term row inside⟩

def quote? {owner : Ready all} {term : Term owner} {row : Row owner} (cursor : Cursor owner term row)
    (inside : row ∈ PublicPolicy.rows owner.release.programme.actual.pool) : Option (Quote owner term row) :=
  match same : cursor.current with
  | .program stack [] => some (completed cursor inside stack same)
  | _ => none

def retain {owner : Ready all} {term : Term owner} {row : Row owner} (cursor : Cursor owner term row)
    (inside : row ∈ PublicPolicy.rows owner.release.programme.actual.pool) (spent : cursor.work.length = sourceUnits owner) : Quote owner term row :=
  ⟨cursor,sourceUnits owner,.exhausted rfl spent,
    (Work.atom_work_bound _ _).trans (atom_budget_fits_the_original_source owner term row inside),Nat.le_refl _⟩

theorem completed_quote_reads_the_actual_cached_value {owner : Ready all} {term : Term owner} {row : Row owner}
    (quote : Quote owner term row) (same : quote.cursor.current = .program [quote.amount] []) :
    quote.amount = Work.atomBudget owner.release.programme.actual.pool (query owner term row) := by
  have semantics := quote.cursor.history.meaning
  rw [same] at semantics
  simpa only [Counter.Frame.meaning,Counter.pure,Option.some.injEq,List.cons.injEq,and_true] using semantics

variable (owner : Ready all)
/-- Used by the progress proof, never by the admission runner. -/
def quotationCeiling := Policy.Work.ceiling
  (fun query : Work.Query owner.release.programme.actual.pool => Counter.Termination.rank _
    (.program [] [.expression (.source (.selection query))])) (Work.queries owner.release.programme.actual.pool)

theorem initial_rank_is_covered (term : Term owner) (row : Row owner) (inside : row ∈ PublicPolicy.rows owner.release.programme.actual.pool) :
    Counter.Termination.rank _ (initial owner term row) ≤ quotationCeiling owner := by
  have member : query owner term row ∈ Work.queries owner.release.programme.actual.pool :=
    List.mem_append_left _ (List.mem_flatMap.mpr ⟨term,every_section_is_generated _ term,List.mem_map.mpr ⟨row,inside,rfl⟩⟩)
  simpa only [initial,quotationCeiling] using
    (below_ceiling (fun query : Work.Query owner.release.programme.actual.pool => Counter.Termination.rank _
      (.program [] [.expression (.source (.selection query))])) _ _ member)

variable {owner}
theorem quote_pending_is_unfinished {term : Term owner} {row : Row owner} (cursor : Cursor owner term row)
    (inside : row ∈ PublicPolicy.rows owner.release.programme.actual.pool) (missing : quote? cursor inside = none) :
    Counter.Termination.finished _ cursor.current = false := by
  unfold quote? at missing
  split at missing
  · cases missing
  · rename_i unfinished
    cases current : cursor.current with
    | program stack tasks =>
      cases tasks with
      | nil => exact False.elim (unfinished stack current)
      | cons => rfl
    | arithmetic => rfl

theorem every_pending_source_advance_progresses {term : Term owner} {row : Row owner} (cursor : Cursor owner term row)
    (inside : row ∈ PublicPolicy.rows owner.release.programme.actual.pool) (missing : quote? cursor inside = none) :
    Counter.Termination.rank _ (advance cursor).after.current < Counter.Termination.rank _ cursor.current := by
  rw [(advance cursor).current_exact]
  exact Counter.Termination.each_original_update_progresses _ (advance cursor).update
    (quote_pending_is_unfinished cursor inside missing) (advance cursor).actual

theorem Cursor.finite_source_completion {term : Term owner} {row : Row owner} (cursor : Cursor owner term row) :
    ∃ fuel,(Counter.execute _ fuel cursor.current).endpoint =
      .program [Work.atomBudget owner.release.programme.actual.pool (query owner term row)] [] := by
  let pool := owner.release.programme.actual.pool
  let fuel := Counter.Termination.rank pool cursor.current
  have valid : cursor.current.meaning pool ≠ none := by rw [cursor.history.meaning];intro impossible;cases impossible
  have completed := Counter.Termination.source_rank_finishes_the_original_run pool fuel cursor.current valid (Nat.le_refl _)
  obtain ⟨stack,same⟩ := Counter.Termination.finished_has_a_cached_stack pool _ completed
  have value := (Counter.execute pool fuel cursor.current).meaning_preserved
  rw [cursor.history.meaning,same] at value
  have exactStack : stack = [Work.atomBudget pool (query owner term row)] := (Option.some.inj value).symm
  exact ⟨fuel,by rw [same,exactStack]⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Admission.Budget
