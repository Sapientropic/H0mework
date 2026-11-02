import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Joint.Responsibility.Canonical.Payment.Runtime
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input}


variable {source : SourceQuota.Generated prepared} {catalogue : SourceQuota.Catalogue source.snapshot}
  {all : Candidates source catalogue}
abbrev Report (all : Candidates source catalogue) := Sigma fun owner : Ready all => Generated owner

structure Candidate (all : Candidates source catalogue) where
  private mk ::
  report : Report all
  policy : Choice all
  completed : report.2.completed = some policy
  first : Responsibility.First report.2
  born : Responsibility.first? report.2 = some first
  paid : (index : Index prepared) → Responsibility.Canonical.Payment.Built report.2 index first
  generated : ∀ index,Responsibility.Canonical.Payment.produce report.2 index first = .ready (paid index)

def isReady {owner : Ready all} {made : Generated owner} {index : Index prepared} {first : Responsibility.First made} :
    Responsibility.Canonical.Payment.Result made index first → Prop
  | .ready _ => True
  | .shortfall .. => False
instance {owner : Ready all} {made : Generated owner} {index : Index prepared} {first : Responsibility.First made}
    (result : Responsibility.Canonical.Payment.Result made index first) : Decidable (isReady result) := by
  cases result <;> dsimp only [isReady] <;> infer_instance

def readReady {owner : Ready all} {made : Generated owner} {index : Index prepared} {first : Responsibility.First made}
    (result : Responsibility.Canonical.Payment.Result made index first) (valid : isReady result) :
    Responsibility.Canonical.Payment.Built made index first :=
  match result with
  | .ready paid => paid
  | .shortfall .. => False.elim valid

theorem readReady_generated {owner : Ready all} {made : Generated owner} {index : Index prepared} {first : Responsibility.First made}
    (result : Responsibility.Canonical.Payment.Result made index first) (valid : isReady result) :
    result = .ready (readReady result valid) := by cases result <;> first | rfl | contradiction

inductive Entry (report : Report all) where
  | unfinished (absent : report.2.completed = none)
  | empty (policy : Choice all) (completed : report.2.completed = some policy) (absent : Responsibility.first? report.2 = none)
  | shortfall (policy : Choice all) (completed : report.2.completed = some policy)
      (first : Responsibility.First report.2) (born : Responsibility.first? report.2 = some first)
      (index : Index prepared) (construction : Responsibility.Canonical.Payment.Cursor report.2 index first)
      (actual : construction = Responsibility.Canonical.Payment.execute report.2 index first)
      (absent : construction.output = none) (short : report.2.unused < Responsibility.Canonical.Payment.units report.2 index)
  | ready (candidate : Candidate all) (same : candidate.report = report)

def inspect (report : Report all) : Entry report :=
  match completed : report.2.completed with
  | none => .unfinished completed
  | some policy => match born : Responsibility.first? report.2 with
    | none => .empty policy completed born
    | some first =>
      let construction := fun index : Index prepared => Responsibility.Canonical.Payment.produce report.2 index first
      match Distributed.inspect (fun index => isReady (construction index)) (keys prepared) with
      | .accepted every =>
          let admitted := fun index => every index (List.mem_finRange index)
          .ready ⟨report,policy,completed,first,born,(fun index => readReady (construction index) (admitted index)),
            (fun index => readReady_generated (construction index) (admitted index))⟩ rfl
      | .rejected index _ broken =>
          match actual : construction index with
          | .ready paid => False.elim (broken (by rw [actual];trivial))
          | .shortfall cursor generated absent short => .shortfall policy completed first born index cursor generated absent short

def Entry.accept? {report : Report all} : Entry report → Option (Candidate all)
  | .ready candidate _ => some candidate
  | _ => none

abbrev Row (all : Candidates source catalogue) := Sigma fun report : Report all => Entry report

def directory (items : List (Report all)) : List (Row all) := items.map fun report => ⟨report,inspect report⟩
def candidates (items : List (Report all)) : List (Candidate all) := (directory items).filterMap (fun row => row.2.accept?)

theorem every_original_report_is_in_the_directory (items : List (Report all)) (report : Report all) (inside : report ∈ items) :
    (⟨report,inspect report⟩ : Row all) ∈ directory items := List.mem_map.mpr ⟨report,inside,rfl⟩

theorem every_generated_candidate_has_an_original_report (items : List (Report all)) (candidate : Candidate all)
    (inside : candidate ∈ candidates items) : candidate.report ∈ items := by
  obtain ⟨row,listed,accepted⟩ := List.mem_filterMap.mp inside
  obtain ⟨report,original,same⟩ := List.mem_map.mp listed
  cases same
  change (inspect report).accept? = some candidate at accepted
  cases actual : inspect report with
  | unfinished | empty | shortfall => rw [actual] at accepted;cases accepted
  | ready found same =>
    rw [actual] at accepted
    have equal : found = candidate := Option.some.inj accepted
    rw [←equal,same]
    exact original

theorem every_ready_entry_is_in_the_pool (items : List (Report all)) (row : Row all) (listed : row ∈ directory items)
    (candidate : Candidate all) (accepted : row.2.accept? = some candidate) : candidate ∈ candidates items :=
  List.mem_filterMap.mpr ⟨row,listed,accepted⟩

theorem every_complete_funded_report_is_retained (items : List (Report all)) (report : Report all) (original : report ∈ items)
    (complete : report.2.completed.isSome = true) (positive : 0 < report.2.execution.work.length)
    (enough : ∀ index : Index prepared,Responsibility.Canonical.Payment.units report.2 index ≤ report.2.unused) :
    ∃ candidate ∈ candidates items,candidate.report = report := by
  cases actual : inspect report with
  | unfinished absent => rw [absent] at complete;cases complete
  | empty policy done absent =>
    obtain ⟨first,born,_⟩ := Responsibility.every_nonempty_paid_run_generates_its_first_write report.2 positive
    change Responsibility.first? report.2 = some first at born
    rw [absent] at born
    cases born
  | shortfall policy done first born index cursor generated absent short =>
    exact False.elim (Nat.not_lt_of_ge (enough index) short)
  | ready candidate same =>
    exact ⟨candidate,every_ready_entry_is_in_the_pool items ⟨report,inspect report⟩
      (every_original_report_is_in_the_directory items report original) candidate (by
        change (inspect report).accept? = some candidate
        rw [actual]
        rfl),same⟩

namespace Candidate
variable (candidate : Candidate all)
def work (index : Index prepared) := (candidate.paid index).construction.work.length
def credit (index : Index prepared) := candidate.report.2.unused-(candidate.paid index).construction.done

theorem work_is_the_actual_constructor (index : Index prepared) :
    candidate.work index = (Responsibility.Canonical.Payment.execute candidate.report.2 index candidate.first).work.length := by
  unfold work
  rw [(candidate.paid index).generated]

theorem every_index_has_an_actual_paid_patch (index : Index prepared) :
    (candidate.paid index).patch = Responsibility.Canonical.patch candidate.report.2 index candidate.first 0 :=
  (candidate.paid index).patch_exact
theorem endpoint_is_the_compared_policy (index : Index prepared) :
    candidate.report.2.endpoint index = (candidate.policy.policy.view index).endpoint := by
  have completed := candidate.completed
  dsimp only [Generated.completed] at completed
  split at completed
  · rename_i cached exact challengers challengersExact policy maximal actual
    have same := Option.some.inj completed
    rw [←same]
    dsimp only [Generated.endpoint]
    rw [actual]
    rfl
  · cases completed

end Candidate

structure Book (items : List (Report all)) where
  private mk ::
  entries : List (Row all)
  generated : entries = directory items

def generateBook (items : List (Report all)) : Book items := ⟨directory items,rfl⟩
def Book.pool {items : List (Report all)} (book : Book items) := book.entries.filterMap (fun row => row.2.accept?)
theorem Book.pool_exact {items : List (Report all)} (book : Book items) : book.pool = candidates items := by rw [Book.pool,book.generated];rfl

theorem Book.every_original_report_is_retained {items : List (Report all)} (book : Book items) (report : Report all) (inside : report ∈ items) :
    (⟨report,inspect report⟩ : Row all) ∈ book.entries := by rw [book.generated];exact every_original_report_is_in_the_directory items report inside

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting
