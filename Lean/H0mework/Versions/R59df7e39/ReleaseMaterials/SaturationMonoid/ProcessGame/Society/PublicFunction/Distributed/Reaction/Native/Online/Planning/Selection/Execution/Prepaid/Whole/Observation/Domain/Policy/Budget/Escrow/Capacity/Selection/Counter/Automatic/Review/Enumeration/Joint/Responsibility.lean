import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Joint.NativePayment
import H0mework.Realization.Audit.DebtFirstWrite

/-! The original paid Joint history generates one persistent computation
responsibility. Its first actual move generates the admission fragment;
later moves spend that same identity. The rank is a termination measure,
not money, energy, principal or a service-settlement receipt. Canonical
living-root installation of the born row is the downstream consumer. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open DebtActivationWorld DebtActivationLedger DebtAdmissionFirstWrite
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {source : SourceQuota.Generated prepared}
  {catalogue : SourceQuota.Catalogue source.snapshot} {all : Candidates source catalogue} {owner : Ready all}

private theorem execute_succ_endpoint {before middle : State owner} {action : Action owner}
    (observed : move owner before = some (middle,action)) (count : Nat) :
    (execute owner (count+1) before).endpoint = (execute owner count middle).endpoint := by
  unfold execute
  split
  · rename_i stopped
    rw [observed] at stopped
    cases stopped
  · rename_i after event actual
    cases Option.some.inj (observed.symm.trans actual)
    cases count <;> rfl

theorem History.actual_prefix_step {before after : State owner} {work : List (Action owner)}
    (history : History owner before after work) (event : Fin work.length) :
    move owner (execute owner event.val before).endpoint =
      some ((execute owner (event.val+1) before).endpoint,work[event]) := by
  induction history with
  | nil => exact Fin.elim0 event
  | @step before middle after action work observed later ih =>
      rcases event with ⟨position,bounded⟩
      cases position with
      | zero =>
          change move owner before = some ((execute owner (0+1) before).endpoint,action)
          rw [execute_succ_endpoint observed 0]
          exact observed
      | succ position =>
          have next := ih ⟨position,Nat.lt_of_succ_lt_succ bounded⟩
          rw [execute_succ_endpoint observed position,execute_succ_endpoint observed (position+1)]
          exact next

namespace Responsibility
variable (owner : Ready all)

def law : DebtActivationLaw where
  DebtState := State owner
  DebtId := Ready all
  DebtClaim := Ready all
  debtId := owner
  debtClaim := owner
  budget := State.rank owner
  StepAt := fun before after => Sigma fun event : Action owner =>
    PLift (move owner before = some (after,event))
  step_budget_lt := fun step => each_step_progresses owner step.2.down
  SettlementAt := fun _ => PEmpty
  settlement_budget_zero := fun impossible => impossible.elim
  ObstructionAt := fun _ => PEmpty

variable {owner} (made : Generated owner)

structure At where
  private mk ::
  ordinal : Fin made.execution.work.length

def entry (ordinal : Fin made.execution.work.length) : At made := ⟨ordinal⟩

namespace At
variable {made} (row : At made)
def before : State owner := (execute owner row.ordinal.val (initial owner)).endpoint
def after : State owner := (execute owner (row.ordinal.val+1) (initial owner)).endpoint
def action : Action owner := made.execution.work[row.ordinal]
theorem actual : move owner row.before = some (row.after,row.action) :=
  made.execution.history.actual_prefix_step row.ordinal

def transition : (law owner).StepAt row.before row.after := ⟨row.action,⟨row.actual⟩⟩
theorem strict : (law owner).budget row.after < (law owner).budget row.before :=
  (law owner).step_budget_lt row.transition

def slot (index : Index prepared) := made.slot index row.ordinal
theorem paid (index : Index prepared) :
    (made.allocation index row.ordinal).invoice.bill.payment.succeeded = true ∧
    (made.allocation index row.ordinal).operation = row.action :=
  ⟨(made.every_event_uses_the_same_successful_invoice index row.ordinal).1,rfl⟩
theorem slots_distinct (index : Index prepared) (other : At made)
    (same : row.slot index = other.slot index) : row = other := by
  have equal := made.slots_are_not_reused index same
  cases row;cases other;cases equal;rfl
theorem consecutive (next : At made) (adjacent : row.ordinal.val+1 = next.ordinal.val) :
    row.after = next.before := by
  dsimp only [after,before]
  rw [adjacent]
end At

/-- The entire old ledger belongs to the exact original endpoint source. -/
abbrev base (index : Index prepared) := ProgrammeSource.N (made.endpoint index).source.val.input
def support (index : Index prepared) : (base made index).Support :=
  ProgrammeSource.supportAt (made.endpoint index).source.val.input
    (ProgrammeHistory.visitAt (made.endpoint index).source.val.input (made.endpoint index).depth).current

def At.payment (row : At made) (index : Index prepared) :
    LedgerWriteEvolutionAt (ExtendedNetwork (base made index) (law owner))
      (activeLedger (support made index) row.before) (activeLedger (support made index) row.after) :=
  stepLedgerEvolution (support made index) row.transition

theorem At.every_inherited_row_is_preserved (row : At made) (index : Index prepared)
    (old : OpenResponsibilityAt (base made index) (support made index)) :
    ((At.payment made row index).destination (oldEntry (law := law owner) (state? := some row.before) old)).1 =
      oldEntry (law := law owner) (state? := some row.after) old := rfl

theorem At.persistent_debt_is_strictly_paid (row : At made) (index : Index prepared) :
    ((At.payment made row index).destination (debtEntry (law := law owner) (support made index) row.before)).1 =
      debtEntry (law := law owner) (support made index) row.after ∧
    (debtEntry (N := base made index) (law := law owner) (support made index) row.after).progressBudget <
      (debtEntry (N := base made index) (law := law owner) (support made index) row.before).progressBudget :=
  ⟨stepLedgerEvolution_destination_debt (support made index) row.transition,row.strict⟩

structure First : Type where
  private mk ::
  nonempty : 0 < made.execution.work.length

def first? : Option (First made) :=
  if nonempty : 0 < made.execution.work.length then some ⟨nonempty⟩ else none

namespace First
variable {made} (first : First made)
def row : At made := entry made ⟨0,first.nonempty⟩
theorem before_is_original_start : first.row.before = initial owner := rfl

def event : SourceFixedDebtAdmissionEventAt (law owner) (initial owner) :=
  ⟨first.row.after,first.row.transition⟩
noncomputable def write (index : Index prepared) :=
  DebtAdmissionFirstWrite.generate (N := base made index) (support made index) first.event

theorem original_paid_action (index : Index prepared) :
    (made.allocation index first.row.ordinal).invoice.bill.payment.succeeded = true ∧
    (made.allocation index first.row.ordinal).operation = made.execution.work[0]'first.nonempty :=
  first.row.paid index

theorem first_write_is_actual_strict_payment (index : Index prepared) :
    ((first.write index).firstPayment.destination (first.write index).initialEntry).1 =
      (first.write index).paidEntry ∧
    (first.write index).paidEntry.progressBudget < (first.write index).initialEntry.progressBudget :=
  ⟨(first.write index).firstPayment_destination_debt,(first.write index).firstPayment_budget_strict⟩

theorem no_settlement_or_terminal_is_created :
    IsEmpty ((law owner).SettlementAt first.row.after) ∧
    IsEmpty ((law owner).SupportTerminalAt first.row.after) := by
  constructor <;> exact ⟨fun impossible => nomatch impossible⟩
end First

/-- One optional birth and the complete original event inventory; callers
cannot supply a replacement inventory or a selected first-write witness. -/
structure Book where
  private mk ::
  birth : Option (First made)
  birth_exact : birth = first? made
  entries : List (At made)
  entries_exact : entries = (List.finRange made.execution.work.length).map (entry made)

def generate : Book made :=
  ⟨first? made,rfl,(List.finRange made.execution.work.length).map (entry made),rfl⟩

theorem every_actual_event_is_registered (event : Fin made.execution.work.length) :
    entry made event ∈ (generate made).entries :=
  List.mem_map.mpr ⟨event,List.mem_finRange _,rfl⟩

theorem entry_count_is_exact : (generate made).entries.length = made.execution.work.length := by
  simp only [generate,List.length_map,List.length_finRange]

theorem empty_work_has_no_birth (empty : made.execution.work = []) :
    (generate made).birth = none := by simp [generate,first?,empty]

theorem every_nonempty_paid_run_generates_its_first_write (nonempty : 0 < made.execution.work.length) :
    ∃ first,(generate made).birth = some first ∧ first.row.ordinal.val = 0 := by
  exact ⟨⟨nonempty⟩,by simp only [generate,first?,dif_pos nonempty],rfl⟩

end Responsibility
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint
