import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Mixed.AtomicDeficiency
import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Mixed.Residual

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Mixed

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction
open _root_.SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {TaskId : Type*} [DecidableEq TaskId]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))
local notation "Task" => PublicTaskSpec Party Good

structure Allocation (source : C) (script : Script) (atomic fragments : Finset TaskId) (task : TaskId → Task) where
  choice : WholeChoice source script atomic task
  receipt : (network source script fragments task choice.reserved).Certificate
  complete : (network source script fragments task choice.reserved).Complete receipt.allocation

abbrev FragmentCut {source : C} {script : Script} {atomic : Finset TaskId} {task : TaskId → Task}
    (fragments : Finset TaskId) (choice : WholeChoice source script atomic task) :=
  NamedCut (network source script fragments task choice.reserved)

inductive Decision (source : C) (script : Script) (atomic fragments : Finset TaskId) (task : TaskId → Task)
  | overlapping (id : TaskId) (whole : id ∈ atomic) (split : id ∈ fragments)
  | malformed (bad : ¬ OriginalDemands fragments task)
  | atomic (short : Clock.Window.Shared.Deficiency source atomic task script)
  | fragments (available : WholeChoice source script atomic task)
      (forEach : ∀ choice : WholeChoice source script atomic task, FragmentCut fragments choice)
  | nativeBlocked (allocation : Allocation source script atomic fragments task) (issue : Obstruction source script)
  | paid (disjoint : Disjoint atomic fragments) (original : OriginalDemands fragments task)
      (allocation : Allocation source script atomic fragments task) (settled : Settled source script)

private def decideDisjoint (source : C) (script : Script) (task : TaskId → Task)
    (atomic fragments : List TaskId) (disjoint : Disjoint atomic.toFinset fragments.toFinset) :
    Decision source script atomic.toFinset fragments.toFinset task :=
  if original : OriginalDemands fragments.toFinset task then
    let whole := wholeChoices source script atomic.toFinset task atomic rfl
    let net := fun choice : WholeChoice source script atomic.toFinset task =>
      network source script fragments.toFinset task choice.reserved
    let certify := fun choice : WholeChoice source script atomic.toFinset task =>
      allocate source script fragments.toFinset task choice.reserved fragments rfl
    match searchResidual net whole
      (wholeChoices_contains_every_original_assignment source script _ task _ rfl) certify with
    | .noWhole absent =>
      .atomic (atomicDeficiency source script atomic.toFinset task atomic rfl
        fun ⟨matching, existing, full⟩ => absent ⟨matching, existing, full⟩)
    | .short first cuts => .fragments first cuts
    | .available choice receipt complete =>
      let allocation : Allocation source script atomic.toFinset fragments.toFinset task := ⟨choice, receipt, complete⟩
      match decideAt source script with
      | .blocked issue => .nativeBlocked allocation issue
      | .feasible paid => .paid disjoint original allocation (settle source script paid)
  else .malformed original

/-- Search every source-authorized whole-bundle assignment before ruling
out a combined settlement. A reservation is used by only one mode. -/
def decideMixed (source : C) (script : Script) (task : TaskId → Task) (atomic fragments : List TaskId) :
    Decision source script atomic.toFinset fragments.toFinset task :=
  match found : atomic.find? (fun id => decide (id ∈ fragments)) with
  | some id => .overlapping id (List.mem_toFinset.mpr (List.mem_of_find?_eq_some found))
      (List.mem_toFinset.mpr (of_decide_eq_true
        (List.find?_some (p := fun key : TaskId => decide (key ∈ fragments)) found)))
  | none => decideDisjoint source script task atomic fragments (Finset.disjoint_left.mpr (by
      intro id whole split
      exact (List.find?_eq_none.mp found id (List.mem_toFinset.mp whole))
        (decide_eq_true (List.mem_toFinset.mp split))))

def JointlyPayable (source : C) (script : Script) (atomic fragments : Finset TaskId) (task : TaskId → Task) : Prop :=
  Disjoint atomic fragments ∧ OriginalDemands fragments task ∧ Feasible source script ∧
    ∃ choice : WholeChoice source script atomic task, ∃ allocation,
      (network source script fragments task choice.reserved).Complete allocation

def Decision.isPaid {source : C} {script : Script} {atomic fragments : Finset TaskId} {task : TaskId → Task} :
    Decision source script atomic fragments task → Bool
  | .paid .. => true
  | _ => false

theorem decision_pays_iff_jointly_payable {source : C} {script : Script}
    {atomic fragments : Finset TaskId} {task : TaskId → Task}
    (decision : Decision source script atomic fragments task) :
    decision.isPaid = true ↔ JointlyPayable source script atomic fragments task := by
  cases decision with
  | overlapping id whole split =>
    exact ⟨fun impossible => Bool.noConfusion impossible, fun possible =>
      (Finset.disjoint_left.mp possible.1 whole split).elim⟩
  | malformed bad =>
    exact ⟨fun impossible => Bool.noConfusion impossible, fun possible => (bad possible.2.1).elim⟩
  | atomic issue =>
    exact ⟨fun impossible => Bool.noConfusion impossible, fun possible => by
      obtain ⟨choice, _, _⟩ := possible.2.2.2
      exact (issue.refutes choice.has_its_own_atomic_settlement).elim⟩
  | fragments _ forEach =>
    exact ⟨fun impossible => Bool.noConfusion impossible, fun possible => by
      obtain ⟨choice, allocation, complete⟩ := possible.2.2.2
      let cut := forEach choice
      exact (a_shortage_rules_out_every_complete_allocation_of_this_execution cut.receipt cut.positive allocation complete).elim⟩
  | nativeBlocked _ issue =>
    exact ⟨fun impossible => Bool.noConfusion impossible, fun possible => (issue.refutes possible.2.2.1).elim⟩
  | paid disjoint original allocation settled =>
    exact ⟨fun _ => ⟨disjoint, original, settled.toFeasible,
      allocation.choice, allocation.receipt.allocation, allocation.complete⟩, fun _ => rfl⟩

theorem the_original_root_records_the_joint_mode_decision
    (source : C) (script : Script) (task : TaskId → Task) (atomic fragments : List TaskId) :
    Recorded source script ∧
      ((decideMixed source script task atomic fragments).isPaid = true ↔
        JointlyPayable source script atomic.toFinset fragments.toFinset task) :=
  ⟨record source script, decision_pays_iff_jointly_payable _⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Mixed
