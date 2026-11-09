import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Review.Payment

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open PublicFunction.Mandate

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

local notation "C" => Root.Cut Party Good Port (State Party Technology) Instrument
local notation "Word" => RawEvent Party Good Port (State Party Technology) Instrument
local notation "Raw" => RawCurrent Party Good (State Party Technology) Instrument
local notation "Item" => ExecutionItem Party Good Port (State Party Technology) Instrument
local notation "Req" => Request Party Good Port (State Party Technology) Instrument
local notation "Base" => RawLaw Party Good Port Technology Instrument
local notation "J" => Scope (Party := Party) (Good := Good) (Port := Port)
local notation "Script" => List (Option (Compile.RawInput Party Good Port (State Party Technology) Instrument))

def Ordinary (request : Req) : Prop :=
  match request.operation with
  | .revise .. => False
  | _ => True

def UsesMandate (base : Base) (scope : J) (before : Raw) (request : Req) : Prop :=
  scope.service ∈ base.requiredPorts (eraseCurrent before) (eraseRequest request) ∨ TaskUse scope request

omit [DecidableEq Instrument] in
theorem every_protected_operation_reads_the_original_clock (base : Base) (scope : J)
    (before : Raw) (request : Req) (ordinary : Ordinary request)
    (valid : (law base scope).Valid before request) (protectedUse : UsesMandate base scope before request) :
    before.technology.holder = some request.signer ∧
      scope.task.earliest ≤ before.clock ∧ before.clock ≤ scope.task.deadline := by
  have check := valid.1.2
  simp only [law, RawLaw.operationAllowed, RawPolicy.eval] at check
  cases operation : request.operation <;>
    simp_all only [Ordinary, Bool.and_eq_true, decide_eq_true_eq]
  all_goals exact check.2 protectedUse

/-- On any descendant of the original expired source, even a retargeted
authorization cannot mobilize a protected port or consume task goods. -/
theorem no_paid_emergency_operation_after_expiry {source : C} {base : Base} {scope : J}
    (original : Installed source base scope) (late : scope.task.deadline < source.raw.clock) (history : Script) :
    let cut := Quantities.Execution.endAt source history
    ∀ word : Word, ∀ item : Item, item ∈ (law base scope).rawItems cut.raw word →
      Ordinary item.request → UsesMandate base scope item.before item.request → ¬ Root.Paid cut word := by
  intro cut word item member ordinary used paid
  have same := original_execution (original.along history) paid
  have actual := paid.authorized item (by unfold RawLaw.rawItems; rw [same]; exact member)
  have installed := original.along history
  unfold Installed at installed
  change (Quantities.Execution.endAt source history).native.input.law = _ at installed
  rw [show cut.native.input.law = law base scope from installed] at actual
  have timely := (every_protected_operation_reads_the_original_clock base scope item.before
    item.request ordinary actual used).2.2
  have sameClock := original_item_clock base scope cut.raw word 0 item member
  rw [sameClock] at timely
  have expired := (no_reset_on_any_original_successor original late history).2.2.1
  exact (not_lt_of_ge timely) expired

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Technology]
  [DecidableEq Instrument] in
/-- Service ownership is read from an affected material address. Removing an
advertised gate or renaming the operation cannot remove this required port. -/
theorem protected_debit_reads_the_mandate (base : Base) (scope : J) (before : Raw) (request : Req)
    (debit : (Party × Good) × ℚ) (affected : debit ∈ base.debit (eraseCurrent before) (eraseRequest request))
    (address : base.stockPort before.technology.technology debit.1.1 debit.1.2 = scope.service) :
    UsesMandate base scope before request := by
  apply Or.inl
  unfold RawLaw.requiredPorts
  apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨debit, affected, address⟩

theorem no_material_relabel_after_expiry {source : C} {base : Base} {scope : J}
    (original : Installed source base scope) (late : scope.task.deadline < source.raw.clock) (history : Script) :
    let cut := Quantities.Execution.endAt source history
    ∀ word : Word, ∀ item : Item, item ∈ (law base scope).rawItems cut.raw word →
      Ordinary item.request → ∀ debit : (Party × Good) × ℚ,
        debit ∈ base.debit (eraseCurrent item.before) (eraseRequest item.request) →
        base.stockPort item.before.technology.technology debit.1.1 debit.1.2 = scope.service →
        ¬ Root.Paid cut word := by
  intro cut word item member ordinary debit affected address
  exact no_paid_emergency_operation_after_expiry original late history word item member ordinary
    (protected_debit_reads_the_mandate base scope item.before item.request debit affected address)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency
