import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Delegation.FundedSource

/-! Both the inherited seven-unit debt and the new three-unit loan are
issued and disbursed in one source history. No preloaded financial balance
is used as a substitute for a native debt origin.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Delegation.FinancedGenesis

open Institutions.Capitalism.Universal.Source.Program
open Funded (Party Port Current Action)
open OutstandingSource.NativeService

def base : RawLaw Party Unit Port Unit Unit := { Funded.base with
  policy := .opaque (fun current request => match request.operation with
    | .issue _ debtor creditor quantity => decide
        (debtor = 1 ∧ creditor = 2 ∧
          ((quantity = 7 ∧ current.claims () 1 2 = 0) ∨
           (quantity = 3 ∧ current.claims () 1 2 = 7)))
    | .transfer sender recipient goods => decide
        (sender = 2 ∧ recipient = 1 ∧
          ((goods = [((), 7)] ∧ current.claims () 1 2 = 7) ∨
           (goods = [((), 3)] ∧ current.claims () 1 2 = 10)))
    | _ => true) }

def law := Delegation.law base Funded.scope

def initial : Current := { Funded.initial with
  stock := fun person _ => if person = 2 then 10 else 0
  claims := fun _ _ _ => 0 }

def oldTerms : Financing.Terms Party Unit := ⟨1, 2, (), 7⟩
def oldIssue : Action := ⟨1, [], .reserve 1, [], .issue () 1 2 7⟩
def oldPayout : Action := ⟨2, [], .reserve 2, [], .transfer 2 1 [((), 7)]⟩
def oldUse : Action := ⟨1, [], .reserve 1, [], .use 1 [((), 7)] .investment⟩

def source : OutstandingSource Party Unit Port (Unit × Option Party) Unit where
  seed := {
    law := law
    initial := initial
    task := Funded.task
    actionsAt := Funded.alphabet
    budget := 5
    original := [oldIssue, oldPayout, oldUse, Funded.original]
    refused := by decide +kernel }
  positive := Funded.source.positive

theorem zero_financial_genesis : source.input.initial.claims = fun _ _ _ => 0 := rfl

theorem old_debt_is_actually_issued_and_funded :
    (source.actualExecution 0).submitted = [oldIssue, oldPayout, oldUse, Funded.original] ∧
    (Financing.readDisbursement? law (source.actualExecution 0).before
      (source.actualExecution 0).submitted oldTerms).isSome = true ∧
    (source.actualExecution 0).after.claims () 1 2 = 7 ∧
    (source.actualExecution 0).after.stock 1 () = 0 ∧
    (source.actualExecution 0).after.stock 2 () = 3 := by
  refine ⟨source.actual_original_word, ?_, ?_, ?_, ?_⟩
  · rw [source.actual_original_word, source.actual_execution_before]; decide +kernel
  all_goals rw [source.actual_execution_after]; decide +kernel

theorem actual_planner_borrows_revokes_and_serves :
    (source.actualExecution 1).submitted = [Funded.issue, Funded.payout,
      revokeRequest Funded.scope (source.currentAt 2) 1, Funded.necessity, Funded.maintenance] := by
  rw [source.actual_execution_word]
  with_unfolding_all rfl

theorem new_loan_is_actually_funded :
    (Financing.readDisbursement? law (source.actualExecution 1).before
      (source.actualExecution 1).submitted Funded.terms).isSome = true ∧
    (source.actualExecution 1).after.claims () 1 2 = 10 ∧
    (source.actualExecution 1).after.stock 1 () = 0 ∧
    (source.actualExecution 1).after.stock 2 () = 0 ∧
    (source.actualExecution 1).after.technology = ((), none) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [actual_planner_borrows_revokes_and_serves, source.actual_execution_before]; decide +kernel
  all_goals rw [source.actual_execution_after]; decide +kernel

theorem native_services_are_paid (index : source.Slot) :
    (historyAt source index 2).state.TerminalAt 0 := by
  apply (native_terminal_iff_recorded source index 2).mpr
  refine ⟨2, ?_⟩
  have bound : index.val < 2 := index.isLt
  by_cases zero : index.val = 0
  · have same : index = ⟨0, by decide⟩ := Fin.ext zero
    subst index
    decide +kernel
  · have same : index = ⟨1, by decide⟩ := Fin.ext (by change index.val = 1; omega)
    subst index
    decide +kernel

end SaturationMonoid.ProcessGame.Society.PublicFunction.Delegation.FinancedGenesis
