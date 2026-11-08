import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProductiveMandateSource

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProductiveMandateChecks
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open ProductiveMandateSource

theorem original_bootstrap_is_paid_and_issues_real_debt :
    (∀ item ∈ law.rawItems initial bootstrap, law.Valid item.before item.request) ∧
    boot.stock false true = 1 ∧ boot.stock true true = 1 ∧
    boot.claims () false true = 7 ∧ boot.technology.holder = some true ∧ boot.technology.version = 2 := by
  decide +kernel

theorem the_grant_has_two_actual_distinct_consent_signers :
    (Mandate.grantsAt base scope initial bootstrap).map (fun grant =>
      (grant.proposal.item.val.request.signer,grant.acceptance.item.val.request.signer,grant.candidate)) =
      [(false,true,true)] := by decide +kernel

theorem the_two_actual_owners_submit_and_pay_the_original_productive_word :
    (StageTrace.records start worked.stages).flatMap (fun row => row.submitted) = body ++ body ∧
    (worked.entries.filter fun entry => entry.verdict model == .command).map
      (fun entry => (StageTrace.activation (entry.row model)).map Fin.val) = [some 1,some 1,some 0,some 0,some 1,some 0,some 1,some 1,some 0,some 0,some 1,some 0] ∧
    (∀ row ∈ StageTrace.records start worked.stages, ∀ item ∈ StageTrace.items row,
      law.Valid item.before item.request) := by
  decide +kernel

theorem actual_production_retains_the_grant_and_original_financial_debt :
    let current := (EventStep.seed (worked.current model start)).current
    current.stock false true = 5 ∧ current.stock true true = 1 ∧
    current.claims = boot.claims ∧ current.technology = boot.technology ∧
    (worked.current model start).cut = 40 ∧ (EventStep.seed (worked.current model start)).remaining = 24 := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · funext instrument debtor creditor
    cases instrument;cases debtor <;> cases creditor <;> decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

def serviceView : Bool := match service with
  | .service receipt => decide (NativeCommandCompiler.input model start worked receipt.ready = .command 6)
  | _ => false
theorem the_generated_material_funds_the_original_native_service : serviceView = true := by decide +kernel

def unfundedView : Bool := match NativeCommandService.produce model start state 0 with
  | .refused _ _ _ => true
  | _ => false
theorem removing_production_leaves_an_actual_law_refusal : unfundedView = true := by decide +kernel

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProductiveMandateChecks
