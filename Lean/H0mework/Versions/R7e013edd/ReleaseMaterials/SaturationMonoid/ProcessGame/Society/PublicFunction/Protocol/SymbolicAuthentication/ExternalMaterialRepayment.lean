import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ExternalMaterialConsumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ExternalMaterialRepayment
open Institutions.Capitalism.Universal.Source.Program
open ExternalMaterialSource ExternalMaterialConsumer
abbrev originalLaw := FuelMandateLaw.law true
abbrev position : Repayment.Position Delegation.Funded.Party Unit := ⟨(),1,2⟩
abbrev debt (current : Community) := current.claims () 1 2
abbrev paymentWord (current : Community) := (Repayment.respond originalLaw position current).word
abbrev next (current : Current) := install current (originalLaw.next (community current) (paymentWord (community current)))

set_option linter.unusedSimpArgs false in
theorem cash_generates_the_original_payment (current : Community) (positive : 0 < debt current)
    (cash : debt current ≤ current.stock 1 .service) :
    Repayment.Ready originalLaw position current ∧ Repayment.quantity originalLaw position current = debt current := by
  have funded : 0 < current.stock 1 .service := lt_of_lt_of_le positive cash
  have prepare : Repayment.preparation originalLaw position current = [] := if_pos funded
  have quantity : Repayment.quantity originalLaw position current = debt current := by
    simp only [Repayment.quantity,Repayment.readyCurrent,prepare,RawLaw.execute]
    change min (debt current) (current.stock 1 .service / 1) = debt current
    simpa only [div_one] using min_eq_left cash
  refine ⟨⟨by simpa only [quantity] using positive,?_⟩,quantity⟩
  intro item member
  simp only [Repayment.candidate,prepare,List.nil_append,RawLaw.rawItems,RawLaw.execute,
    List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  change originalLaw.Valid current ⟨1,[],.reserve 1,[],.settle () 1 2 (Repayment.quantity originalLaw position current)⟩
  rw [quantity]
  simp [RawLaw.Valid,RawLaw.SignerMatches,RawLaw.operationAllowed,RawPolicy.eval,
    RawLaw.requiredPorts,RawLaw.debit,RawLaw.credit,RawLaw.ClaimGuard,NonnegativeBundle,
    originalLaw,position,FuelMandateLaw.law,FuelMandateLaw.base,RenewedQuorumMaterial.base,
    Mandate.law,Mandate.eraseCurrent,Mandate.eraseRequest,Mandate.eraseOperation,Mandate.TaskUse,
    Repayment.Recovery.base,Repayment.Recovery.scope,Repayment.Recovery.task,flowAt,locate,amount]
  all_goals repeat' constructor
  all_goals linarith

theorem the_original_response_uses_the_generated_cash (current : Community) (positive : 0 < debt current)
    (cash : debt current ≤ current.stock 1 .service) :
    paymentWord current = Repayment.candidate originalLaw position current := by
  have ready := (cash_generates_the_original_payment current positive cash).1
  change (Repayment.respond originalLaw position current).word = _
  simp only [Repayment.respond,show Repayment.balance position current = debt current from rfl,
    dif_pos positive,dif_pos ready,Repayment.Response.word]

theorem actual_funded_upstream_production_settles_the_same_original_debt (current : Current) (count : Nat)
    (reserve : Reserve current count) (positive : 0 < debt (community current))
    (resources : debt (community current) ≤ (community current).stock 1 .service + 3 * count) :
    debt (community (next (ExternalMaterialConsumer.run current count))) = 0 := by
  have generated := the_actual_upstream_stock_generates_every_funded_cycle current count reserve
  have sameDebt : debt (community (ExternalMaterialConsumer.run current count)) = debt (community current) := by
    rw [generated];rfl
  have service : (community (ExternalMaterialConsumer.run current count)).stock 1 .service =
      (community current).stock 1 .service + 3 * count := by
    rw [generated];simp [community,ExternalMaterialConsumer.expected,supplier]
  have positiveNow := sameDebt.symm ▸ positive
  have cash : debt (community (ExternalMaterialConsumer.run current count)) ≤
      (community (ExternalMaterialConsumer.run current count)).stock 1 .service := by rw [sameDebt,service];exact resources
  have paid := cash_generates_the_original_payment _ positiveNow cash
  change (originalLaw.next _ (paymentWord _)).claims () 1 2 = 0
  rw [the_original_response_uses_the_generated_cash _ positiveNow cash]
  rw [Repayment.paid_principal_balance originalLaw position _ paid.1,paid.2]
  exact sub_self _
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ExternalMaterialRepayment
