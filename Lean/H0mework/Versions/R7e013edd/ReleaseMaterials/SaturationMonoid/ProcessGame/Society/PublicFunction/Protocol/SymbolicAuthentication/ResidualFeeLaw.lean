import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ResidualQuorumSource
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ResourceEnvelope

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ResidualFeeLaw
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol Continuation
open RenewedQuorumConsumer (code start protocols)
open RenewedQuorumSource (fee)
open Delegation.Funded (Party)
open Repayment.Recovery (Good)
abbrev Current := RecycledQuorumMaterial.Current

set_option linter.unusedSimpArgs false in
theorem original_fee_valid (current : Current) (second : Bool) (funded : 1 ≤ current.stock 1 .service) :
    code.law.Valid current (fee second) := by
  cases second <;>
    simpa [RawLaw.Valid,RawLaw.SignerMatches,RawLaw.operationAllowed,RawPolicy.eval,
      RawLaw.requiredPorts,RawLaw.debit,RawLaw.credit,RawLaw.ClaimGuard,fee,code,
      RenewedQuorumSource.code,RenewedQuorumMaterial.law,RenewedQuorumMaterial.base,
      Mandate.law,Mandate.TaskUse,Mandate.eraseCurrent,Mandate.eraseRequest,Mandate.eraseOperation,
      Repayment.Recovery.base,Repayment.Recovery.scope,Repayment.Recovery.task,
      NonnegativeBundle,flowAt,locate,amount] using funded

set_option linter.unusedSimpArgs false in
theorem fee_stock (current : Current) (second : Bool) (funded : 1 ≤ current.stock 1 .service)
    (party : Party) (good : Good) :
    (code.law.next current [fee second]).stock party good =
      current.stock party good - (if party = 1 ∧ good = .service then 1 else 0) := by
  have valid := original_fee_valid current second funded
  simp only [RawLaw.next,RawLaw.execute,RawLaw.step,if_pos valid]
  fin_cases party <;> cases good <;> cases second <;>
    simp [RawLaw.paidStep,RawLaw.debit,RawLaw.credit,fee,code,RenewedQuorumSource.code,
      RenewedQuorumMaterial.law,RenewedQuorumMaterial.base,Mandate.law,flowAt,locate,amount]

set_option linter.unusedSimpArgs false in
theorem fee_bill (current : Current) (second : Bool) (party : Party) (good : Good) :
    ResourceEnvelope.bill code.law (code.law.rawItems current [fee second]) party good =
      if party = 1 ∧ good = .service then 1 else 0 := by
  fin_cases party <;> cases good <;> cases second <;>
    simp [ResourceEnvelope.bill,ResourceEnvelope.demand,RawLaw.rawItems,RawLaw.execute,
      RawLaw.debit,fee,code,RenewedQuorumSource.code,RenewedQuorumMaterial.law,
      RenewedQuorumMaterial.base,Mandate.law,flowAt,locate,amount]

theorem original_fee_items (current : Current) (second : Bool) (funded : 1 ≤ current.stock 1 .service) :
    ∀ item ∈ code.law.rawItems current [fee second], code.law.Valid item.before item.request := by
  intro item member
  simp only [RawLaw.rawItems,RawLaw.execute,List.mem_cons,List.not_mem_nil,or_false] at member
  subst item
  exact original_fee_valid current second funded

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ResidualFeeLaw
