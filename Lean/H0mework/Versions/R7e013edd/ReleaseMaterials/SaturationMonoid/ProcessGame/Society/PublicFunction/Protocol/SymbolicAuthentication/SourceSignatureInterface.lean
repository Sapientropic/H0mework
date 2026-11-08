import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceReadyMemory

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceSignatureInterface
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

def policyCheck : Bool := match model.base.policy with
  | .unrestricted | .settlement _ => true
  | .opaque _ => false

def inspect : Bool := policyCheck model && decide (model.scope.challenge ≠ model.scope.service) &&
  decide (1 ≤ model.source.code.actionLimit) &&
  (List.finRange model.source.code.sites).all fun receiver => decide
    (RejectionResponse.signature model receiver ∈ model.source.code.actions ∧
      Event.activate receiver ∈ model.source.code.eventAlphabet ∧
      model.source.code.siteParty receiver ∈ Delegation.members model.scope.task)

theorem source_policy_admits_presentation_in_every_actual_state
    (checked : policyCheck model = true)
    (current : RawCurrent Party Good (Mandate.State Party Technology) Instrument)
    (receiver : Fin model.source.code.sites) :
    model.base.operationAllowed (Mandate.eraseCurrent current)
      (Mandate.eraseRequest (RejectionResponse.signature model receiver)) = true := by
  cases policy : model.base.policy with
  | unrestricted => simp only [RawLaw.operationAllowed, policy, RawPolicy.eval]
  | settlement code =>
    simp only [RawLaw.operationAllowed, policy, RawPolicy.eval, Mandate.eraseRequest, Mandate.eraseOperation,
      RejectionResponse.signature, IncidentResponse.signature, SettlementPolicyCode.eval]
  | «opaque» callback => simp only [policyCheck, policy, Bool.false_eq_true] at checked

theorem checked_interface_generates_static_and_legal_signature_resources
    (checked : inspect model = true)
    (current : RawCurrent Party Good (Mandate.State Party Technology) Instrument)
    (receiver : Fin model.source.code.sites) :
    RejectionResponse.signature model receiver ∈ model.source.code.actions ∧
      1 ≤ model.source.code.actionLimit ∧ Event.activate receiver ∈ model.source.code.eventAlphabet ∧
      Mandate.Challenge.Submission (scope := model.scope) (RejectionResponse.signature model receiver) ∧
      model.source.code.law.Valid current (RejectionResponse.signature model receiver) := by
  simp only [inspect, Bool.and_eq_true, decide_eq_true_eq] at checked
  rcases checked with ⟨⟨⟨policy, distinct⟩, capacity⟩, interfaces⟩
  have facts :=  of_decide_eq_true ((List.all_eq_true.mp interfaces) receiver (List.mem_finRange _))
  have allowed := source_policy_admits_presentation_in_every_actual_state model policy current receiver
  refine ⟨facts.1, capacity, facts.2.1, ?_, ?_⟩
  · exact ⟨facts.2.2, rfl, rfl, rfl, trivial⟩
  · rw [model.law_exact]
    simpa [RawLaw.Valid, RawLaw.SignerMatches, RawLaw.requiredPorts, RawLaw.debit, RawLaw.credit,
      RawLaw.ClaimGuard, RawLaw.operationAllowed, RejectionResponse.signature, IncidentResponse.signature,
      Mandate.law, RawPolicy.eval, Mandate.TaskUse, Mandate.eraseRequest, Mandate.eraseOperation,
      distinct, Ne.symm distinct, facts.2.2, NonnegativeBundle] using allowed

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceSignatureInterface
