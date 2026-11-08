import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Delegation.Law

/-! Accepted revisions are recognized in the actual instruction trace.
Challenge jurisdiction and affected service scope are distinct: requiring
the old service holder's port permission would restore its veto.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Delegation

open Institutions.Capitalism.Universal.Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (base : RawLaw Party Good Port Technology Instrument)
  (scope : Jurisdiction Party Good Port)
  (current : RawCurrent Party Good (State (Party := Party) (Technology := Technology)) Instrument)
  (word : RawEvent Party Good Port (State (Party := Party) (Technology := Technology)) Instrument)

structure ActualRevocation where
  private mk ::
  item : {item // item ∈ (law base scope).rawItems current word}
  operator : Party
  target : State (Party := Party) (Technology := Technology)
  operation : item.val.request.operation = .revise operator target
  accepted : (law base scope).Valid item.val.before item.val.request

def recognizeRevocation (item : {item // item ∈ (law base scope).rawItems current word}) :
    Option (ActualRevocation base scope current word) :=
  match operation : item.val.request.operation with
  | .revise operator target =>
      if accepted : (law base scope).Valid item.val.before item.val.request then
        some ⟨item, operator, target, operation, accepted⟩
      else none
  | _ => none

def revocationsAt : List (ActualRevocation base scope current word) :=
  ((law base scope).rawItems current word).attach.filterMap
    (recognizeRevocation base scope current word)

namespace ActualRevocation

variable {base scope current word} (event : ActualRevocation base scope current word)

def after := (law base scope).step event.item.val.before event.item.val.request

theorem authorization :
    event.operator = event.item.val.request.signer ∧
    event.item.val.request.signer ∈ members scope.task ∧
    event.item.val.request.consents = [] ∧
    event.item.val.before.technology.2.isSome = true ∧
    event.target = (event.item.val.before.technology.1, none) := by
  have policy := event.accepted.1.2
  simpa only [law, RawLaw.operationAllowed, RawPolicy.eval, event.operation,
    decide_eq_true_eq] using policy

theorem actual_effect :
    event.after.technology = (event.item.val.before.technology.1, none) ∧
      event.after.claims = event.item.val.before.claims := by
  unfold after
  simp only [RawLaw.step, if_pos event.accepted]
  constructor
  · simpa only [RawLaw.paidStep, event.operation] using event.authorization.2.2.2.2
  · change RawLaw.nextClaims event.item.val.before event.item.val.request = _
    simp only [RawLaw.nextClaims, event.operation]

theorem actual_cost (party : Party) (good : Good) :
    event.after.stock party good +
      flowAt ((law base scope).debit event.item.val.before event.item.val.request) party good =
      event.item.val.before.stock party good := by
  have balance := (law base scope).material_step_balance
    event.item.val.before event.item.val.request party good
  have noCredit : (law base scope).credit event.item.val.before event.item.val.request = [] := by
    simp [RawLaw.credit, event.operation]
  simpa only [after, RawLaw.actualDebit, RawLaw.actualCredit, if_pos event.accepted, noCredit,
    flowAt, amount, List.map_nil, List.sum_nil, add_zero] using balance

theorem real_service_permission_loss (former : Party)
    (held : event.item.val.before.technology.2 = some former)
    (outside : former ∉ members scope.task) :
    (law base scope).allowed event.item.val.before.technology scope.service former = true ∧
    (law base scope).allowed event.after.technology scope.service former = false := by
  constructor
  · simp [law, scope.separate, held]
  · rw [event.actual_effect.1]
    simp [law, scope.separate, outside]

theorem old_request_has_no_authority
    (request : Request Party Good Port (State (Party := Party) (Technology := Technology)) Instrument)
    (outside : request.signer ∉ members scope.task)
    (noFreshConsent : request.consents = [])
    (required : scope.service ∈ (law base scope).requiredPorts event.after request) :
    ¬ (law base scope).Valid event.after request :=
  stale_request_is_rejected base scope event.after request
    (congrArg Prod.snd event.actual_effect.1) outside noFreshConsent required

end ActualRevocation

end SaturationMonoid.ProcessGame.Society.PublicFunction.Delegation
