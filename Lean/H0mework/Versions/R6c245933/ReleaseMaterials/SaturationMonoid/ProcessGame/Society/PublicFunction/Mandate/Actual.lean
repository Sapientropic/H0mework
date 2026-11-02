import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Law
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Election.MandateResponsibility

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate

open Institutions.Capitalism.Universal.Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (base : RawLaw Party Good Port Technology Instrument)
  (scope : Scope (Party := Party) (Good := Good) (Port := Port))
  (current : RawCurrent Party Good (State Party Technology) Instrument)
  (word : RawEvent Party Good Port (State Party Technology) Instrument)

structure ActualCommand where
  private mk ::
  item : {item // item ∈ (law base scope).rawItems current word}
  operator : Party
  target : State Party Technology
  command : Command Party
  operation : item.val.request.operation = .revise operator target
  marked : target.last = some command
  accepted : (law base scope).Valid item.val.before item.val.request

def recognize (item : {item // item ∈ (law base scope).rawItems current word}) :
    Option (ActualCommand base scope current word) :=
  match operation : item.val.request.operation with
  | .revise operator target => match marked : target.last with
    | none => none
    | some command =>
        if accepted : (law base scope).Valid item.val.before item.val.request then
          some ⟨item, operator, target, command, operation, marked, accepted⟩
        else none
  | _ => none

def commandsAt : List (ActualCommand base scope current word) :=
  ((law base scope).rawItems current word).attach.filterMap (recognize base scope current word)

namespace ActualCommand

variable {base scope current word} (event : ActualCommand base scope current word)

def after := (law base scope).step event.item.val.before event.item.val.request

theorem authorization : event.operator = event.item.val.request.signer ∧
    event.item.val.request.consents = [] ∧ event.item.val.request.purpose = scope.challenge ∧
    event.item.val.request.gates = [scope.challenge] ∧
    event.target = advance scope event.item.val.before event.command ∧
    CanRun scope event.item.val.before event.item.val.request.signer event.command := by
  have policy := event.accepted.1.2
  simpa only [law, RawLaw.operationAllowed, RawPolicy.eval, event.operation,
    event.marked, decide_eq_true_eq] using policy

theorem actual_effect : event.after.technology = advance scope event.item.val.before event.command ∧
    event.after.claims = event.item.val.before.claims := by
  unfold after
  simp only [RawLaw.step, if_pos event.accepted]
  constructor
  · simpa only [RawLaw.paidStep, event.operation] using event.authorization.2.2.2.2.1
  · change RawLaw.nextClaims event.item.val.before event.item.val.request = _
    simp only [RawLaw.nextClaims, event.operation]

theorem actual_version_is_fresh :
    event.after.technology.version = event.item.val.before.technology.version + 1 := by
  rw [event.actual_effect.1, advance_version]

theorem actual_cost (party : Party) (good : Good) :
    event.after.stock party good +
      flowAt ((law base scope).debit event.item.val.before event.item.val.request) party good =
      event.item.val.before.stock party good := by
  have balance := (law base scope).material_step_balance event.item.val.before event.item.val.request party good
  have noCredit : (law base scope).credit event.item.val.before event.item.val.request = [] := by
    simp [RawLaw.credit, event.operation]
  simpa only [after, RawLaw.actualDebit, RawLaw.actualCredit, if_pos event.accepted, noCredit,
    flowAt, amount, List.map_nil, List.sum_nil, add_zero] using balance

end ActualCommand

namespace ActualCommand
variable {base scope current word} (event : ActualCommand base scope current word)

def appendRight (suffix : RawEvent Party Good Port (State Party Technology) Instrument) :
    ActualCommand base scope current (word ++ suffix) :=
  ⟨⟨event.item.val,by
      unfold RawLaw.rawItems
      rw [(law base scope).execute_append]
      exact List.mem_append_left _ event.item.property⟩,
    event.operator,event.target,event.command,event.operation,event.marked,event.accepted⟩

theorem is_recognized : recognize base scope current word event.item = some event := by
  rcases event with ⟨⟨⟨index,before,⟨signer,consents,purpose,gates,operation⟩⟩,member⟩,
    operator,⟨technology,version,holder,offered,last⟩,command,operation_eq,marked,accepted⟩
  dsimp only at operation_eq marked
  subst operation
  subst last
  exact dif_pos accepted

theorem is_enumerated : event ∈ commandsAt base scope current word :=
  List.mem_filterMap.mpr ⟨event.item,by simp,event.is_recognized⟩

end ActualCommand

/-- Both signatures are original accepted items in this trace. Only the
authority-state projection is shared between them; material history may differ. -/
structure Grant where
  private mk ::
  proposal : ActualCommand base scope current word
  acceptance : ActualCommand base scope current word
  candidate : Party
  proposed : proposal.command = .propose candidate
  accepted_kind : acceptance.command = .accept
  ordered : proposal.item.val.index < acceptance.item.val.index
  same_offer : proposal.after.technology = acceptance.item.val.before.technology

def grantsAt : List (Grant base scope current word) :=
  (commandsAt base scope current word).flatMap fun proposal =>
    (commandsAt base scope current word).filterMap fun acceptance =>
      match proposed : proposal.command, accepted_kind : acceptance.command with
      | .propose candidate, .accept =>
          if linked : proposal.item.val.index < acceptance.item.val.index ∧
              proposal.after.technology = acceptance.item.val.before.technology then
            some ⟨proposal, acceptance, candidate, proposed, accepted_kind, linked.1, linked.2⟩
          else none
      | _, _ => none

namespace Grant
variable {base scope current word} (grant : Grant base scope current word)

def appendRight (suffix : RawEvent Party Good Port (State Party Technology) Instrument) :
    Grant base scope current (word ++ suffix) :=
  ⟨grant.proposal.appendRight suffix,grant.acceptance.appendRight suffix,grant.candidate,
    grant.proposed,grant.accepted_kind,grant.ordered,grant.same_offer⟩

theorem is_enumerated : grant ∈ grantsAt base scope current word := by
  rcases grant with ⟨proposal,acceptance,candidate,proposed,kind,ordered,same⟩
  rcases proposal with ⟨proposalItem,proposalOperator,proposalTarget,proposalCommand,proposalOperation,proposalMarked,proposalPaid⟩
  rcases acceptance with ⟨acceptanceItem,acceptanceOperator,acceptanceTarget,acceptanceCommand,acceptanceOperation,acceptanceMarked,acceptancePaid⟩
  dsimp only at proposed kind
  subst proposalCommand
  subst acceptanceCommand
  let proposal : ActualCommand base scope current word :=
    ⟨proposalItem,proposalOperator,proposalTarget,.propose candidate,
      proposalOperation,proposalMarked,proposalPaid⟩
  let acceptance : ActualCommand base scope current word :=
    ⟨acceptanceItem,acceptanceOperator,acceptanceTarget,.accept,
      acceptanceOperation,acceptanceMarked,acceptancePaid⟩
  unfold grantsAt
  apply List.mem_flatMap.mpr
  refine ⟨proposal,proposal.is_enumerated,
    List.mem_filterMap.mpr ⟨acceptance,acceptance.is_enumerated,?_⟩⟩
  simp only [proposal,acceptance,dif_pos (And.intro ordered same)]

end Grant

namespace Grant

variable {base scope current word} (grant : Grant base scope current word)

theorem proposal_is_by_task_member :
    grant.proposal.item.val.request.signer ∈ Delegation.members scope.task := by
  have admitted := grant.proposal.authorization.2.2.2.2.2
  rw [grant.proposed] at admitted
  exact admitted.1

theorem original_offer : grant.acceptance.item.val.before.technology.offered = some grant.candidate := by
  rw [← grant.same_offer, grant.proposal.actual_effect.1, grant.proposed]
  rfl

theorem candidate_actually_signed : grant.acceptance.item.val.request.signer = grant.candidate := by
  have admitted := grant.acceptance.authorization.2.2.2.2.2
  rw [grant.accepted_kind] at admitted
  exact Option.some.inj (admitted.1.symm.trans grant.original_offer)

theorem holder_is_generated : grant.acceptance.after.technology.holder = some grant.candidate := by
  rw [grant.acceptance.actual_effect.1, grant.accepted_kind]
  exact grant.original_offer

def electionEvent : Election.MandateEvent Nat Port Party where
  period := grant.acceptance.after.technology.version
  officeSeed := scope.service
  controllerSeed := grant.candidate
  disposition := .continue

def lineageCompiler : Election.ElectionLineageCompiler (Period := Nat)
    (OfficeSeed := Port) (ControllerSeed := Party) (Office := Port) (Controller := Party) :=
  ⟨id, id⟩

def mandateAdmission := Election.mandateAdmissionEdge
  (lineageCompiler (Party := Party) (Port := Port)) grant.electionEvent

theorem native_mandate_bearer_and_scope :
    (Election.mandateObligation (lineageCompiler (Party := Party) (Port := Port)) grant.electionEvent).bearer =
        grant.acceptance.item.val.request.signer ∧
    (Election.mandateObligation (lineageCompiler (Party := Party) (Port := Port)) grant.electionEvent).scope =
        scope.service := by
  exact ⟨grant.candidate_actually_signed.symm, rfl⟩

end Grant

/-- Installation transports the generated native edge itself, retaining
its exact actual Grant rather than replacing it by a native target state. -/
structure AdmittedGrant where
  private mk ::
  grant : Grant base scope current word
  native : (Election.mandateProcess (Grant.lineageCompiler (Party := Party) (Port := Port))).Edge
    (ResponsibilityLifecycle.ResponsibilityState.empty
      (Election.mandateVocabulary (Grant.lineageCompiler (Party := Party) (Port := Port))))
  native_exact : native = grant.mandateAdmission

def admitGrant (grant : Grant base scope current word) : AdmittedGrant base scope current word :=
  ⟨grant, grant.mandateAdmission, rfl⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate
