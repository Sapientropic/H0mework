import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Control.Scenario.Compare
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.RootBinding

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility

open Source.Program
open Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

/-- Only the permission gates change at this intermediate interpretation.
The policy component remains a separately accountable source restriction. -/
def permissionsOpened (source : Trials.Mechanism Party Good Port Technology Instrument) :=
  { source with code := { source.code with law :=
    { source.code.law with allowed := fun _ _ _ => true } } }

variable (source : Trials.Mechanism Party Good Port Technology Instrument)
  (past : List (RawEvent Party Good Port Technology Instrument)) (nature : source.Nature)
  (response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

def permissionLoss (good : Good) : ℚ :=
  Control.net (permissionsOpened source).code.law
      (Control.responseExecution (permissionsOpened source) past nature response).items good -
    Control.net source.code.law (Control.responseExecution source past nature response).items good

def policyLoss (good : Good) : ℚ :=
  Control.net (Control.openedProgramme source).code.law
      (Control.responseExecution (Control.openedProgramme source) past nature response).items good -
    Control.net (permissionsOpened source).code.law
      (Control.responseExecution (permissionsOpened source) past nature response).items good

theorem the_full_original_gap_retains_permission_and_policy_responsibility (good : Good) :
    Control.measuredLoss source past nature response good =
      permissionLoss source past nature response good + policyLoss source past nature response good := by
  unfold Control.measuredLoss Control.controlLoss permissionLoss policyLoss
  ring

theorem permissions_are_the_whole_gap_when_the_original_policy_is_unrestricted
    (unrestricted : source.code.law.policy = .unrestricted) (good : Good) :
    permissionLoss source past nature response good = Control.measuredLoss source past nature response good ∧
      policyLoss source past nature response good = 0 := by
  have sameLaw : {source.code.law with allowed := fun _ _ _ => true} =
      PublicFunction.physicalLaw source.code.law := by
    unfold PublicFunction.physicalLaw
    rw [← unrestricted]
  have same : permissionsOpened source = Control.openedProgramme source := by
    unfold permissionsOpened Control.openedProgramme
    rw [sameLaw]
  have zero : policyLoss source past nature response good = 0 := by
    unfold policyLoss
    rw [same,sub_self]
  exact ⟨by
    rw [the_full_original_gap_retains_permission_and_policy_responsibility,zero,add_zero],zero⟩

/-- Productive harm is read before any internal financial redistribution.
The same original debit includes investment, maintenance and actual response costs. -/
def productiveNetAt (law : RawLaw Party Good Port Technology Instrument)
    (item : ExecutionItem Party Good Port Technology Instrument) (party : Party) (good : Good) : ℚ :=
  match item.request.operation with
  | .produce _ => flowAt (law.actualCredit item.before item.request) party good -
      flowAt (law.actualDebit item.before item.request) party good
  | .use .. | .revise .. => -flowAt (law.actualDebit item.before item.request) party good
  | _ => 0

def productiveNetFor (law : RawLaw Party Good Port Technology Instrument)
    (items : List (ExecutionItem Party Good Port Technology Instrument)) (party : Party) (good : Good) : ℚ :=
  (items.map fun item => productiveNetAt law item party good).sum

def partyLoss (party : Party) (good : Good) : ℚ :=
  productiveNetFor (Control.openedProgramme source).code.law
      (Control.responseExecution (Control.openedProgramme source) past nature response).items party good -
    productiveNetFor source.code.law (Control.responseExecution source past nature response).items party good

structure AssessedClaim (party : Party) (good : Good) : Type where
  private mk ::
  positive : 0 < partyLoss source past nature response party good

def assess (party : Party) (good : Good) : Option (AssessedClaim source past nature response party good) :=
  if positive : 0 < partyLoss source past nature response party good then some ⟨positive⟩ else none

namespace AssessedClaim
variable {source past nature response party good}

def quantity (_claim : AssessedClaim source past nature response party good) : ℚ :=
  partyLoss source past nature response party good

theorem quantity_is_the_original_productive_gap
    (claim : AssessedClaim source past nature response party good) :
    claim.quantity = partyLoss source past nature response party good := rfl

end AssessedClaim

abbrev OriginalItem := {item // item ∈ (Control.responseExecution source past nature response).items}

structure GateOccurrence where
  item : OriginalItem source past nature response
  port : {port // port ∈ source.code.law.requiredPorts item.val.before item.val.request}
  withheld : source.code.law.allowed item.val.before.technology port.val item.val.request.signer = false ∧
    source.code.law.controller item.val.before.technology port.val ∉ item.val.request.consents

namespace GateOccurrence
variable (gate : GateOccurrence source past nature response)

def controller : Party := source.code.law.controller gate.item.val.before.technology gate.port.val

theorem the_original_request_is_rejected : ¬ source.code.law.Valid gate.item.val.before gate.item.val.request := by
  intro valid
  rcases valid.2.1 gate.port.val gate.port.property with allowed | consent
  · exact Bool.noConfusion (gate.withheld.1.symm.trans allowed)
  · exact gate.withheld.2 consent

theorem controller_is_an_original_item_participant :
    gate.controller source past nature response ∈ Source.ProgrammeFace.itemParties source.code.law gate.item.val :=
  Source.ProgrammeFace.controller_mem_itemParties source.code.law gate.item.val gate.port.val gate.port.property

end GateOccurrence

def gateOccurrences : List (GateOccurrence source past nature response) :=
  (Control.responseExecution source past nature response).items.attach.flatMap fun item =>
    (source.code.law.requiredPorts item.val.before item.val.request).attach.filterMap fun port =>
      if blocked : source.code.law.allowed item.val.before.technology port.val item.val.request.signer = false ∧
          source.code.law.controller item.val.before.technology port.val ∉ item.val.request.consents then
        some ⟨item,port,blocked⟩ else none

def controllerCohort : List Party :=
  ((gateOccurrences source past nature response).map fun gate => gate.controller source past nature response).dedup

def policyOccurrences : List (OriginalItem source past nature response) :=
  (Control.responseExecution source past nature response).items.attach.filter fun item =>
    decide (source.code.law.operationAllowed item.val.before item.val.request = false)

theorem every_generated_controller_has_its_original_blocked_site
    (actor : Party) (member : actor ∈ controllerCohort source past nature response) :
    ∃ gate ∈ gateOccurrences source past nature response,
      gate.controller source past nature response = actor ∧
      ¬ source.code.law.Valid gate.item.val.before gate.item.val.request := by
  obtain ⟨gate,original,same⟩ := List.mem_map.mp (List.mem_dedup.mp member)
  exact ⟨gate,original,same,gate.the_original_request_is_rejected source past nature response⟩

theorem every_generated_policy_site_is_an_original_rejection
    (item : OriginalItem source past nature response)
    (member : item ∈ policyOccurrences source past nature response) :
    ¬ source.code.law.Valid item.val.before item.val.request := by
  have rejected := of_decide_eq_true (List.mem_filter.mp member).2
  intro valid
  exact Bool.noConfusion (rejected.symm.trans valid.1.2)

theorem an_unrestricted_original_policy_has_no_policy_rejection
    (unrestricted : source.code.law.policy = .unrestricted) :
    policyOccurrences source past nature response = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro item _
  simp [RawLaw.operationAllowed,unrestricted,RawPolicy.eval]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility
