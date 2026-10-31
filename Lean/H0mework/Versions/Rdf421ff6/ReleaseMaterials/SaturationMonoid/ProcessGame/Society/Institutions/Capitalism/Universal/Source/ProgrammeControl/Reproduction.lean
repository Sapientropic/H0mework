import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Circuit
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Decoder.ActualInventory

/-! Actual surplus use, source-computed needs and renewed physical inputs
are checked on one execution.  Financial positions keep their own units and
original debt lineage; they are never added to a physical surplus amount. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl

open Program
universe u
variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)
  (current : RawCurrent Party Good Technology Instrument)
  (word : RawEvent Party Good Port Technology Instrument)

/-- This counts only actual accepted source-checked use instructions. -/
def usedFor (kind : Use) (party : Party) (good : Good) : ℚ :=
  ((law.rawItems current word).map (fun item => Decoder.consumedFor law kind item party good)).sum

def NeedsPaid : Prop :=
  ∀ party ∈ ProgrammeFace.parties law (current, word),
    (∀ entry ∈ law.necessities current party,
      amount Good (law.necessities current party) entry.1 ≤ usedFor law current word .necessity party entry.1) ∧
    (∀ entry ∈ law.mandatoryMaintenance current party,
      amount Good (law.mandatoryMaintenance current party) entry.1 ≤ usedFor law current word .maintenance party entry.1)

instance : Decidable (NeedsPaid law current word) := by unfold NeedsPaid; infer_instance

/-- Only finite actual footprint coordinates are checked.  Untouched
coordinates already obey the original complete material balance. -/
def InputsRenewed : Prop :=
  ∀ item ∈ law.rawItems current word,
    ∀ entry ∈ law.actualDebit item.before item.request ++ law.actualCredit item.before item.request,
      current.stock entry.1.1 entry.1.2 ≤ (law.next current word).stock entry.1.1 entry.1.2

instance : Decidable (InputsRenewed law current word) := by unfold InputsRenewed; infer_instance

structure SurplusProposal where
  circuit : CircuitProposal law current word
  disposition : OriginalItem law current word
  good : Good
  route : List (RouteLeg law current word)

namespace SurplusProposal
variable (proposal : SurplusProposal law current word)

def beneficiary : Party :=
  law.controller proposal.disposition.val.before.technology proposal.circuit.port

def actualAmount : ℚ :=
  flowAt (law.actualDebit proposal.disposition.val.before proposal.disposition.val.request)
    (proposal.beneficiary law current word) proposal.good

def Disposed : Prop :=
  match proposal.disposition.val.request.operation with
  | .use bearer _ kind => bearer = proposal.beneficiary law current word ∧
      (kind = .external ∨ kind = .investment) ∧
      law.Valid proposal.disposition.val.before proposal.disposition.val.request ∧
      0 < proposal.actualAmount law current word
  | _ => False

instance : Decidable (proposal.Disposed law current word) := by
  unfold Disposed
  cases proposal.disposition.val.request.operation <;> infer_instance

def Checks : Prop :=
  proposal.circuit.Checks law current word ∧
  proposal.Disposed law current word ∧
  PrivatePhase law proposal.disposition.val.before proposal.circuit.port proposal.circuit.recipient ∧
  Follows law current word (proposal.circuit.operator, proposal.circuit.outputGood)
    (proposal.circuit.production.val.index + 1) proposal.route
    (proposal.beneficiary law current word, proposal.good) proposal.disposition.val.index ∧
  NeedsPaid law current word ∧ InputsRenewed law current word

instance : Decidable (proposal.Checks law current word) := by unfold Checks; infer_instance
end SurplusProposal

structure PrivateProductionReproduction where
  private mk ::
  proposal : SurplusProposal law current word
  checked : proposal.Checks law current word

def compilePrivateProduction (proposal : SurplusProposal law current word) :
    Option (PrivateProductionReproduction law current word) :=
  if checked : proposal.Checks law current word then some ⟨proposal, checked⟩ else none

theorem compilePrivateProduction_success (proposal : SurplusProposal law current word)
    (checked : proposal.Checks law current word) :
    ∃ reproduction, compilePrivateProduction law current word proposal = some reproduction :=
  ⟨⟨proposal, checked⟩, dif_pos checked⟩

namespace PrivateProductionReproduction
variable (reproduction : PrivateProductionReproduction law current word)

/-- The right may subsequently be retained without positive realized
surplus on every step.  This is its actual generating circuit. -/
def control : ReproducedControl law current word :=
  (compileCircuit law current word reproduction.proposal.circuit).get
    (by simp [compileCircuit, reproduction.checked.1])

theorem control_proposal_exact :
    (reproduction.control law current word).proposal = reproduction.proposal.circuit := by
  simp [control, compileCircuit, reproduction.checked.1]

omit [DecidableEq Port] in
theorem actual_surplus_and_all_source_needs :
    0 < reproduction.proposal.actualAmount law current word ∧
    law.Valid reproduction.proposal.disposition.val.before reproduction.proposal.disposition.val.request ∧
    NeedsPaid law current word ∧ InputsRenewed law current word := by
  have disposed := reproduction.checked.2.1
  unfold SurplusProposal.Disposed at disposed
  split at disposed
  · exact ⟨disposed.2.2.2, disposed.2.2.1,
      reproduction.checked.2.2.2.2.1, reproduction.checked.2.2.2.2.2⟩
  all_goals contradiction
end PrivateProductionReproduction

inductive ContributionMode
  | productiveInput | returnFlow
  deriving DecidableEq

/-- Actual labour, care, material contribution or realized repayment can
be traced through intermediate households and productive conversions. -/
structure ContributionProposal where
  reproduction : SurplusProposal law current word
  mode : ContributionMode
  inputGood : Good
  outputGood : Good
  route : List (RouteLeg law current word)

namespace ContributionProposal
variable (proposal : ContributionProposal law current word)

def Checks : Prop :=
  proposal.reproduction.Checks law current word ∧ proposal.route ≠ [] ∧
  match proposal.mode with
  | .productiveInput =>
      Follows law current word (proposal.reproduction.circuit.recipient, proposal.inputGood) 0 proposal.route
        (proposal.reproduction.circuit.operator, proposal.outputGood)
        proposal.reproduction.circuit.production.val.index ∧
      0 < flowAt (law.actualDebit proposal.reproduction.circuit.production.val.before
        proposal.reproduction.circuit.production.val.request)
        proposal.reproduction.circuit.operator proposal.outputGood
  | .returnFlow =>
      Follows law current word (proposal.reproduction.circuit.recipient, proposal.inputGood)
        (proposal.reproduction.circuit.production.val.index + 1) proposal.route
        (proposal.reproduction.beneficiary law current word, proposal.outputGood)
        proposal.reproduction.disposition.val.index

instance : Decidable (proposal.Checks law current word) := by
  unfold Checks
  cases proposal.mode <;> infer_instance
end ContributionProposal

structure CapitalContributionReproduction where
  private mk ::
  proposal : ContributionProposal law current word
  checked : proposal.Checks law current word

def compileContribution (proposal : ContributionProposal law current word) :
    Option (CapitalContributionReproduction law current word) :=
  if checked : proposal.Checks law current word then some ⟨proposal, checked⟩ else none

namespace CapitalContributionReproduction
variable (reproduction : CapitalContributionReproduction law current word)

def privateProduction : PrivateProductionReproduction law current word :=
  (compilePrivateProduction law current word reproduction.proposal.reproduction).get
    (by simp [compilePrivateProduction, reproduction.checked.1])

theorem private_proposal_exact :
    (reproduction.privateProduction law current word).proposal = reproduction.proposal.reproduction := by
  simp [privateProduction, compilePrivateProduction, reproduction.checked.1]
end CapitalContributionReproduction

#print axioms compilePrivateProduction
#print axioms PrivateProductionReproduction.actual_surplus_and_all_source_needs
#print axioms compileContribution

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl
