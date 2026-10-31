import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Circuit

/-! Constitutive access can release existing property, realize a service or
license production.  It need not create new goods and it need not yield a
positive profit.  All access and necessary-use addresses are original. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel

open Program
universe u
variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)
  (current : RawCurrent Party Good Technology Instrument)
  (word : RawEvent Party Good Port Technology Instrument)

inductive AccessMode
  | acquired | used
  deriving DecidableEq

structure AccessProposal where
  access : OriginalItem law current word
  necessity : OriginalItem law current word
  mode : AccessMode
  accessHolder : Party
  recipient : Party
  port : Port
  accessGood : Good
  necessityGood : Good
  delivery : List (RouteLeg law current word)

namespace AccessProposal
variable (proposal : AccessProposal law current word)

def controller : Party := law.controller proposal.access.val.before.technology proposal.port

def RequiredUsePaid : Prop :=
  match proposal.necessity.val.request.operation with
  | .use recipient goods kind => recipient = proposal.recipient ∧
      (kind = .necessity ∨ kind = .maintenance) ∧
      law.Valid proposal.necessity.val.before proposal.necessity.val.request ∧
      0 < amount Good goods proposal.necessityGood
  | _ => False

instance : Decidable (proposal.RequiredUsePaid law current word) := by
  unfold RequiredUsePaid
  cases proposal.necessity.val.request.operation with
  | use _ _ kind => cases kind <;> infer_instance
  | _ => infer_instance

def Accessed : Prop := match proposal.mode with
  | .acquired =>
      0 < flowAt (law.actualCredit proposal.access.val.before proposal.access.val.request)
        proposal.accessHolder proposal.accessGood ∧
      Follows law current word (proposal.accessHolder, proposal.accessGood)
        (proposal.access.val.index + 1) proposal.delivery
        (proposal.recipient, proposal.necessityGood) proposal.necessity.val.index
  | .used =>
      proposal.access.val.index = proposal.necessity.val.index ∧
      proposal.accessHolder = proposal.recipient ∧ proposal.accessGood = proposal.necessityGood ∧
      proposal.delivery = [] ∧
      0 < flowAt (law.actualDebit proposal.access.val.before proposal.access.val.request)
        proposal.recipient proposal.necessityGood

instance : Decidable (proposal.Accessed law current word) := by
  unfold Accessed
  cases proposal.mode <;> infer_instance

def Checks : Prop :=
  law.Valid proposal.access.val.before proposal.access.val.request ∧
  proposal.port ∈ law.requiredPorts proposal.access.val.before proposal.access.val.request ∧
  PrivatePhase law proposal.access.val.before proposal.port proposal.recipient ∧
  proposal.RequiredUsePaid law current word ∧ proposal.Accessed law current word ∧
  PrivatePhase law (law.next current word) proposal.port proposal.recipient

instance : Decidable (proposal.Checks law current word) := by unfold Checks; infer_instance
end AccessProposal

structure AccessBasis where
  private mk ::
  proposal : AccessProposal law current word
  checked : proposal.Checks law current word

def compileAccess (proposal : AccessProposal law current word) : Option (AccessBasis law current word) :=
  if checked : proposal.Checks law current word then some ⟨proposal, checked⟩ else none

namespace AccessBasis
variable (basis : AccessBasis law current word)

omit [DecidableEq Port] in
theorem original_access_and_real_necessity :
    law.Valid basis.proposal.access.val.before basis.proposal.access.val.request ∧
    basis.proposal.port ∈ law.requiredPorts basis.proposal.access.val.before basis.proposal.access.val.request ∧
    law.Valid basis.proposal.necessity.val.before basis.proposal.necessity.val.request ∧
    ∃ goods kind, basis.proposal.necessity.val.request.operation =
      .use basis.proposal.recipient goods kind ∧
      ((kind = .necessity ∧ goods = law.necessities basis.proposal.necessity.val.before basis.proposal.recipient) ∨
       (kind = .maintenance ∧ goods = law.mandatoryMaintenance basis.proposal.necessity.val.before basis.proposal.recipient)) ∧
      0 < amount Good goods basis.proposal.necessityGood := by
  refine ⟨basis.checked.1, basis.checked.2.1, ?_⟩
  have paid := basis.checked.2.2.2.1
  unfold AccessProposal.RequiredUsePaid at paid
  cases operation : basis.proposal.necessity.val.request.operation with
  | use bearer goods kind =>
      simp only [operation] at paid
      rcases paid with ⟨rfl, necessary | maintenance, accepted, positive⟩
      · subst kind
        have guarded := accepted.2.2.1
        simp only [RawLaw.ClaimGuard, operation] at guarded
        exact ⟨accepted, goods, .necessity, rfl, Or.inl ⟨rfl, guarded⟩, positive⟩
      · subst kind
        have guarded := accepted.2.2.1
        simp only [RawLaw.ClaimGuard, operation] at guarded
        exact ⟨accepted, goods, .maintenance, rfl, Or.inr ⟨rfl, guarded⟩, positive⟩
  | _ => simp only [operation] at paid

end AccessBasis

/-- The stronger productive-cycle checker feeds this access kernel by
forgetting profit and input-renewal observations, not by changing source. -/
def ofProductionProposal (proposal : CircuitProposal law current word) : AccessProposal law current word where
  access := proposal.production
  necessity := proposal.necessity
  mode := .acquired
  accessHolder := proposal.operator
  recipient := proposal.recipient
  port := proposal.port
  accessGood := proposal.outputGood
  necessityGood := proposal.necessityGood
  delivery := proposal.delivery

omit [DecidableEq Port] in
theorem production_checks_imply_access (proposal : CircuitProposal law current word)
    (checked : proposal.Checks law current word) :
    (ofProductionProposal law current word proposal).Checks law current word := by
  have produced := checked.1
  have need : (ofProductionProposal law current word proposal).RequiredUsePaid law current word := by
    have paid := checked.2.1
    unfold CircuitProposal.NecessityPaid at paid
    cases operation : proposal.necessity.val.request.operation with
    | use recipient goods kind =>
        cases kind <;> simp only [operation] at paid
        case necessity =>
          simp only [AccessProposal.RequiredUsePaid, ofProductionProposal, operation]
          exact ⟨paid.1, Or.inl trivial, paid.2.1, paid.2.2⟩
    | _ => simp only [operation] at paid
  unfold CircuitProposal.Produced at produced
  split at produced
  · exact ⟨produced.2.1, produced.2.2.1, checked.2.2.1, need,
      ⟨produced.2.2.2, checked.2.2.2.1⟩, checked.2.2.2.2.1⟩
  all_goals contradiction

#print axioms compileAccess
#print axioms AccessBasis.original_access_and_real_necessity

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel
