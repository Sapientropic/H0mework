import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.Reciprocity
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.Disposal

/-! The constitutive kernel is actual controlled access, actual reverse
contribution/claim/payment and a source-executable disposition right.  Profit
and resource change are observations; neither is an admission condition. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel

open Program
universe u
variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)
  (current : RawCurrent Party Good Technology Instrument)
  (word : RawEvent Party Good Port Technology Instrument)

structure Proposal where
  access : AccessProposal law current word
  reciprocity : ReciprocityProposal law current word
  disposal : DisposalProposal law current word

namespace Proposal
variable (proposal : Proposal law current word)

def Checks : Prop := proposal.access.Checks law current word ∧
  proposal.reciprocity.Checks law current word proposal.access ∧
  proposal.disposal.Checks law current word proposal.access

instance : Decidable (proposal.Checks law current word) := by unfold Checks; infer_instance
end Proposal

structure CapitalRelationKernel where
  private mk ::
  proposal : Proposal law current word
  checked : proposal.Checks law current word

def compile (proposal : Proposal law current word) : Option (CapitalRelationKernel law current word) :=
  if checked : proposal.Checks law current word then some ⟨proposal, checked⟩ else none

namespace CapitalRelationKernel
variable (kernel : CapitalRelationKernel law current word)

def access : AccessBasis law current word :=
  (compileAccess law current word kernel.proposal.access).get
    (by simp [compileAccess, kernel.checked.1])

theorem access_proposal_exact : (kernel.access law current word).proposal = kernel.proposal.access := by
  simp [access, compileAccess, kernel.checked.1]

omit [DecidableEq Port] in
theorem original_control_and_reproduced_phase :
    law.Valid kernel.proposal.access.access.val.before kernel.proposal.access.access.val.request ∧
    kernel.proposal.access.port ∈ law.requiredPorts kernel.proposal.access.access.val.before
      kernel.proposal.access.access.val.request ∧
    PrivatePhase law kernel.proposal.access.access.val.before kernel.proposal.access.port kernel.proposal.access.recipient ∧
    PrivatePhase law (law.next current word) kernel.proposal.access.port kernel.proposal.access.recipient :=
  ⟨kernel.checked.1.1, kernel.checked.1.2.1,
    kernel.checked.1.2.2.1, kernel.checked.1.2.2.2.2.2⟩

omit [DecidableEq Port] in
theorem disposal_is_a_lawful_local_alternative :
    kernel.proposal.disposal.request.signer =
      kernel.proposal.disposal.holder law current word kernel.proposal.access ∧
    kernel.proposal.disposal.request.consents = [] ∧
    law.Valid kernel.proposal.disposal.position.val.before kernel.proposal.disposal.request :=
  ⟨kernel.checked.2.2.2.1, kernel.checked.2.2.2.2.1, kernel.checked.2.2.2.2.2.1⟩

def financialOrigin : Option (OriginalItem law current word) :=
  kernel.proposal.reciprocity.financialOrigin law current word
end CapitalRelationKernel

#print axioms compile
#print axioms CapitalRelationKernel.original_control_and_reproduced_phase
#print axioms CapitalRelationKernel.disposal_is_a_lawful_local_alternative

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel
