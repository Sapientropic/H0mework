import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.Core
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Power.ActionableFreedomChange

/-! Acting as oneself is not ownership of a transferable production right.
This face requires a real source update changing who holds the same port,
or a checked local alternative, with a genuine loss of the former holder's permission.  No new actor or
asset registry is introduced: the witness is an original instruction. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.AssetAuthority

open Program Power
universe u
variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)
  (current : RawCurrent Party Good Technology Instrument)
  (word : RawEvent Party Good Port Technology Instrument)

structure TransferProposal where
  instruction : OriginalItem law current word
  port : Port
  alternative : Option (Request Party Good Port Technology Instrument) := none

namespace TransferProposal
variable (proposal : TransferProposal law current word)

def request := proposal.alternative.getD proposal.instruction.val.request

def after := law.step proposal.instruction.val.before (proposal.request law current word)

def oldHolder := law.controller proposal.instruction.val.before.technology proposal.port

def newHolder := law.controller (proposal.after law current word).technology proposal.port

def IsRevision : Prop := match (proposal.request law current word).operation with
  | .revise _ _ => True
  | _ => False

instance : Decidable (proposal.IsRevision law current word) := by
  unfold IsRevision
  cases (proposal.request law current word).operation <;> infer_instance

def Checks : Prop :=
  proposal.IsRevision law current word ∧
  law.Valid proposal.instruction.val.before (proposal.request law current word) ∧
  proposal.port ∈ law.requiredPorts proposal.instruction.val.before (proposal.request law current word) ∧
  proposal.oldHolder law current word ≠ proposal.newHolder law current word ∧
  law.allowed proposal.instruction.val.before.technology proposal.port (proposal.oldHolder law current word) = true ∧
  law.allowed (proposal.after law current word).technology proposal.port (proposal.oldHolder law current word) = false ∧
  law.allowed (proposal.after law current word).technology proposal.port (proposal.newHolder law current word) = true

instance : Decidable (proposal.Checks law current word) := by unfold Checks; infer_instance
end TransferProposal

structure AssetControlTransport where
  private mk ::
  proposal : TransferProposal law current word
  checked : proposal.Checks law current word

def compileTransfer (proposal : TransferProposal law current word) :
    Option (AssetControlTransport law current word) :=
  if checked : proposal.Checks law current word then some ⟨proposal, checked⟩ else none

theorem compileTransfer_exact (proposal : TransferProposal law current word)
    (transport : AssetControlTransport law current word)
    (compiled : compileTransfer law current word proposal = some transport) :
    transport.proposal = proposal := by
  unfold compileTransfer at compiled
  split at compiled
  · cases Option.some.inj compiled
    rfl
  · contradiction

def transportsAt (port : Port) : List (AssetControlTransport law current word) :=
  (law.rawItems current word).attach.filterMap (fun item => compileTransfer law current word ⟨item, port, none⟩)

namespace AssetControlTransport
variable (transport : AssetControlTransport law current word)

omit [DecidableEq Port] in
theorem real_permission_changed :
    law.allowed transport.proposal.instruction.val.before.technology transport.proposal.port ≠
      law.allowed (transport.proposal.after law current word).technology transport.proposal.port := by
  intro same
  have old := transport.checked.2.2.2.2.1
  have lost := transport.checked.2.2.2.2.2.1
  rw [same] at old
  exact Bool.noConfusion (old.symm.trans lost)

/-- This actual action has its own signer.  Its identity is not replaced
by the newly generated holder of the relation. -/
def actualSigner := transport.proposal.instruction.val.request.signer
end AssetControlTransport

omit [DecidableEq Port] in
theorem invariant_actor_authority_has_no_asset_transport (port : Port) (actor : Party)
    (fixed : ∀ technology, law.controller technology port = actor)
    (transport : AssetControlTransport law current word)
    (samePort : transport.proposal.port = port) : False := by
  have distinct := transport.checked.2.2.2.1
  unfold TransferProposal.oldHolder TransferProposal.newHolder at distinct
  rw [samePort, fixed, fixed] at distinct
  exact distinct rfl

omit [DecidableEq Port] in
/-- With no way to represent a holder change, the coarse source has no
positive asset-separation witness.  This is not a claim about its intended
social interpretation. -/
theorem singleton_technology_has_no_asset_transport [Subsingleton Technology]
    (transport : AssetControlTransport law current word) : False := by
  have distinct := transport.checked.2.2.2.1
  unfold TransferProposal.oldHolder TransferProposal.newHolder at distinct
  have same := Subsingleton.elim transport.proposal.instruction.val.before.technology
    (transport.proposal.after law current word).technology
  exact distinct (congrArg (fun technology => law.controller technology transport.proposal.port) same)

#print axioms compileTransfer
#print axioms AssetControlTransport.real_permission_changed
#print axioms invariant_actor_authority_has_no_asset_transport

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.AssetAuthority
