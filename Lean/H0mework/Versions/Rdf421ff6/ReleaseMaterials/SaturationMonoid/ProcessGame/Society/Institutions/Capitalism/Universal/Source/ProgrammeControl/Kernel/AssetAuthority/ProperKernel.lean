import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.AssetAuthority.Transfer
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.Discovery.Detector

/-! Proper capital control additionally requires separable authority over
its productive/access port.  The local quotation is raw source code, not a
capital-membership certificate.  The source compiler checks every guard. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.AssetAuthority

open Program
universe u
variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)
  (current : RawCurrent Party Good Technology Instrument)
  (word : RawEvent Party Good Port Technology Instrument)

structure ProperCapitalKernel where
  private mk ::
  dependency : CapitalRelationKernel law current word
  asset : AssetControlTransport law current word
  samePort : asset.proposal.port = dependency.proposal.access.port

/-- It is legal for title transfer to remain unexercised.  Actual access,
needed use and reciprocal contribution are still original executed items. -/
def compileProper (dependency : CapitalRelationKernel law current word)
    (position : OriginalItem law current word)
    (quotation : Request Party Good Port Technology Instrument) :
    Option (ProperCapitalKernel law current word) :=
  match compiled : compileTransfer law current word ⟨position, dependency.proposal.access.port, some quotation⟩ with
  | none => none
  | some asset => some ⟨dependency, asset,
      congrArg TransferProposal.port (compileTransfer_exact law current word _ asset compiled)⟩

theorem compileProper_dependency (dependency : CapitalRelationKernel law current word)
    (position : OriginalItem law current word)
    (quotation : Request Party Good Port Technology Instrument)
    (capital : ProperCapitalKernel law current word)
    (compiled : compileProper law current word dependency position quotation = some capital) :
    capital.dependency = dependency := by
  unfold compileProper at compiled
  split at compiled
  · contradiction
  · cases Option.some.inj compiled
    rfl

/-- This is a source-derived range, never a caller-supplied C-family.  A
membership witness contains the raw local quotation and its checked image. -/
def SourceGeneratedCapitalAt (port : Port) : Prop :=
  ∃ dependency : CapitalRelationKernel law current word,
    ∃ position : OriginalItem law current word,
      ∃ quotation : Request Party Good Port Technology Instrument,
        ∃ capital : ProperCapitalKernel law current word,
          compileProper law current word dependency position quotation = some capital ∧
            capital.dependency.proposal.access.port = port

omit [DecidableEq Port] in
theorem fixed_personal_authority_cannot_be_proper_capital (port : Port) (actor : Party)
    (fixed : ∀ technology, law.controller technology port = actor)
    (capital : ProperCapitalKernel law current word)
    (samePort : capital.dependency.proposal.access.port = port) : False :=
  invariant_actor_authority_has_no_asset_transport law current word port actor fixed capital.asset
    (capital.samePort.trans samePort)

#print axioms compileProper
#print axioms fixed_personal_authority_cannot_be_proper_capital

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.AssetAuthority
