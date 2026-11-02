import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame.State
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Enactment.Admitted.Action
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Enactment.Inquiry.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {review : Option (ReviewPhase.ContextAt input)}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  {proposal : Compile.RawInput Party Good Port Technology Instrument} {sourcePosition : Nat}
  (package : Macro.Inquiry.Package (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
  (visit : SourceNativeTemporalVisitAt package.frame.root.toAuthoritativeRoot.toLedgerRoot)
  (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt package.frame.root visit (package.frame.entry visit.current))
  (germ : Macro.Raw.GermAt package.source package.sourceData package.reader visit.current)
  (admission : Abolition.Functions.Revision.InitialAdmissionAt
    (Abolition.Functions.Revision.Enactment.Inquiry.contextAt package visit authority germ))

local notation "context₀" => Abolition.Functions.Revision.Enactment.Inquiry.contextAt package visit authority germ

/-- Entry authority is transported from the existing package through the
actual enacted first write. The complete query root is already installed. -/
def initial : Frame context₀ admission := by
  let full := Abolition.Functions.Revision.Enactment.Admitted.frame context₀ admission
  let initialVisit := full.root.toAuthoritativeRoot.toRoot.initialVisit
  let selected := Abolition.Functions.Revision.Enactment.Admitted.generated context₀ admission
  have rowEq : selected.target.translatedSourceEntry = full.entry initialVisit.current := by
    apply Financial.Installation.entry_eq_of_key _ _
    · exact (Abolition.Functions.Revision.Enactment.Admitted.initial_ledger_preserves_every_original_row context₀ admission
        (Abolition.Functions.Revision.sourceEntry context₀)).1.trans
        ((package.familyEntryAligned visit.current germ.ready (package.source.sourceSupport visit.current)).trans
          ((Abolition.Functions.Revision.Enactment.Admitted.family context₀).entry_key _ _))
    · exact full.family.open_fibres _
  have initialAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt full.root (.finite initialVisit)
      (full.entry initialVisit.current) := rowEq ▸ selected.target.initialAuthority
  exact {
    start := Abolition.Functions.Revision.InitialAdmission.start admission
    reader := Abolition.Functions.Revision.InitialAdmission.reader admission
    source := Abolition.Functions.Revision.Enactment.Admitted.bareFrame context₀ admission
    visit := initialVisit.next (Abolition.Functions.Revision.Enactment.Admitted.firstSuccessor context₀ admission).next_eq
    actual := ⟨Abolition.Functions.Revision.Enactment.Admitted.bodyNext context₀,
      congrArg some (Abolition.Functions.Revision.Enactment.Admitted.first_successor_is_the_actual_public_body context₀ admission)⟩
    authority := Accounting.Born.Action.nextAuthorityForInstalledEntry full (.finite initialVisit) initialAuthority
    paid := rfl }

theorem initial_keeps_the_original_complete_account :
    (initial package visit authority germ admission).account = package.frame.account visit.current := rfl

#print axioms initial
#print axioms initial_keeps_the_original_complete_account

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame
