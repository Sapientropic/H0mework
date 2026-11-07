import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame.Initial
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame.Query

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

theorem initial_erase : (initial package visit authority germ admission).presentation.erase =
    (⟨(Abolition.Functions.Revision.Enactment.Admitted.generated context₀ admission).target.TargetN,
      (Abolition.Functions.Revision.Enactment.Admitted.generated context₀ admission).target.targetAnswerAndNext.nextCurrent⟩ : AnyAuthoritativeRootCurrent) := by
  rw [(Abolition.Functions.Revision.Enactment.Admitted.generated context₀ admission).target.targetAnswerAndNext_next_eq]
  rfl

theorem initial_preserves_the_complete_target_living_root :
    HEq (initial package visit authority germ admission).presentation.state.base.root
      (Abolition.Functions.Revision.Enactment.Admitted.generated context₀ admission).target.targetRoot := HEq.rfl

#print axioms initial_erase
#print axioms initial_preserves_the_complete_target_living_root

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame
