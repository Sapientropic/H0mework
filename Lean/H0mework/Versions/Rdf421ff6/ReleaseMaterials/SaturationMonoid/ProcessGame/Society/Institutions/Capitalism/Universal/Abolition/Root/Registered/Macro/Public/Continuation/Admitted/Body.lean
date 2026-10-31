import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Frame.Ordinary
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Inquiry.Readout
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.InitialAdmission.Origin

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Continuation.Admitted

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {review : Option (ReviewPhase.ContextAt input)}
  (origin : Abolition.Functions.Revision.Context (input := input) (review := review)
    depth count prefixLimit renewalLimit sourceDepth sourceCount)
  (admission : Abolition.Functions.Revision.InitialAdmissionAt origin)
  {oldPast : List (Compile.RawInput Party Good Port Technology Instrument)}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  (frame : NativeFrame input depth count prefixLimit renewalLimit oldPast start)
  {current : frame.V.Current} (atCurrent : Inquiry.ActualAt frame current)
  (reader : Macro.Raw.Reader input depth count)

abbrev family := frame.family.after atCurrent.actual.account atCurrent.actual.native
abbrev selectedStart := atCurrent.selectedCursor reader

def bareFrame : NativeFrame input depth count prefixLimit renewalLimit oldPast (selectedStart frame atCurrent reader) :=
  let base := Frame.ordinary input depth count prefixLimit renewalLimit oldPast
    (selectedStart frame atCurrent reader) (family frame atCurrent)
  base.withProjectionCoface (Abolition.Functions.Revision.InitialAdmission.originalComponent origin admission base.root)

abbrev bodyInitial := Accounting.initial input depth count atCurrent.actual.account
abbrev bodyNext := Accounting.bodyTarget input depth count atCurrent.actual.account

theorem initial_support_is_the_same_original_current :
    (bareFrame origin admission frame atCurrent reader).sourceSupport (bodyInitial frame atCurrent) =
      frame.sourceSupport current := by
  change (family frame atCurrent).currentSupport = frame.sourceSupport current
  exact (frame.support_exact current atCurrent.actual atCurrent.aligned).symm

theorem the_next_body_keeps_the_literal_complete_account :
    (bodyNext frame atCurrent).account = atCurrent.actual.account ∧
      (bodyNext frame atCurrent).position = 0 ∧ (bodyNext frame atCurrent).bodyPaid = true :=
  ⟨rfl, rfl, rfl⟩

theorem the_next_body_executes_the_selected_public_proposal :
    Accounting.physical input depth count prefixLimit renewalLimit oldPast
        (selectedStart frame atCurrent reader) (bodyNext frame atCurrent) =
      (Scope.actualResult input depth count prefixLimit renewalLimit oldPast atCurrent.snapshot
        (atCurrent.proposal reader)).next :=
  Physical.Public.consumed_input_generates_its_own_after input depth count prefixLimit renewalLimit oldPast
    (selectedStart frame atCurrent reader)

theorem the_new_source_does_not_reread_the_original_cut :
    Physical.Public.stateAt input depth count prefixLimit renewalLimit oldPast
        (selectedStart frame atCurrent reader).past =
      Physical.Public.stateAt input depth count prefixLimit renewalLimit oldPast atCurrent.snapshot.past := rfl

#print axioms bareFrame
#print axioms initial_support_is_the_same_original_current
#print axioms the_next_body_executes_the_selected_public_proposal

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Continuation.Admitted
