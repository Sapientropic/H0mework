import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Root.Installation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Root

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Source.Program Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)} {oldN : WorldRelationNetwork}
  (claim : Responsibility.Family.Claim mechanism past nature response)
  (frame : Abolition.Accounting.Root.Reentry.Frame (oldN := oldN) claim)
  (proposal : RawEvent Party Good Port Technology Instrument)

/-- Necessity and maintenance remain independently visible even when the
first refusal was a different request, such as an unpaid financial claim. -/
def successorNeedsFace : SourceNativeRootSemanticFaceAt
    (Installation.successor claim frame proposal).root (Installation.successor claim frame proposal).visit where
  projection := .component Abolition.Accounting.Root.Reentry.Report.needs
  active := PUnit.unit
  classifier_eq := rfl

theorem the_next_need_face_retains_the_actual_original_bearers :
    HEq (successorNeedsFace claim frame proposal).rootRead
      (Responsibility.Family.inspectActualNeeds claim
        (Abolition.Accounting.Root.Reentry.Frame.state claim frame) frame.actualLaw
        (Gate.executableWord claim frame proposal) frame.members) := HEq.rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Root
