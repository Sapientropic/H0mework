import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Continuation.Admitted.Action

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
  (visit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot)
  (atCurrent : Inquiry.ActualAt frame visit.current)
  (reader : Macro.Raw.Reader input depth count)
  (complete : ¬ Inquiry.HasWork frame atCurrent.actual)
  (entry : OpenResponsibilityAt frame.N (frame.sourceSupport visit.current))
  (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt frame.root visit entry)

def originalRenewalReport : RenewalReport origin frame atCurrent :=
  (generated origin admission frame visit atCurrent reader complete entry authority).receipt.2.down

theorem the_actual_kernel_receipt_carries_the_complete_source_report :
    originalRenewalReport origin admission frame visit atCurrent reader complete entry authority =
      renewalReport origin frame atCurrent := rfl

#print axioms originalRenewalReport
#print axioms the_actual_kernel_receipt_carries_the_complete_source_report

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Continuation.Admitted
