import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Inquiry.Faces.Component

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Inquiry

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit : Nat}
  {oldPast : List (Compile.RawInput Party Good Port Technology Instrument)}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  (frame : NativeFrame input depth count prefixLimit renewalLimit oldPast start)

variable (reader : Macro.Raw.Reader input depth count)
  (visit : SourceNativeTemporalVisitAt (installedFrame frame reader).root.toAuthoritativeRoot.toLedgerRoot)
  (atCurrent : ActualAt frame visit.current)

def registeredInput : SourceNativeRootInquiryInputAt (installedFrame frame reader).root visit PUnit where
  projection := (installation frame reader).embed .query
  active := atCurrent
  classifier_eq := the_unique_source_active_is_selected frame .query _ atCurrent
  queryType_eq := rfl

def answerFace (work : HasWork frame atCurrent.actual) :
    SourceNativeRootSemanticFaceAt (installedFrame frame reader).root visit where
  projection := (installation frame reader).embed .answer
  active := ⟨atCurrent, work⟩
  classifier_eq := the_unique_source_active_is_selected frame .answer _ ⟨atCurrent, work⟩

def consumer (work : HasWork frame atCurrent.actual)
    (ordinary : Accounting.registration? input depth count prefixLimit renewalLimit oldPast start atCurrent.actual = none) :
    SourceNativeInquiryAnswerConsumerAt PUnit.unit
      (ULift.up.{1, 0} ((installedFrame frame reader).root.emitted visit.current))
      ((installedFrame frame reader).entry visit.current) (answerFace frame reader visit atCurrent work) where
  projection := (installation frame reader).embed .consumer
  active := ⟨atCurrent, work, ordinary⟩
  classifier_eq := the_unique_source_active_is_selected frame .consumer _ ⟨atCurrent, work, ordinary⟩
  project_heq := HEq.rfl

#print axioms registeredInput
#print axioms consumer

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Inquiry
