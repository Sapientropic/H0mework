import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Source.Face

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Source

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro

noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit : Nat}
  {oldPast : List (Compile.RawInput Party Good Port Technology Instrument)}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  (frame : Public.NativeFrame input depth count prefixLimit renewalLimit oldPast start)
  (value : Control (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
  (reader : Macro.Raw.Reader input depth count)

def phaseFrame := frame.withProjectionCoface (component frame value)
def fullFrame := Public.Inquiry.installedFrame (phaseFrame frame value) reader

def face (visit : SourceNativeTemporalVisitAt (fullFrame frame value reader).root.toAuthoritativeRoot.toLedgerRoot)
    (actual : Public.Inquiry.ActualAt (phaseFrame frame value) visit.current) (paid : actual.actual.bodyPaid = true) :
    SourceNativeRootSemanticFaceAt (fullFrame frame value reader).root visit where
  projection := .inherited (.component PUnit.unit)
  active := ⟨⟨actual.actual,actual.aligned⟩,paid⟩
  classifier_eq := active_selected frame _ ⟨⟨actual.actual,actual.aligned⟩,paid⟩

theorem face_type (visit) (actual) (paid) :
    (face frame value reader visit actual paid).Restriction =
      Control (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) := rfl

theorem face_reads (visit) (actual) (paid) :
    cast (face_type frame value reader visit actual paid) (face frame value reader visit actual paid).rootRead = value := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Source
