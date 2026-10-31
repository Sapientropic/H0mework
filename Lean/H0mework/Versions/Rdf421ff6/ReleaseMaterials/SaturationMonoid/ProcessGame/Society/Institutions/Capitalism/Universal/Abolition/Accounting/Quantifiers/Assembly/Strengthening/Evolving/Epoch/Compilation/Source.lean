import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Transition.Next
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Native

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Compilation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution

noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (current : Current (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))

local notation "full" => current.native.full

def compileUnit : SourceNativeInquiryCompilationAt (full).root current.native.visit (full).basis.U7 (full).basis.calculus
    (full).root.toAuthoritativeRoot.source.lawSurface PUnit.unit
    (ULift.up.{1,0} ((full).root.emitted current.native.visit.current)) ((full).entry current.native.visit.current) current.native.authority :=
  if work : Public.Inquiry.HasWork current.native.frame current.native.actual.actual then
    match parsed : Public.Accounting.registration? current.native.input current.native.depth current.native.count current.native.prefixLimit
        current.native.renewalLimit current.native.oldPast current.native.start current.native.actual.actual with
    | some registered => .debtAdmission (current.native.birthAction registered)
    | none => .answered (Public.Inquiry.answerFace current.native.frame current.native.reader current.native.visit current.native.actual work)
        (Public.Inquiry.consumer current.native.frame current.native.reader current.native.visit current.native.actual work parsed)
  else .actualAction (Transition.generated current work)

theorem compileUnit_audit : (compileUnit current).audit = .answered := by
  unfold compileUnit
  split
  · split <;> rfl
  · rfl

private def AnswerCommutes (compiled : SourceNativeInquiryCompilationAt (full).root current.native.visit (full).basis.U7 (full).basis.calculus
    (full).root.toAuthoritativeRoot.source.lawSurface PUnit.unit
    (ULift.up.{1,0} ((full).root.emitted current.native.visit.current)) ((full).entry current.native.visit.current) current.native.authority) : Prop :=
  HEq compiled.answerReadout (current.native.actual.sourceAnswer current.native.reader)

theorem compileUnit_answer : HEq (compileUnit current).answerReadout (current.native.actual.sourceAnswer current.native.reader) := by
  change AnswerCommutes current (compileUnit current)
  unfold compileUnit
  split
  · rename_i work
    split <;> exact (current.native.actual.sourceAnswer_internal_heq current.native.reader work).symm
  · rename_i complete
    exact (current.native.actual.sourceAnswer_raw_heq current.native.reader complete).symm

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Compilation
