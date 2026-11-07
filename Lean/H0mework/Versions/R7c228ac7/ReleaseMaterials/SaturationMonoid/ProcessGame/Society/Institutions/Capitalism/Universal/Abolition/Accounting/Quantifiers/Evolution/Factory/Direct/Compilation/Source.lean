import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Inquiry.Faces.Installed
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Inquiry.Readback
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Action.Complete
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Direct.Authority

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Direct

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
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
  (reader : Macro.Raw.Reader input depth count)
  (visit : SourceNativeTemporalVisitAt (Public.Inquiry.installedFrame frame reader).root.toAuthoritativeRoot.toLedgerRoot)
  (atCurrent : Public.Inquiry.ActualAt frame visit.current)
  (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt (Public.Inquiry.installedFrame frame reader).root visit
    ((Public.Inquiry.installedFrame frame reader).entry visit.current))

local notation "full" => Public.Inquiry.installedFrame frame reader

def actualForInstalled : Public.Inquiry.ActualAt full visit.current := ⟨atCurrent.actual, atCurrent.aligned⟩

def debtCore (registered : Public.Accounting.Registration input depth count prefixLimit renewalLimit oldPast start atCurrent.actual) :=
  (Public.Accounting.Born.Action.completeProgram full visit atCurrent.actual atCurrent.aligned registered reader authority).generate
    ((full).root.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt visit)

def rawCore (complete : ¬ Public.Inquiry.HasWork frame atCurrent.actual) :=
  generated full visit (actualForInstalled frame reader visit atCurrent) reader complete
    ((full).entry visit.current) authority

def compileUnit : SourceNativeInquiryCompilationAt (full).root visit (full).basis.U7 (full).basis.calculus
    (full).root.toAuthoritativeRoot.source.lawSurface PUnit.unit
    (ULift.up.{1, 0} ((full).root.emitted visit.current)) ((full).entry visit.current) authority :=
  if work : Public.Inquiry.HasWork frame atCurrent.actual then
    match parsed : Public.Accounting.registration? input depth count prefixLimit renewalLimit oldPast start atCurrent.actual with
    | some registered => .debtAdmission (debtCore frame reader visit atCurrent authority registered)
    | none => .answered (Public.Inquiry.answerFace frame reader visit atCurrent work)
        (Public.Inquiry.consumer frame reader visit atCurrent work parsed)
  else .actualAction (rawCore frame reader visit atCurrent authority work)

theorem compileUnit_audit : (compileUnit frame reader visit atCurrent authority).audit = .answered := by
  unfold compileUnit
  split
  · split <;> rfl
  · rfl

private def AnswerCommutes
    (compiled : SourceNativeInquiryCompilationAt (full).root visit (full).basis.U7 (full).basis.calculus
      (full).root.toAuthoritativeRoot.source.lawSurface PUnit.unit
      (ULift.up.{1, 0} ((full).root.emitted visit.current)) ((full).entry visit.current) authority) : Prop :=
  HEq compiled.answerReadout (atCurrent.sourceAnswer reader)

theorem compileUnit_answer :
    HEq (compileUnit frame reader visit atCurrent authority).answerReadout (atCurrent.sourceAnswer reader) := by
  change AnswerCommutes frame reader visit atCurrent authority (compileUnit frame reader visit atCurrent authority)
  unfold compileUnit
  split
  · rename_i work
    split <;> exact (atCurrent.sourceAnswer_internal_heq reader work).symm
  · rename_i complete
    exact (atCurrent.sourceAnswer_raw_heq reader complete).symm

#print axioms compileUnit
#print axioms compileUnit_answer

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Direct
