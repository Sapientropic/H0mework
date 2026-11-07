import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Inquiry.Faces.Installed
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Inquiry.Readback
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Action.Complete
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Continuation.Admitted.Action

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Inquiry

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
  (reader : Macro.Raw.Reader input depth count)
  (visit : SourceNativeTemporalVisitAt (installedFrame frame reader).root.toAuthoritativeRoot.toLedgerRoot)
  (atCurrent : ActualAt frame visit.current)
  (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt (installedFrame frame reader).root visit
    ((installedFrame frame reader).entry visit.current))

local notation "full" => installedFrame frame reader

def actualForInstalled : ActualAt full visit.current := ⟨atCurrent.actual, atCurrent.aligned⟩

def debtCore (registered : Accounting.Registration input depth count prefixLimit renewalLimit oldPast start atCurrent.actual) :=
  (Accounting.Born.Action.completeProgram full visit atCurrent.actual atCurrent.aligned registered reader authority).generate
    ((full).root.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt visit)

def rawCore (complete : ¬ HasWork frame atCurrent.actual) :=
  Continuation.Admitted.generated origin admission full visit (actualForInstalled frame reader visit atCurrent) reader complete
    ((full).entry visit.current) authority

def compileUnit : SourceNativeInquiryCompilationAt (full).root visit (full).basis.U7 (full).basis.calculus
    (full).root.toAuthoritativeRoot.source.lawSurface PUnit.unit
    (ULift.up.{1, 0} ((full).root.emitted visit.current)) ((full).entry visit.current) authority :=
  if work : HasWork frame atCurrent.actual then
    match parsed : Accounting.registration? input depth count prefixLimit renewalLimit oldPast start atCurrent.actual with
    | some registered => .debtAdmission (debtCore frame reader visit atCurrent authority registered)
    | none => .answered (answerFace frame reader visit atCurrent work)
        (consumer frame reader visit atCurrent work parsed)
  else .actualAction (rawCore origin admission frame reader visit atCurrent authority work)

theorem compileUnit_audit : (compileUnit origin admission frame reader visit atCurrent authority).audit = .answered := by
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
    HEq (compileUnit origin admission frame reader visit atCurrent authority).answerReadout (atCurrent.sourceAnswer reader) := by
  change AnswerCommutes frame reader visit atCurrent authority (compileUnit origin admission frame reader visit atCurrent authority)
  unfold compileUnit
  split
  · rename_i work
    split <;> exact (atCurrent.sourceAnswer_internal_heq reader work).symm
  · rename_i complete
    exact (atCurrent.sourceAnswer_raw_heq reader complete).symm

#print axioms compileUnit
#print axioms compileUnit_answer

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Inquiry
