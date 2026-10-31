import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.RootedSource.Position

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.RootedSource
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
namespace Position
variable {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  (current : Position input)

theorem native_is_the_actual_root_resolution
    (work : Public.Inquiry.HasWork current.frame current.actual.actual)
    (absent : Public.Accounting.registration? input 0 0 0 0 [] current.start current.actual.actual = none) :
    current.native.inquiry.erase = (RootInquiryProcessNode.answered current.inquiry PUnit.unit).erase ∧
      (RootInquiryProcessNode.active current.inquiry).PreservesGeneratedLivingLawAt PUnit.unit
        (RootInquiryProcessNode.active current.native.inquiry) := by
  apply RootInquiryProcessNode.active_directlyAnswered_successor_valid current.inquiry current.native.inquiry PUnit.unit
    (Public.Inquiry.answerFace current.frame current.reader current.visit current.actual work)
    (Public.Inquiry.consumer current.frame current.reader current.visit current.actual work absent)
  · change Evolution.Factory.Direct.compileUnit current.frame current.reader current.visit current.actual current.authority = _
    rw [Evolution.Factory.Direct.compileUnit,dif_pos work]
    split
    · rename_i registered parsed
      cases parsed.symm.trans absent
    · rfl
  · exact congrArg (fun x => (⟨(full current).N,x⟩ : AnyAuthoritativeRootCurrent))
      (Registered.Macro.Ingress.next_is_the_same_generated_successor (full current).root current.visit
        ((full current).successor current.visit.current)).symm
  · exact HEq.rfl

theorem raw_is_the_actual_root_resolution
    (complete : ¬ Public.Inquiry.HasWork current.frame current.actual.actual) :
    (current.raw complete).inquiry.erase = (RootInquiryProcessNode.answered current.inquiry PUnit.unit).erase ∧
      (RootInquiryProcessNode.active current.inquiry).PreservesGeneratedLivingLawAt PUnit.unit
        (RootInquiryProcessNode.active (current.raw complete).inquiry) := by
  apply RootInquiryProcessNode.active_actualAction_successor_valid current.inquiry (current.raw complete).inquiry PUnit.unit
    (Evolution.Factory.Direct.rawCore current.frame current.reader current.visit current.actual current.authority complete)
  · change Evolution.Factory.Direct.compileUnit current.frame current.reader current.visit current.actual current.authority = _
    exact dif_neg complete
  · exact Evolution.Factory.Direct.the_generated_body_returns_a_live_native_query (full current) current.visit
      (sourceActual current) current.reader complete current.authority
  · exact HEq.rfl

end Position
end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.RootedSource
