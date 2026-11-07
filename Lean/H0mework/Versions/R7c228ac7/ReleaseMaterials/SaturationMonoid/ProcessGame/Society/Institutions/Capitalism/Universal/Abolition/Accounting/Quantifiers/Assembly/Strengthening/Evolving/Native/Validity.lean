import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Native.Selection

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution

noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (current : NativeCurrent (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

namespace NativeCurrent


private theorem ordinary_valid
    (work : Public.Inquiry.HasWork current.frame current.actual.actual)
    (absent : Public.Accounting.registration? current.input current.depth current.count current.prefixLimit
      current.renewalLimit current.oldPast current.start current.actual.actual = none) :
    (ordinary current).inquiry.erase =
        (RootInquiryProcessNode.answered current.inquiry PUnit.unit).erase ∧
      (RootInquiryProcessNode.active current.inquiry).PreservesGeneratedLivingLawAt PUnit.unit
        (RootInquiryProcessNode.active (ordinary current).inquiry) := by
  apply RootInquiryProcessNode.active_directlyAnswered_successor_valid current.inquiry (ordinary current).inquiry PUnit.unit
    (Public.Inquiry.answerFace current.frame current.reader current.visit current.actual work)
    (Public.Inquiry.consumer current.frame current.reader current.visit current.actual work absent)
  · change Factory.Direct.compileUnit current.frame current.reader current.visit current.actual current.authority = _
    rw [Factory.Direct.compileUnit,dif_pos work]
    split
    · rename_i registered parsed
      cases parsed.symm.trans absent
    · rfl
  · exact congrArg (fun x => (⟨(full current).N,x⟩ : AnyAuthoritativeRootCurrent))
      (Registered.Macro.Ingress.next_is_the_same_generated_successor (full current).root current.visit
        ((full current).successor current.visit.current)).symm
  · exact HEq.rfl

private theorem raw_valid (complete : ¬ Public.Inquiry.HasWork current.frame current.actual.actual) :
    (raw current complete).inquiry.erase =
        (RootInquiryProcessNode.answered current.inquiry PUnit.unit).erase ∧
      (RootInquiryProcessNode.active current.inquiry).PreservesGeneratedLivingLawAt PUnit.unit
        (RootInquiryProcessNode.active (raw current complete).inquiry) := by
  apply RootInquiryProcessNode.active_actualAction_successor_valid current.inquiry (raw current complete).inquiry PUnit.unit
    (rawAction current complete)
  · change Factory.Direct.compileUnit current.frame current.reader current.visit current.actual current.authority = _
    exact dif_neg complete
  · exact raw_is_the_same_actual_action_next current complete
  · exact HEq.rfl

private theorem birth_valid (work : Public.Inquiry.HasWork current.frame current.actual.actual)
    (registered : Public.Accounting.Registration current.input current.depth current.count current.prefixLimit
      current.renewalLimit current.oldPast current.start current.actual.actual)
    (present : Public.Accounting.registration? current.input current.depth current.count current.prefixLimit
      current.renewalLimit current.oldPast current.start current.actual.actual = some registered) :
    (birth current registered).inquiry.erase =
        (RootInquiryProcessNode.answered current.inquiry PUnit.unit).erase ∧
      (RootInquiryProcessNode.active current.inquiry).PreservesGeneratedLivingLawAt PUnit.unit
        (RootInquiryProcessNode.active (birth current registered).inquiry) := by
  apply RootInquiryProcessNode.active_debtAdmission_successor_valid current.inquiry (birth current registered).inquiry PUnit.unit
    (birthAction current registered)
  · change Factory.Direct.compileUnit current.frame current.reader current.visit current.actual current.authority = _
    rw [Factory.Direct.compileUnit,dif_pos work]
    split
    · rename_i chosen parsed
      cases Option.some.inj (parsed.symm.trans present)
      rfl
    · rename_i parsed
      cases parsed.symm.trans present
  · exact birth_is_the_same_actual_admission_next current registered
  · exact HEq.rfl

/-- The recursive interface is exactly the root resolver's generated current
and living law, including the type-changing native birth branch. -/
theorem advance_is_the_actual_source_successor :
    (advance current).inquiry.erase =
        (RootInquiryProcessNode.answered current.inquiry PUnit.unit).erase ∧
      (RootInquiryProcessNode.active current.inquiry).PreservesGeneratedLivingLawAt PUnit.unit
        (RootInquiryProcessNode.active (advance current).inquiry) := by
  unfold advance selected
  split
  · rename_i work
    split
    · rename_i registered present
      exact birth_valid current work registered present
    · rename_i absent
      exact ordinary_valid current work absent
  · rename_i complete
    exact raw_valid current complete

end NativeCurrent
end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving
