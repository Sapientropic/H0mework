import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Advance

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Current

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution

noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (current : Current (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))

private theorem ordinary_valid (work : Public.Inquiry.HasWork current.native.frame current.native.actual.actual)
    (absent : Public.Accounting.registration? current.native.input current.native.depth current.native.count current.native.prefixLimit
      current.native.renewalLimit current.native.oldPast current.native.start current.native.actual.actual = none) :
    current.ordinary.inquiry.erase = (RootInquiryProcessNode.answered current.inquiry PUnit.unit).erase ∧
      (RootInquiryProcessNode.active current.inquiry).PreservesGeneratedLivingLawAt PUnit.unit
        (RootInquiryProcessNode.active current.ordinary.inquiry) := by
  apply RootInquiryProcessNode.active_directlyAnswered_successor_valid current.inquiry current.ordinary.inquiry PUnit.unit
    (Public.Inquiry.answerFace current.native.frame current.native.reader current.native.visit current.native.actual work)
    (Public.Inquiry.consumer current.native.frame current.native.reader current.native.visit current.native.actual work absent)
  · change Compilation.compileUnit current = _
    rw [Compilation.compileUnit,dif_pos work]
    split
    · rename_i registered parsed
      cases parsed.symm.trans absent
    · rfl
  · exact congrArg (fun x => (⟨current.native.full.N,x⟩ : AnyAuthoritativeRootCurrent))
      (Ingress.next_is_the_same_generated_successor current.native.full.root current.native.visit
        (current.native.full.successor current.native.visit.current)).symm
  · exact HEq.rfl

private theorem birth_valid (work : Public.Inquiry.HasWork current.native.frame current.native.actual.actual)
    (registered : Public.Accounting.Registration current.native.input current.native.depth current.native.count current.native.prefixLimit
      current.native.renewalLimit current.native.oldPast current.native.start current.native.actual.actual)
    (present : Public.Accounting.registration? current.native.input current.native.depth current.native.count current.native.prefixLimit
      current.native.renewalLimit current.native.oldPast current.native.start current.native.actual.actual = some registered) :
    (current.birth registered).inquiry.erase = (RootInquiryProcessNode.answered current.inquiry PUnit.unit).erase ∧
      (RootInquiryProcessNode.active current.inquiry).PreservesGeneratedLivingLawAt PUnit.unit
        (RootInquiryProcessNode.active (current.birth registered).inquiry) := by
  apply RootInquiryProcessNode.active_debtAdmission_successor_valid current.inquiry (current.birth registered).inquiry PUnit.unit
    (current.native.birthAction registered)
  · change Compilation.compileUnit current = _
    rw [Compilation.compileUnit,dif_pos work]
    split
    · rename_i chosen parsed
      cases Option.some.inj (parsed.symm.trans present)
      rfl
    · rename_i parsed
      cases parsed.symm.trans present
  · exact current.native.birth_is_the_same_actual_admission_next registered
  · exact HEq.rfl

private theorem raw_valid (complete : ¬ Public.Inquiry.HasWork current.native.frame current.native.actual.actual) :
    (Transition.next current complete).inquiry.erase = (RootInquiryProcessNode.answered current.inquiry PUnit.unit).erase ∧
      (RootInquiryProcessNode.active current.inquiry).PreservesGeneratedLivingLawAt PUnit.unit
        (RootInquiryProcessNode.active (Transition.next current complete).inquiry) := by
  apply RootInquiryProcessNode.active_actualAction_successor_valid current.inquiry
    (Transition.next current complete).inquiry PUnit.unit (Transition.generated current complete)
  · change Compilation.compileUnit current = _
    exact dif_neg complete
  · exact congrArg (fun x => (⟨(Transition.generated current complete).target.TargetN,x⟩ : AnyAuthoritativeRootCurrent))
      (Transition.generated current complete).target.canonical_targetNextVisit_eq.symm
  · exact HEq.rfl

theorem advance_is_the_actual_root_successor :
    current.advance.inquiry.erase = (RootInquiryProcessNode.answered current.inquiry PUnit.unit).erase ∧
      (RootInquiryProcessNode.active current.inquiry).PreservesGeneratedLivingLawAt PUnit.unit
        (RootInquiryProcessNode.active current.advance.inquiry) := by
  unfold advance
  split
  · rename_i work
    split
    · rename_i registered present
      exact birth_valid current work registered present
    · rename_i absent
      exact ordinary_valid current work absent
  · rename_i complete
    exact raw_valid current complete

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Current
