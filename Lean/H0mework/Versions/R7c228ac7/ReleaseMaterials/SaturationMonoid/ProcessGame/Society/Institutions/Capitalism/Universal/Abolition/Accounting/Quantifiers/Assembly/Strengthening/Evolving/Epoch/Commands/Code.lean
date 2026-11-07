import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Commands.Metadata
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Commands.CodeKernel

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Current

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution

noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (current : Current (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
  (submission : Actual.Submission Party Good Port Technology Instrument)
  (source : current.proposal = .code submission)
  (unregistered : current.control.review = none)
  (admitted : boundary (Public.Scope.checkInput current.native.input)
    (Actual.origin current.native.input current.native.depth current.native.count) current.members
    current.native.depth current.native.count current.native.prefixLimit current.native.renewalLimit current.state)

include source unregistered admitted in
theorem code_execution_is_the_original_registration : current.executionRaw = .code submission := by
  unfold executionRaw choice
  rw [source]
  exact CodeKernel.executionRaw _ _ _ _ _ _ _ _ _ _ unregistered admitted

include source unregistered admitted in
theorem code_changes_the_original_phase_and_remaining :
    current.afterControl = ⟨.seeking,submission.requests,none⟩ := by
  unfold afterControl choice
  rw [source]
  exact CodeKernel.controlAfter _ _ _ _ _ _ _ _ _ _ unregistered admitted _ _

include source unregistered admitted in
theorem the_code_write_is_not_a_material_payment : current.physicalResult.next.raw = current.raw := by
  rw [physicalResult,code_execution_is_the_original_registration current submission source unregistered admitted]
  rfl

include source unregistered admitted in
theorem code_registration_has_no_material_items : current.physicalResult.execution.items = [] := by
  rw [physicalResult,code_execution_is_the_original_registration current submission source unregistered admitted]
  rfl

variable (complete : ¬ Public.Inquiry.HasWork current.native.frame current.native.actual.actual)
include source unregistered admitted in
theorem the_actual_code_successor_reads_the_new_programme :
    (Transition.next current complete).control = ⟨.seeking,submission.requests,none⟩ ∧
      (Transition.next current complete).raw = current.raw :=
  ⟨(Transition.next_reads_the_written_control current complete).trans
      (code_changes_the_original_phase_and_remaining current submission source unregistered admitted),
    (Transition.next_state_reads_the_same_actual_material_target current complete).trans
      (the_code_write_is_not_a_material_payment current submission source unregistered admitted)⟩

include source unregistered admitted in
theorem the_actual_code_registration_is_ready_for_its_own_next_query :
    ¬ Public.Inquiry.HasWork (Transition.next current complete).native.frame
      (Transition.next current complete).native.actual.actual :=
  current.an_empty_actual_body_has_no_native_head complete
    (code_registration_has_no_material_items current submission source unregistered admitted)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Current
