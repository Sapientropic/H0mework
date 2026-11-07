import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Commands.ReviewKernel
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Commands.Metadata

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Current

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution

noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (current : Current (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
  (reviewCode : ReviewSource.Control.Code Party Good Port Technology Instrument)
  (source : current.proposal = .review reviewCode)
  (unregistered : current.control.review = none)
  (admitted : boundary (Public.Scope.checkInput current.native.input)
    (Actual.origin current.native.input current.native.depth current.native.count) current.members
    current.native.depth current.native.count current.native.prefixLimit current.native.renewalLimit current.state)

include source unregistered admitted in
theorem review_execution_is_the_original_registration : current.executionRaw = .review reviewCode := by
  unfold executionRaw choice
  rw [source]
  exact ReviewKernel.executionRaw _ _ _ _ _ _ _ _ _ _ unregistered admitted

include source unregistered admitted in
theorem review_installs_only_the_original_finite_code : current.afterControl =
    {current.control with review := some (ReviewCursor.initial reviewCode current.native.prefixLimit current.native.renewalLimit)} := by
  unfold afterControl choice
  rw [source]
  exact ReviewKernel.controlAfter _ _ _ _ _ _ _ _ _ _ unregistered admitted _ _

include source unregistered admitted in
theorem review_registration_has_no_material_items : current.physicalResult.execution.items = [] := by
  rw [physicalResult,review_execution_is_the_original_registration current reviewCode source unregistered admitted]
  rfl

variable (complete : ¬ Public.Inquiry.HasWork current.native.frame current.native.actual.actual)
include source unregistered admitted in
theorem the_actual_review_registration_is_ready_for_its_own_next_query :
    ¬ Public.Inquiry.HasWork (Transition.next current complete).native.frame
      (Transition.next current complete).native.actual.actual :=
  current.an_empty_actual_body_has_no_native_head complete
    (review_registration_has_no_material_items current reviewCode source unregistered admitted)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Current
