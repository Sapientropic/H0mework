import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Programme.Realization
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Parameters

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Programme.Epoch
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (current : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

/-- Native heads have already executed their material body. Only the next
root-selected epoch body contributes a new physical submission. -/
def effective : Submission (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) :=
  if Public.Inquiry.HasWork current.native.frame current.native.actual.actual then []
  else [Public.Scope.executionRaw current.native.input current.native.depth current.native.count
    current.native.prefixLimit current.native.renewalLimit current.native.oldPast
    current.native.actual.snapshot current.executionRaw]

def materialItems : List (ExecutionItem Party Good Port Technology Instrument) :=
  if Public.Inquiry.HasWork current.native.frame current.native.actual.actual then []
  else current.physicalResult.execution.items

theorem the_epoch_physical_result_is_the_original_selected_compilation :
    current.physicalResult = Physical.Public.compile current.native.input
      (Evolving.Epoch.Source.originalState current.native)
      (Public.Scope.executionRaw current.native.input current.native.depth current.native.count
        current.native.prefixLimit current.native.renewalLimit current.native.oldPast
        current.native.actual.snapshot current.executionRaw) := rfl

theorem native_accounting_has_no_second_material_submission
    (work : Public.Inquiry.HasWork current.native.frame current.native.actual.actual) :
    effective current = [] ∧ materialItems current = [] := by
  simp [effective,materialItems,work]

theorem the_epoch_items_are_the_same_returned_actual_report
    (ready : ¬ Public.Inquiry.HasWork current.native.frame current.native.actual.actual) :
    materialItems current = (Evolving.Epoch.Transition.returnedReport current ready).physical.execution.items := by
  rw [materialItems,if_neg ready,
    (Evolving.Epoch.Transition.the_actual_root_returns_its_original_input_choice_and_physical_verdict current ready).2.2]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Programme.Epoch
