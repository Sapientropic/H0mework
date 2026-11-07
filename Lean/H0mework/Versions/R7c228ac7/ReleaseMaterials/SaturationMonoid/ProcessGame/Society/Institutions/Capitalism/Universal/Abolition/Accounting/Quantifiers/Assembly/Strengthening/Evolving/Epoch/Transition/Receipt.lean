import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Transition.Next

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Transition

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution

noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (current : Current (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
  (complete : ¬ Public.Inquiry.HasWork current.native.frame current.native.actual.actual)

def returnedReport : Report current (current.native.actual.rawAnswer current.native.reader) :=
  (generated current complete).receipt.down

theorem the_actual_root_returns_its_original_input_choice_and_physical_verdict :
    (returnedReport current complete).proposal = current.proposal ∧
      (returnedReport current complete).choice = current.choice ∧
      (returnedReport current complete).physical = current.physicalResult :=
  ⟨(returnedReport current complete).proposal_eq,(returnedReport current complete).choice_eq,
    (returnedReport current complete).physical_eq⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Transition
