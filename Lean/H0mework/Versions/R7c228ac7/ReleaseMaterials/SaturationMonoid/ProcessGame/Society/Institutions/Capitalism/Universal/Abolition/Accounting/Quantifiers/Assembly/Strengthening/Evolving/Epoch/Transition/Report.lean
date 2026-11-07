import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Transition.Frame

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Transition

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution

noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (current : Current (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
  (answer : current.native.actual.RawAnswer current.native.reader)

/-- The rooted action returns the original proposal, complete typed choice
and physical verdict. Failed migration/fee effects remain visible here. -/
structure Report where
  proposal : Compile.RawInput Party Good Port Technology Instrument
  proposal_eq : proposal = current.proposal
  choice : type_of% (current.choice)
  choice_eq : choice = current.choice
  physical : type_of% (current.physicalResult)
  physical_eq : physical = current.physicalResult
  actualBody : Public.Accounting.physical current.native.input current.native.depth current.native.count current.native.prefixLimit
    current.native.renewalLimit current.native.oldPast
    (Factory.Direct.selectedStart current.native.full current.native.sourceActual current.executionReader)
    (actual current).actual = physical.next
  bodyNext : (first current).targetCurrent = Factory.Direct.bodyNext current.native.full current.native.sourceActual
  accountKept : (actual current).actual.account = current.native.actual.actual.account
  answer_eq : answer = current.native.actual.rawAnswer current.native.reader

def report : Report current (current.native.actual.rawAnswer current.native.reader) :=
  ⟨current.proposal,rfl,current.choice,rfl,current.physicalResult,rfl,
    the_material_target_is_the_same_actual_public_result current,first_is_the_literal_body current,rfl,rfl⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Transition
