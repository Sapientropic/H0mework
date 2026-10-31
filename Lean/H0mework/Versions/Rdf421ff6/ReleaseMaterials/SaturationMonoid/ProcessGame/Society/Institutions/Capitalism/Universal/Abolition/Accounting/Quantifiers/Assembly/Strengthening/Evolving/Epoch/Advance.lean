import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Compilation.State

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Current

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution

noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (current : Current (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))

def advance : Current (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) :=
  if work : Public.Inquiry.HasWork current.native.frame current.native.actual.actual then
    match Public.Accounting.registration? current.native.input current.native.depth current.native.count current.native.prefixLimit
        current.native.renewalLimit current.native.oldPast current.native.start current.native.actual.actual with
    | some registered => current.birth registered
    | none => current.ordinary
  else Transition.next current work

def inquiry := Compilation.presentation current

theorem advance_eq_epoch (complete : ¬ Public.Inquiry.HasWork current.native.frame current.native.actual.actual) :
    current.advance = Transition.next current complete := by
  unfold advance
  rw [dif_neg complete]

theorem the_unconsumed_source_phase_is_not_reset_by_ordinary_accounting :
    current.ordinary.control = current.control := by
  rw [control_is_the_actual_root_coordinate,control_is_the_actual_root_coordinate]
  rfl

theorem native_birth_keeps_the_same_source_phase
    (registered : Public.Accounting.Registration current.native.input current.native.depth current.native.count current.native.prefixLimit
      current.native.renewalLimit current.native.oldPast current.native.start current.native.actual.actual) :
    (current.birth registered).control = current.control := by
  rw [control_is_the_actual_root_coordinate,control_is_the_actual_root_coordinate]
  rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Current
