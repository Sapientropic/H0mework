import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Source.Frame

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Source

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro

noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (native : NativeCurrent (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))

def originalState := Physical.Public.stateAt native.input native.depth native.count native.prefixLimit
  native.renewalLimit native.oldPast native.actual.snapshot.past

def initialValue := Control.fromState (originalState native)

def initialNative : NativeCurrent (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) where
  input := native.input
  depth := native.depth
  count := native.count
  prefixLimit := native.prefixLimit
  renewalLimit := native.renewalLimit
  oldPast := native.oldPast
  start := native.start
  frame := phaseFrame native.full (initialValue native)
  reader := native.reader
  visit := native.visit
  actual := ⟨native.actual.actual,native.actual.aligned⟩
  bodyPaid := native.bodyPaid
  authority := (native.authority.withProjectionCoface (component native.full (initialValue native))).withProjectionCoface
    (Public.Inquiry.component (phaseFrame native.full (initialValue native)) native.reader)
  rows := native.rows

def initial : Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) where
  native := initialNative native
  binding := {
    value := initialValue native
    faceAt := face native.full (initialValue native) native.reader
    typeAt := face_type native.full (initialValue native) native.reader
    readAt := face_reads native.full (initialValue native) native.reader }

theorem initial_raw_is_the_original_live_raw :
    (originalState (initialNative native)).raw = (originalState native).raw := rfl

theorem initial_native_account_is_literal :
    (initial native).native.actual.actual.account = native.actual.actual.account := rfl

theorem initial_source_phase_is_read_from_its_own_face :
    (initial native).control = Control.fromState (originalState native) :=
  (initial native).control_is_the_actual_root_coordinate

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Source
