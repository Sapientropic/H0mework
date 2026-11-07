import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.AfterNative.Raw
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing.Run

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.AfterNative

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution

noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument} {depth count boundary : Nat}
  {plan : RawEvent Party Good Port Technology Instrument} {fallback : Macro.Raw.Reader input depth count}

/-- Only the already-generated clearing schedule advances. The source
control restriction travels through its literal raw/ordinary transitions. -/
def run : (remaining : RawEvent Party Good Port Technology Instrument) →
    (source : Clearing.Schedule input depth count boundary plan fallback remaining) →
    Binding source.position.native →
    Current (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)
  | [], source, binding => ⟨source.position.native,binding⟩
  | _ :: tail, source, binding =>
      let current : Current (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) :=
        ⟨source.position.native,binding⟩
      run tail source.next (current.afterNativePrimitive source.position.ready).binding

theorem run_native (remaining : RawEvent Party Good Port Technology Instrument)
    (source : Clearing.Schedule input depth count boundary plan fallback remaining) (binding : Binding source.position.native) :
    (run remaining source binding).native = (Clearing.Schedule.run remaining source).native := by
  induction remaining with
  | nil => rfl
  | cons request tail induction => exact induction source.next _

theorem run_control (remaining : RawEvent Party Good Port Technology Instrument)
    (source : Clearing.Schedule input depth count boundary plan fallback remaining) (binding : Binding source.position.native) :
    (run remaining source binding).control = binding.value := by
  induction remaining with
  | nil => exact (run [] source binding).control_is_the_actual_root_coordinate
  | cons request tail induction => exact induction source.next _

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.AfterNative
