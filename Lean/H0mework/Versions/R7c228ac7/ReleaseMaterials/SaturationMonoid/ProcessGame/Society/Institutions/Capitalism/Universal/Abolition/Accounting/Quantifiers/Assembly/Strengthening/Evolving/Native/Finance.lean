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


/-- This typed getter is the original generated finance state. It prevents
instance inference at a concrete evolving current from re-elaborating the
native occurrence factory merely to recover the accessor indices. -/
def nativeGS : (Epoch.Finance.process current.input current.depth current.count).GeneratedState :=
  current.actual.actual.account

theorem nativeGS_is_the_original_account : nativeGS current = current.actual.actual.account := rfl

theorem raw_next_keeps_the_literal_native_GS
    (complete : ¬ Public.Inquiry.HasWork current.frame current.actual.actual) :
    HEq (nativeGS (advance current)) (nativeGS current) := advance_raw_account_heq current complete

end NativeCurrent
end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving
