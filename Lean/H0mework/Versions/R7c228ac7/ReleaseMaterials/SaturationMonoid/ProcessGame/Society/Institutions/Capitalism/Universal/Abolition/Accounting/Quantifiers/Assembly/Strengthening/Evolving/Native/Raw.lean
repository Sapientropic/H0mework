import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Native.Current

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

variable (complete : ¬ Public.Inquiry.HasWork current.frame current.actual.actual)

def rawAction := Factory.Direct.rawCore current.frame current.reader current.visit current.actual current.authority complete

def raw : NativeCurrent (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) where
  input := current.input
  depth := current.depth
  count := current.count
  prefixLimit := current.prefixLimit
  renewalLimit := current.renewalLimit
  oldPast := current.oldPast
  start := Factory.Direct.selectedStart (full current) (sourceActual current) current.reader
  frame := Factory.Direct.recordedFrame (full current) (sourceActual current) current.reader
  reader := current.reader
  visit := Factory.Direct.nextVisit (full current) current.visit (sourceActual current) current.reader
  actual := Factory.Direct.nextActual (full current) current.visit (sourceActual current) current.reader
  bodyPaid := rfl
  authority := Factory.Direct.nextAuthorityForInstalledEntry (full current) current.visit (sourceActual current)
    current.reader complete current.authority
  rows := afterSequential (rawAction current complete) current.rows

theorem raw_is_the_same_actual_action_next :
    (raw current complete).erase =
      ⟨(full current).N,(rawAction current complete).target.targetAnswerAndNext.nextCurrent⟩ :=
  Factory.Direct.the_generated_body_returns_a_live_native_query (full current) current.visit
    (sourceActual current) current.reader complete current.authority

theorem raw_keeps_the_whole_original_native_account :
    (raw current complete).actual.actual.account = current.actual.actual.account := rfl

end NativeCurrent
end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving
