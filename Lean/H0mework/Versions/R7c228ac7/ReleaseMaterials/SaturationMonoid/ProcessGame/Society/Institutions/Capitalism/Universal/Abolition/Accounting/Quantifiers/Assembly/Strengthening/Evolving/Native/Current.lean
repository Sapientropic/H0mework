import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Rows.Sequential
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Rows.Birth
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Direct.Next
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Global.Capital

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Evolution

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

/-- Existing native source data with two original paid-row views. The world,
root, actor fold and account are those of the frame, not rebuilt here. -/
structure NativeCurrent : Type 4 where
  input : ProgrammeSource.Input Party Good Port Technology Instrument
  depth : Nat
  count : Nat
  prefixLimit : Nat
  renewalLimit : Nat
  oldPast : List (Compile.RawInput Party Good Port Technology Instrument)
  start : Physical.Cursor Party Good Port Technology Instrument
  frame : Public.NativeFrame input depth count prefixLimit renewalLimit oldPast start
  reader : Macro.Raw.Reader input depth count
  visit : SourceNativeTemporalVisitAt (Public.Inquiry.installedFrame frame reader).root.toAuthoritativeRoot.toLedgerRoot
  actual : Public.Inquiry.ActualAt frame visit.current
  bodyPaid : actual.actual.bodyPaid = true
  authority : SourceNativeLivingTemporalCausalEntryAuthorityAt (Public.Inquiry.installedFrame frame reader).root visit
    ((Public.Inquiry.installedFrame frame reader).entry visit.current)
  rows : PaidRowsAt frame.N (frame.sourceSupport visit.current)

namespace NativeCurrent
variable (current : NativeCurrent (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))

def full := Public.Inquiry.installedFrame current.frame current.reader

def erase : AnyAuthoritativeRootCurrent :=
  ⟨(full current).N,⟨(full current).V,(full current).root.toAuthoritativeRoot,current.visit⟩⟩

def sourceActual : Public.Inquiry.ActualAt (full current) current.visit.current :=
  ⟨current.actual.actual,current.actual.aligned⟩

def inquiry := Factory.Direct.presentation current.frame current.reader current.visit current.actual current.authority

theorem inquiry_is_the_current : (inquiry current).erase = erase current := rfl

def handlerLaw := Physical.Public.interpreter current.input

theorem the_actual_public_handler_excludes_every_capital_relation : Global.NoCapital (handlerLaw current) :=
  Global.publicLawNoCapital _

end NativeCurrent
end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving
