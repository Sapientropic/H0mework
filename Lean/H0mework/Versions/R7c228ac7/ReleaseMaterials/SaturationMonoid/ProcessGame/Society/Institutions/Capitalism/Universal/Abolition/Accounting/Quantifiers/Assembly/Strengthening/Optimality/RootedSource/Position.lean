import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.RootedSource.Canonical
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Action.Installed

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.RootedSource
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

/-- A view of the existing native root at its own actual visit; no extra row,
world or authority is admitted by this execution package. -/
structure Position (input : ProgrammeSource.Input Party Good Port Technology Instrument) : Type 4 where
  start : Physical.Cursor Party Good Port Technology Instrument
  frame : Public.NativeFrame input 0 0 0 0 [] start
  reader : Macro.Raw.Reader input 0 0
  visit : SourceNativeTemporalVisitAt (Public.Inquiry.installedFrame frame reader).root.toAuthoritativeRoot.toLedgerRoot
  actual : Public.Inquiry.ActualAt frame visit.current
  authority : SourceNativeLivingTemporalCausalEntryAuthorityAt (Public.Inquiry.installedFrame frame reader).root visit
    ((Public.Inquiry.installedFrame frame reader).entry visit.current)

namespace Position
variable {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  (current : Position input)

def full := Public.Inquiry.installedFrame current.frame current.reader
def inquiry := Evolution.Factory.Direct.presentation current.frame current.reader current.visit current.actual current.authority
def sourceActual : Public.Inquiry.ActualAt (full current) current.visit.current :=
  ⟨current.actual.actual,current.actual.aligned⟩

def native : Position input where
  start := current.start
  frame := current.frame
  reader := current.reader
  visit := Public.Accounting.Born.Action.nextVisit (full current) current.visit
  actual := ⟨Public.Accounting.nativeNext input 0 0 0 0 [] current.start current.actual.actual,
    current.frame.cursor_next current.visit.current current.actual.actual current.actual.aligned⟩
  authority := Public.Accounting.Born.Action.nextAuthorityForInstalledEntry (full current) current.visit current.authority

def raw (complete : ¬ Public.Inquiry.HasWork current.frame current.actual.actual) : Position input where
  start := Evolution.Factory.Direct.selectedStart (full current) (sourceActual current) current.reader
  frame := Evolution.Factory.Direct.recordedFrame (full current) (sourceActual current) current.reader
  reader := current.reader
  visit := Evolution.Factory.Direct.nextVisit (full current) current.visit (sourceActual current) current.reader
  actual := Evolution.Factory.Direct.nextActual (full current) current.visit (sourceActual current) current.reader
  authority := Evolution.Factory.Direct.nextAuthorityForInstalledEntry (full current) current.visit
    (sourceActual current) current.reader complete current.authority

def initial {world : WorldRelationNetwork} {anchor : (Epoch.Finance.process input 0 0).GeneratedState}
    (family : Epoch.Finance.Future.Continuation.AccountFamily input 0 0 world anchor)
    (start : Physical.Cursor Party Good Port Technology Instrument) (reader : Macro.Raw.Reader input 0 0) :
    Position input where
  start := start
  frame := Canonical.frame input family start
  reader := reader
  visit := Canonical.visit input family start
  actual := ⟨Public.Accounting.initial input 0 0 anchor,rfl⟩
  authority := (Canonical.authority input family start).withProjectionCoface
    (Public.Inquiry.component (Canonical.frame input family start) reader)

end Position
end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.RootedSource
