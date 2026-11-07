import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Resumption.Suffix.Frame
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Native.Source
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Public.Installation
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.TemporalMemory

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Resumption.Action

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root.Registered Abolition.Root.Registered.Macro

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit : Nat}
  {oldPast : List (Compile.RawInput Party Good Port Technology Instrument)}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  (frame : Abolition.Root.Registered.Macro.Public.NativeFrame input depth count prefixLimit renewalLimit oldPast start)
  (visit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot)
  (actual : Public.Inquiry.ActualAt frame visit.current)
  (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt frame.root visit (frame.entry visit.current))

def sourceContext := Ingress.Native.context frame visit actual (frame.entry visit.current) authority
def opened := Factory.Public.next (sourceContext frame visit actual authority)

variable (incoming : Context (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument) frame.N)

/-- The enacted event and all its old queries remain readable as actual past;
the suffix's original native query inventory remains dynamic. -/
def past : SourceNativeProjectionLaw
    (Suffix.nativeFrame frame visit.current).root.toAuthoritativeRoot.toLedgerRoot.source where
  Projection := incoming.root.source.base.projectionLaw.Projection
  ActiveAt := fun projection {_} _ => incoming.root.source.base.projectionLaw.ActiveAt projection
    (incoming.root.emitted incoming.visit.current)
  InactiveAt := fun projection {_} _ => incoming.root.source.base.projectionLaw.InactiveAt projection
    (incoming.root.emitted incoming.visit.current)
  classify := fun projection {_} _ => incoming.root.source.base.projectionLaw.classify projection
    (incoming.root.emitted incoming.visit.current)
  PayloadAt := fun projection {_} _ active => incoming.root.source.base.projectionLaw.PayloadAt projection
    (incoming.root.emitted incoming.visit.current) active
  project := fun projection {_} _ active => incoming.root.source.base.projectionLaw.project projection
    (incoming.root.emitted incoming.visit.current) active

def historyFrame := (Suffix.nativeFrame frame visit.current).withProjectionCoface (past frame visit incoming)

def registeredPast : SourceNativeProjectionLaw
    (historyFrame frame visit incoming).root.toAuthoritativeRoot.toLedgerRoot.source where
  Projection := PUnit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {_} _ _ => Sparse.TemporalMemory.View frame.root.toAuthoritativeRoot.toLedgerRoot
  project := fun _ {_} _ _ => Sparse.TemporalMemory.read _ visit

def bareFrame := (historyFrame frame visit incoming).withProjectionCoface (registeredPast frame visit incoming)

def fullFrame (reader : Macro.Raw.Reader input depth count) :=
  Public.Inquiry.installedFrame (bareFrame frame visit incoming) reader

def initialVisit (reader : Macro.Raw.Reader input depth count) :
    SourceNativeTemporalVisitAt (fullFrame frame visit incoming reader).root.toAuthoritativeRoot.toLedgerRoot :=
  .finite (fullFrame frame visit incoming reader).root.toAuthoritativeRoot.toRoot.initialVisit

theorem reentry_is_at_the_same_live_cursor (reader : Macro.Raw.Reader input depth count) :
    (fullFrame frame visit incoming reader).cursor
        (Sparse.Compiler.successor (Suffix.code frame visit.current) none).targetCurrent = some actual.actual :=
  (Suffix.after_ingress_the_native_cursor_is_the_original_cut frame visit.current).trans actual.aligned

theorem ingress_has_no_native_item_to_consume (reader : Macro.Raw.Reader input depth count) :
    (fullFrame frame visit incoming reader).cursor (initialVisit frame visit incoming reader).current = none := rfl

theorem native_query_uses_the_same_enacted_interpreter :
    Factory.Context.readLaw (opened frame visit actual authority) = Physical.Public.interpreter input := by
  exact (Factory.Public.next_reads_the_new_active_interpreter (sourceContext frame visit actual authority)).trans
    (by rw [Factory.Public.law,Factory.Context.readLaw_eq]; rfl)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Resumption.Action
