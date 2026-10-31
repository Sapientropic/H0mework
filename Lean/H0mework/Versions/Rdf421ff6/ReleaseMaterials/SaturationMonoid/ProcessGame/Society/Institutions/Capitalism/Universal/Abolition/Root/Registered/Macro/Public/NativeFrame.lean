import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Source.Readback
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Inquiry.Foundation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

private theorem target_emitted {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
    {source : SourceNativeSource N V} {current : V.Current}
    (emit : (state : V.Current) → source.toRootSource.actual.OccurrenceAt state)
    {occurrence : source.toRootSource.actual.OccurrenceAt current}
    (generated : SourceNativeLedgerEvolutionAt source occurrence)
    (successor : SourceNativeLedgerGeneratedSuccessorAt occurrence generated)
    (commutes : generated.CommutesWith emit) :
    successor.targetOccurrence = emit successor.targetCurrent := by
  cases generated <;> first | exact commutes | exact successor.elim

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (oldPast : List (Compile.RawInput Party Good Port Technology Instrument))
  (start : Physical.Cursor Party Good Port Technology Instrument)

structure NativeFrame where
  N : WorldRelationNetwork
  anchor : (Epoch.Finance.process input depth count).GeneratedState
  family : Epoch.Finance.Future.Continuation.AccountFamily input depth count N anchor
  V : ConstructiveRoot.Vocabulary
  root : SourceNativeLivingRootClosure N V
  occurrence_eq_emitted : ∀ {current : V.Current}
    (occurrence : root.toAuthoritativeRoot.toRoot.actual.OccurrenceAt current), occurrence = root.emitted current
  cursor : V.Current → Option (Accounting.Current input depth count anchor)
  support_exact : ∀ current actual, cursor current = some actual →
    root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf (root.emitted current) =
      Accounting.support input depth count family actual
  successor : (current : V.Current) → SourceNativeLedgerGeneratedSuccessorAt
    (root.emitted current) (root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current)
  cursor_next : ∀ current actual, cursor current = some actual →
    cursor (successor current).targetCurrent =
      some (Accounting.nativeNext input depth count prefixLimit renewalLimit oldPast start actual)
  successor_destination : ∀ current actual, cursor current = some actual →
    HEq (successor current).ledgerEvolution.destination
      (Accounting.nativeEvolution input depth count prefixLimit renewalLimit oldPast start family actual).destination
  entries_finite : ∀ current, Finite (OpenResponsibilityAt N
    (root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf (root.emitted current)))
  successor_keys : ∀ current, Financial.Installation.KeepsKeys (successor current).ledgerEvolution

namespace NativeFrame

variable {input depth count prefixLimit renewalLimit oldPast start}
  (frame : NativeFrame input depth count prefixLimit renewalLimit oldPast start)

def sourceSupport (current : frame.V.Current) :=
  frame.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf (frame.root.emitted current)

theorem target_occurrence (current : frame.V.Current) :
    (frame.successor current).targetOccurrence = frame.root.emitted (frame.successor current).targetCurrent :=
  target_emitted frame.root.emitted _ _ (frame.root.compiler_commutes current)

def entry (current : frame.V.Current) := frame.family.entry (frame.sourceSupport current)

def basis : Macro.Inquiry.Basis frame.N where
  entry := frame.family.entry
  disposition := frame.family.disposition

def withProjectionCoface
    (component : SourceNativeProjectionLaw frame.root.toAuthoritativeRoot.toLedgerRoot.source) :
    NativeFrame input depth count prefixLimit renewalLimit oldPast start where
  N := frame.N
  anchor := frame.anchor
  family := frame.family
  V := frame.V
  root := frame.root.withProjectionCoface component
  occurrence_eq_emitted := frame.occurrence_eq_emitted
  cursor := frame.cursor
  support_exact := frame.support_exact
  successor := frame.successor
  cursor_next := frame.cursor_next
  successor_destination := frame.successor_destination
  entries_finite := frame.entries_finite
  successor_keys := frame.successor_keys

end NativeFrame

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public
