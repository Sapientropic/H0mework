import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Direct.Ledger
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.TemporalMemory

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Direct

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit : Nat}
  {oldPast : List (Compile.RawInput Party Good Port Technology Instrument)}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  (frame : Public.NativeFrame input depth count prefixLimit renewalLimit oldPast start)
  {visit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot}
  (atCurrent : Public.Inquiry.ActualAt frame visit.current)
  (reader : Macro.Raw.Reader input depth count)

def past : SourceNativeProjectionLaw (bareFrame frame atCurrent reader).root.toAuthoritativeRoot.toLedgerRoot.source where
  Projection := PUnit
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun _ {_} _ _ => Sparse.TemporalMemory.View frame.root.toAuthoritativeRoot.toLedgerRoot
  project := fun _ {_} _ _ => Sparse.TemporalMemory.read frame.root.toAuthoritativeRoot.toLedgerRoot visit

def recordedFrame := (bareFrame frame atCurrent reader).withProjectionCoface (past frame atCurrent reader)
def targetFrame := Public.Inquiry.installedFrame (recordedFrame frame atCurrent reader) reader
abbrev targetRoot := (targetFrame frame atCurrent reader).root
abbrev targetInitial := (targetRoot frame atCurrent reader).toAuthoritativeRoot.toRoot.initialVisit

def firstSuccessor := (targetFrame frame atCurrent reader).successor (targetInitial frame atCurrent reader).current

theorem first_target_is_the_actual_selected_body :
    (firstSuccessor frame atCurrent reader).targetCurrent = bodyNext frame atCurrent :=
  Public.Source.successor_current input depth count prefixLimit renewalLimit oldPast
    (selectedStart frame atCurrent reader) (family frame atCurrent) (bodyInitial frame atCurrent)

theorem the_target_starts_with_the_same_whole_source_support :
    (targetFrame frame atCurrent reader).sourceSupport (targetInitial frame atCurrent reader).current =
      frame.sourceSupport visit.current := initial_support_is_the_actual_current frame atCurrent reader

def oldProjection (projection : frame.root.source.base.projectionLaw.Projection) :
    (targetRoot frame atCurrent reader).source.base.projectionLaw.Projection :=
  .inherited (.inherited (.component projection))

theorem every_target_preserves_every_original_query {current : (targetFrame frame atCurrent reader).V.Current}
    (occurrence : (targetRoot frame atCurrent reader).toAuthoritativeRoot.toRoot.actual.OccurrenceAt current)
    (projection : frame.root.source.base.projectionLaw.Projection) :
    HEq ((targetRoot frame atCurrent reader).source.base.projectionLaw.outcomeAt
        (oldProjection frame atCurrent reader projection) occurrence)
      (frame.root.source.base.projectionLaw.outcomeAt projection (frame.root.emitted visit.current)) := by
  have outer := (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (recordedFrame frame atCurrent reader).root.source.base
    (Public.Inquiry.component (recordedFrame frame atCurrent reader) reader)).outcome_heq occurrence
      (.inherited (.component projection))
  have middle := (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (bareFrame frame atCurrent reader).root.source.base (past frame atCurrent reader)).outcome_heq occurrence
      (.component projection)
  have inner := (SourceNativeProjectionLaw.InstallationAt.componentCoface
    (ordinary frame atCurrent reader).root.source.base (history frame atCurrent reader)).outcome_heq occurrence projection
  exact outer.trans (middle.trans (inner.trans
    (every_old_query_keeps_its_original_outcome frame atCurrent reader occurrence projection)))

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Direct
