import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Admission.State

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Admission

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (frame : NativeFrame input) {origin : frame.V.Current}
  (registered : Registration input frame origin)

abbrev vocabulary : ConstructiveRoot.Vocabulary where
  Current := Current input frame registered
  Anchor := frame.V.Anchor
  Incidence := frame.V.Incidence
  Lineage := frame.V.Lineage
  anchorAt := fun current => frame.V.anchorAt current.1
  incidenceAt := fun current => frame.V.incidenceAt current.1
  lineageAt := fun current => frame.V.lineageAt current.1
  NativeWriteAt := fun _ => Unit
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := fun {current} _ => next input frame registered current
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

abbrev V := vocabulary input frame registered

inductive NativeEventAt : (V input frame registered).Current → (N input frame registered).Support → Type
  | emitted (current : Current input frame registered) : NativeEventAt current (supportAt input frame registered current)

def sourceLaw : SourceNativeEventAlgebra (N input frame registered) (V input frame registered) where
  EventAt := NativeEventAt input frame registered
  compile := fun _ => .nativeWrite ()
  AffectedInventoryAt := fun {_} {support} _ => OpenResponsibilityAt (N input frame registered) support
  affectedInventoryPresentation := fun _ => ConstructivePresentation.refl _
  anchorKey := frame.root.toAuthoritativeRoot.toLedgerRoot.source.source.law.anchorKey
  incidenceKey := frame.root.toAuthoritativeRoot.toLedgerRoot.source.source.law.incidenceKey
  lineageKey := frame.root.toAuthoritativeRoot.toLedgerRoot.source.source.law.lineageKey
  anchor_commutes := by
    intro current support event
    cases event
    exact frame.root.toAuthoritativeRoot.toLedgerRoot.source.source.law.anchor_commutes (frame.root.emitted current.1).2
  incidence_commutes := by
    intro current support event
    cases event
    exact frame.root.toAuthoritativeRoot.toLedgerRoot.source.source.law.incidence_commutes (frame.root.emitted current.1).2
  lineage_commutes := by
    intro current support event
    cases event
    exact frame.root.toAuthoritativeRoot.toLedgerRoot.source.source.law.lineage_commutes (frame.root.emitted current.1).2

def source : SourceNativeSource (N input frame registered) (V input frame registered) where
  initial := initial input frame registered
  law := sourceLaw input frame registered

def emitted (current : Current input frame registered) :
    (source input frame registered).toRootSource.actual.OccurrenceAt current :=
  ⟨supportAt input frame registered current, .emitted current⟩

theorem occurrence_eq_emitted {current : Current input frame registered}
    (occurrence : (source input frame registered).toRootSource.actual.OccurrenceAt current) :
    occurrence = emitted input frame registered current := by
  rcases occurrence with ⟨support, event⟩
  cases event
  rfl

def originalOccurrence {current : Current input frame registered}
    (_occurrence : (source input frame registered).toRootSource.actual.OccurrenceAt current) :
    frame.root.toAuthoritativeRoot.toRoot.actual.OccurrenceAt current.1 := frame.root.emitted current.1

theorem original_next_is_used_once (current : Current input frame registered) :
    (next input frame registered current).1 = frame.V.nativeTarget (frame.program.emit current.1).write := rfl

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Admission
