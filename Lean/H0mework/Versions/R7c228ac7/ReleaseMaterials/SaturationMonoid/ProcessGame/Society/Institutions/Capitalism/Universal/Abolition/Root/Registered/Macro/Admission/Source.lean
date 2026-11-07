import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Admission.State

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Admission

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  {proposal : Compile.RawInput Party Good Port Technology Instrument} {sourcePosition : Nat}
  {review : Option (ReviewPhase.ContextAt input)}
  (frame : NativeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
  {origin : frame.V.Current}
  (registered : HeadRegistration (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition frame origin)

abbrev V : ConstructiveRoot.Vocabulary where
  Current := Current frame registered
  Anchor := frame.V.Anchor
  Incidence := frame.V.Incidence
  Lineage := frame.V.Lineage
  anchorAt := fun current => frame.V.anchorAt current.1
  incidenceAt := fun current => frame.V.incidenceAt current.1
  lineageAt := fun current => frame.V.lineageAt current.1
  NativeWriteAt := fun current => PLift ((frame.item? current.1).isSome = true)
  ContinuedTransportAt := fun current => PLift ((frame.item? current.1).isSome = false)
  RelationWriteAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := fun {current} _ => next frame registered current
  continuedTarget := fun {current} _ => next frame registered current
  relationTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

inductive NativeEventAt : (V frame registered).Current → (N frame registered).Support → Type
  | emitted (current) : NativeEventAt current (supportAt frame registered current)

def sourceLaw : SourceNativeEventAlgebra (N frame registered) (V frame registered) where
  EventAt := NativeEventAt frame registered
  compile := by
    intro current support event
    cases event
    by_cases active : (frame.item? current.1).isSome = true
    · exact .nativeWrite ⟨active⟩
    · exact .continuedTransport ⟨Bool.eq_false_of_not_eq_true active⟩
  AffectedInventoryAt := fun {_} {support} _ => OpenResponsibilityAt (N frame registered) support
  affectedInventoryPresentation := fun _ => ConstructivePresentation.refl _
  anchorKey := frame.root.toAuthoritativeRoot.toLedgerRoot.source.source.law.anchorKey
  incidenceKey := frame.root.toAuthoritativeRoot.toLedgerRoot.source.source.law.incidenceKey
  lineageKey := frame.root.toAuthoritativeRoot.toLedgerRoot.source.source.law.lineageKey
  anchor_commutes := by
    intro current support event; cases event
    exact frame.root.toAuthoritativeRoot.toLedgerRoot.source.source.law.anchor_commutes (frame.root.emitted current.1).2
  incidence_commutes := by
    intro current support event; cases event
    exact frame.root.toAuthoritativeRoot.toLedgerRoot.source.source.law.incidence_commutes (frame.root.emitted current.1).2
  lineage_commutes := by
    intro current support event; cases event
    exact frame.root.toAuthoritativeRoot.toLedgerRoot.source.source.law.lineage_commutes (frame.root.emitted current.1).2

def source : SourceNativeSource (N frame registered) (V frame registered) where
  initial := initial frame registered
  law := sourceLaw frame registered

def emitted (current : (V frame registered).Current) : (source frame registered).toRootSource.actual.OccurrenceAt current :=
  ⟨supportAt frame registered current, .emitted current⟩

theorem occurrence_eq_emitted {current : (V frame registered).Current}
    (occurrence : (source frame registered).toRootSource.actual.OccurrenceAt current) :
    occurrence = emitted frame registered current := by
  rcases occurrence with ⟨support, event⟩
  cases event
  rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Admission
