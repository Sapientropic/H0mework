import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Migration.Selection

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Migration

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)

def supportAt (index : Nat) : (N input depth count).Support :=
  (Continuation.oldSupport input (frame input depth count), rawAt input depth count prefixLimit renewalLimit index)

abbrev V : ConstructiveRoot.Vocabulary where
  Current := Nat
  Anchor := (N input depth count).Anchor
  Incidence := (N input depth count).Incidence
  Lineage := (N input depth count).Lineage
  anchorAt := fun index => (N input depth count).anchorAt (supportAt input depth count prefixLimit renewalLimit index)
  incidenceAt := fun index => (N input depth count).incidenceAt (supportAt input depth count prefixLimit renewalLimit index)
  lineageAt := fun index => (N input depth count).lineageAt (supportAt input depth count prefixLimit renewalLimit index)
  NativeWriteAt := fun _ => Unit
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := fun {current} _ => current + 1
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

inductive EventAt : (V input depth count prefixLimit renewalLimit).Current → (N input depth count).Support → Type
  | emitted (index) : EventAt index (supportAt input depth count prefixLimit renewalLimit index)

def sourceLaw : SourceNativeEventAlgebra (N input depth count) (V input depth count prefixLimit renewalLimit) where
  EventAt := EventAt input depth count prefixLimit renewalLimit
  compile := fun _ => .nativeWrite ()
  AffectedInventoryAt := fun {_} {support} _ => OpenResponsibilityAt (N input depth count) support
  affectedInventoryPresentation := fun _ => ConstructivePresentation.refl _
  anchorKey := id
  incidenceKey := id
  lineageKey := id
  anchor_commutes := by intro current support event; cases event; rfl
  incidence_commutes := by intro current support event; cases event; rfl
  lineage_commutes := by intro current support event; cases event; rfl

def source : SourceNativeSource (N input depth count) (V input depth count prefixLimit renewalLimit) where
  initial := 0
  law := sourceLaw input depth count prefixLimit renewalLimit

def emitted (index : Nat) : (source input depth count prefixLimit renewalLimit).toRootSource.actual.OccurrenceAt index :=
  ⟨supportAt input depth count prefixLimit renewalLimit index, .emitted index⟩

theorem occurrence_eq_emitted {index : Nat}
    (occurrence : (source input depth count prefixLimit renewalLimit).toRootSource.actual.OccurrenceAt index) :
    occurrence = emitted input depth count prefixLimit renewalLimit index := by
  rcases occurrence with ⟨support, event⟩
  cases event
  rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Migration
