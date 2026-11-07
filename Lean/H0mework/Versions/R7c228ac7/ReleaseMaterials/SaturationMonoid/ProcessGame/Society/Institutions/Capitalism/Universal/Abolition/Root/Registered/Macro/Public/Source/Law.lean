import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.NativeEvolution

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Source

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (oldPast : List (Compile.RawInput Party Good Port Technology Instrument))
  (start : Physical.Cursor Party Good Port Technology Instrument)
  {world : WorldRelationNetwork} {anchor : (Epoch.Finance.process input depth count).GeneratedState}
  (family : Epoch.Finance.Future.Continuation.AccountFamily input depth count world anchor)

def writes (current : Accounting.Current input depth count anchor) : Bool :=
  if current.bodyPaid then
    match Accounting.item? input depth count prefixLimit renewalLimit oldPast start current with
    | none => false
    | some _item => true
  else Physical.Public.materialWrite input depth count prefixLimit renewalLimit oldPast start

abbrev V : ConstructiveRoot.Vocabulary where
  Current := Accounting.Current input depth count anchor
  Anchor := world.Anchor
  Incidence := world.Incidence
  Lineage := world.Lineage
  anchorAt := fun current => world.anchorAt (Accounting.support input depth count family current)
  incidenceAt := fun current => world.incidenceAt (Accounting.support input depth count family current)
  lineageAt := fun current => world.lineageAt (Accounting.support input depth count family current)
  NativeWriteAt := fun current => PLift (writes input depth count prefixLimit renewalLimit oldPast start current = true)
  ContinuedTransportAt := fun current => PLift (writes input depth count prefixLimit renewalLimit oldPast start current = false)
  RelationWriteAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := fun {current} _ => Accounting.nativeNext input depth count prefixLimit renewalLimit oldPast start current
  continuedTarget := fun {current} _ => Accounting.nativeNext input depth count prefixLimit renewalLimit oldPast start current
  relationTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

inductive EventAt : (V input depth count prefixLimit renewalLimit oldPast start family).Current → world.Support → Type
  | emitted (current) : EventAt current (Accounting.support input depth count family current)

def sourceLaw : SourceNativeEventAlgebra world (V input depth count prefixLimit renewalLimit oldPast start family) where
  EventAt := EventAt input depth count prefixLimit renewalLimit oldPast start family
  compile := by
    intro current support event
    cases event
    by_cases active : writes input depth count prefixLimit renewalLimit oldPast start current = true
    · exact .nativeWrite ⟨active⟩
    · exact .continuedTransport ⟨Bool.eq_false_of_not_eq_true active⟩
  AffectedInventoryAt := fun {_} {support} _ => OpenResponsibilityAt world support
  affectedInventoryPresentation := fun _ => ConstructivePresentation.refl _
  anchorKey := id
  incidenceKey := id
  lineageKey := id
  anchor_commutes := by intro current support event; cases event; rfl
  incidence_commutes := by intro current support event; cases event; rfl
  lineage_commutes := by intro current support event; cases event; rfl

def source : SourceNativeSource world (V input depth count prefixLimit renewalLimit oldPast start family) where
  initial := Accounting.initial input depth count anchor
  law := sourceLaw input depth count prefixLimit renewalLimit oldPast start family

def emitted (current : Accounting.Current input depth count anchor) :
    (source input depth count prefixLimit renewalLimit oldPast start family).toRootSource.actual.OccurrenceAt current :=
  ⟨Accounting.support input depth count family current, .emitted current⟩

theorem occurrence_eq_emitted {current : Accounting.Current input depth count anchor}
    (occurrence : (source input depth count prefixLimit renewalLimit oldPast start family).toRootSource.actual.OccurrenceAt current) :
    occurrence = emitted input depth count prefixLimit renewalLimit oldPast start family current := by
  rcases occurrence with ⟨support, event⟩
  cases event
  rfl

theorem source_choice (current : Accounting.Current input depth count anchor) :
    (source input depth count prefixLimit renewalLimit oldPast start family).toRootSource.actual.compile
      (emitted input depth count prefixLimit renewalLimit oldPast start family current) =
      if active : writes input depth count prefixLimit renewalLimit oldPast start current = true then
        EvolutionAt.nativeWrite (V := V input depth count prefixLimit renewalLimit oldPast start family) ⟨active⟩
      else .continuedTransport ⟨Bool.eq_false_of_not_eq_true active⟩ := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Source
