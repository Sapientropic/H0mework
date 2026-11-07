import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Source.State

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Source

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit : Nat}
  {oldPast : List (Compile.RawInput Party Good Port Technology Instrument)}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  {world : WorldRelationNetwork} {anchor : (Epoch.Finance.process input depth count).GeneratedState}
  (prior : Epoch.Finance.Future.Continuation.AccountFamily input depth count world anchor)
  (origin : Accounting.Current input depth count anchor)
  (registered : Registration input depth count prefixLimit renewalLimit oldPast start origin)


abbrev V : ConstructiveRoot.Vocabulary where
  Current := State origin registered
  Anchor := (Born.N prior origin registered).Anchor
  Incidence := (Born.N prior origin registered).Incidence
  Lineage := (Born.N prior origin registered).Lineage
  anchorAt := fun current => (Born.N prior origin registered).anchorAt (supportAt prior origin registered current)
  incidenceAt := fun current => (Born.N prior origin registered).incidenceAt (supportAt prior origin registered current)
  lineageAt := fun current => (Born.N prior origin registered).lineageAt (supportAt prior origin registered current)
  NativeWriteAt := fun current => PLift (writes origin registered current = true)
  ContinuedTransportAt := fun current => PLift (writes origin registered current = false)
  RelationWriteAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := fun {current} _ => next origin registered current
  continuedTarget := fun {current} _ => next origin registered current
  relationTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

inductive EventAt : (V prior origin registered).Current → (Born.N prior origin registered).Support → Type
  | emitted (current) : EventAt current (supportAt prior origin registered current)

def sourceLaw : SourceNativeEventAlgebra (Born.N prior origin registered) (V prior origin registered) where
  EventAt := EventAt prior origin registered
  compile := by
    intro current support event
    cases event
    by_cases active : writes origin registered current = true
    · exact .nativeWrite ⟨active⟩
    · exact .continuedTransport ⟨Bool.eq_false_of_not_eq_true active⟩
  AffectedInventoryAt := fun {_} {support} _ => OpenResponsibilityAt (Born.N prior origin registered) support
  affectedInventoryPresentation := fun _ => ConstructivePresentation.refl _
  anchorKey := id
  incidenceKey := id
  lineageKey := id
  anchor_commutes := by intro current support event; cases event; rfl
  incidence_commutes := by intro current support event; cases event; rfl
  lineage_commutes := by intro current support event; cases event; rfl

def source : SourceNativeSource (Born.N prior origin registered) (V prior origin registered) where
  initial := none
  law := sourceLaw prior origin registered

def emitted (current : State origin registered) :
    (source prior origin registered).toRootSource.actual.OccurrenceAt current :=
  ⟨supportAt prior origin registered current, .emitted current⟩

theorem occurrence_eq_emitted {current : State origin registered}
    (occurrence : (source prior origin registered).toRootSource.actual.OccurrenceAt current) :
    occurrence = emitted prior origin registered current := by
  rcases occurrence with ⟨support, event⟩
  cases event
  rfl

theorem source_choice (current : State origin registered) :
    (source prior origin registered).toRootSource.actual.compile
      (emitted prior origin registered current) =
      if active : writes origin registered current = true then
        EvolutionAt.nativeWrite (V := V prior origin registered) ⟨active⟩
      else .continuedTransport ⟨Bool.eq_false_of_not_eq_true active⟩ := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Source
