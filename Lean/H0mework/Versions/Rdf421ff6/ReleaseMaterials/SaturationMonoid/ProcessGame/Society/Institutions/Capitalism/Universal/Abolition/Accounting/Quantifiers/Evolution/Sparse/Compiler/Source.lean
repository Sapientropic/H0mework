import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Compiler.Code

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Compiler

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

noncomputable section

variable {N : WorldRelationNetwork} (code : Code N)

abbrev V : ConstructiveRoot.Vocabulary where
  Current := code.Current
  Anchor := N.Anchor
  Incidence := N.Incidence
  Lineage := N.Lineage
  anchorAt := fun current => N.anchorAt (code.support current)
  incidenceAt := fun current => N.incidenceAt (code.support current)
  lineageAt := fun current => N.lineageAt (code.support current)
  NativeWriteAt := fun current => PLift (code.writes current = true)
  ContinuedTransportAt := fun current => PLift (code.writes current = false)
  RelationWriteAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := fun {current} _ => code.next current
  continuedTarget := fun {current} _ => code.next current
  relationTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

inductive EventAt : code.Current → N.Support → Type
  | emitted (current) (origin : code.Fibre) : EventAt current (code.supportAt current origin)

def eventAlgebra : SourceNativeEventAlgebra N (V code) where
  EventAt := EventAt code
  compile := by
    intro current support event
    cases event
    by_cases write : code.writes current = true
    · exact .nativeWrite ⟨write⟩
    · exact .continuedTransport ⟨Bool.eq_false_of_not_eq_true write⟩
  AffectedInventoryAt := fun {_} {support} _ => OpenResponsibilityAt N support
  affectedInventoryPresentation := fun _ => ConstructivePresentation.refl _
  anchorKey := id
  incidenceKey := id
  lineageKey := id
  anchor_commutes := by intro current support event; cases event; exact code.anchor_coherent _ _
  incidence_commutes := by intro current support event; cases event; exact code.incidence_coherent _ _
  lineage_commutes := by intro current support event; cases event; exact code.lineage_coherent _ _

def source : SourceNativeSource N (V code) where
  initial := code.initial
  law := eventAlgebra code

def represented (current : code.Current) (origin : code.Fibre) : (source code).toRootSource.actual.OccurrenceAt current :=
  ⟨code.supportAt current origin,.emitted current origin⟩

def emitted (current : code.Current) : (source code).toRootSource.actual.OccurrenceAt current :=
  represented code current code.emission

def originalOccurrence {current : code.Current} (occurrence : (source code).toRootSource.actual.OccurrenceAt current) : code.Fibre := by
  rcases occurrence with ⟨support,event⟩
  cases event with
  | emitted origin => exact origin

theorem represented_original {current : code.Current} (occurrence : (source code).toRootSource.actual.OccurrenceAt current) :
    represented code current (originalOccurrence code occurrence) = occurrence := by
  rcases occurrence with ⟨support,event⟩
  cases event
  rfl

theorem original_represented (current : code.Current) (origin : code.Fibre) :
    originalOccurrence code (represented code current origin) = origin := rfl

theorem occurrence_support {current : code.Current} (occurrence : (source code).toRootSource.actual.OccurrenceAt current) :
    occurrence.1 = code.supportAt current (originalOccurrence code occurrence) := by
  rcases occurrence with ⟨support,event⟩
  cases event
  rfl

structure ExactTransitionAt {current : code.Current}
    (occurrence : (source code).toRootSource.actual.OccurrenceAt current) {targetSupport : N.Support}
    (before : OpenResponsibilityAt N occurrence.1) (after : OpenResponsibilityAt N targetSupport) : Type where
  evolution : LedgerEntryEvolutionAt N before after

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Compiler
