import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Compiler.Flow

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Compiler

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {N : WorldRelationNetwork} (F : Flow N)



abbrev V : ConstructiveRoot.Vocabulary where
  Current := F.Current
  Anchor := (N).Anchor
  Incidence := (N).Incidence
  Lineage := (N).Lineage
  anchorAt := fun current => (N).anchorAt (F.support current)
  incidenceAt := fun current => (N).incidenceAt (F.support current)
  lineageAt := fun current => (N).lineageAt (F.support current)
  NativeWriteAt := fun current => PLift (F.writes current = true)
  ContinuedTransportAt := fun current => PLift (F.writes current = false)
  RelationWriteAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := fun {current} _ => F.next current
  continuedTarget := fun {current} _ => F.next current
  relationTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

inductive EventAt : (V F).Current → (N).Support → Type
  | emitted (current) : EventAt current (F.support current)

def sourceLaw : SourceNativeEventAlgebra (N) (V F) where
  EventAt := EventAt F
  compile := by
    intro current support event
    cases event
    by_cases active : F.writes current = true
    · exact .nativeWrite ⟨active⟩
    · exact .continuedTransport ⟨Bool.eq_false_of_not_eq_true active⟩
  AffectedInventoryAt := fun {_} {support} _ => OpenResponsibilityAt (N) support
  affectedInventoryPresentation := fun _ => ConstructivePresentation.refl _
  anchorKey := id
  incidenceKey := id
  lineageKey := id
  anchor_commutes := by intro current support event; cases event; rfl
  incidence_commutes := by intro current support event; cases event; rfl
  lineage_commutes := by intro current support event; cases event; rfl

def source : SourceNativeSource (N) (V F) where
  initial := F.initial
  law := sourceLaw F

def emitted (current : F.Current) :
    (source F).toRootSource.actual.OccurrenceAt current :=
  ⟨F.support current, .emitted current⟩

theorem occurrence_eq_emitted {current : F.Current}
    (occurrence : (source F).toRootSource.actual.OccurrenceAt current) :
    occurrence = emitted F current := by
  rcases occurrence with ⟨support, event⟩
  cases event
  rfl

theorem source_choice (current : F.Current) :
    (source F).toRootSource.actual.compile
      (emitted F current) =
      if active : F.writes current = true then
        EvolutionAt.nativeWrite (V := V F) ⟨active⟩
      else .continuedTransport ⟨Bool.eq_false_of_not_eq_true active⟩ := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Compiler
