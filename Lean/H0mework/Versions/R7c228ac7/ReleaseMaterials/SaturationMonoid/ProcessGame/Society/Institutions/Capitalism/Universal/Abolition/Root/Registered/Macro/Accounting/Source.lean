import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Accounting.State

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Accounting

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat)
  (start : Physical.Cursor Party Good Port Technology Instrument)
  (proposal : Compile.RawInput Party Good Port Technology Instrument)
  (sourcePosition : Nat)
  (review : Option (ReviewPhase.ContextAt input) := none)

abbrev V : ConstructiveRoot.Vocabulary where
  Current := Current (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
  Anchor := (N (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition).Anchor
  Incidence := (N (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition).Incidence
  Lineage := (N (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition).Lineage
  anchorAt := fun current => (N (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition).anchorAt
    (supportAt (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current)
  incidenceAt := fun current => (N (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition).incidenceAt
    (supportAt (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current)
  lineageAt := fun current => (N (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition).lineageAt
    (supportAt (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current)
  NativeWriteAt := fun current => PLift (writes (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current = true)
  ContinuedTransportAt := fun current => PLift (writes (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current = false)
  RelationWriteAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := fun {current} _ => next (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current
  continuedTarget := fun {current} _ => next (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current
  relationTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

inductive EventAt : (V (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition).Current →
    (N (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition).Support → Type
  | emitted (current) : EventAt current
      (supportAt (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current)

def sourceLaw : SourceNativeEventAlgebra
    (N (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
    (V (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition) where
  EventAt := EventAt (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
  compile := by
    intro current support event
    cases event
    by_cases active : writes (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current = true
    · exact .nativeWrite (PLift.up active)
    · exact .continuedTransport (PLift.up (Bool.eq_false_of_not_eq_true active))
  AffectedInventoryAt := fun {_} {support} _ => OpenResponsibilityAt
    (N (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition) support
  affectedInventoryPresentation := fun _ => ConstructivePresentation.refl _
  anchorKey := id
  incidenceKey := id
  lineageKey := id
  anchor_commutes := by intro current support event; cases event; rfl
  incidence_commutes := by intro current support event; cases event; rfl
  lineage_commutes := by intro current support event; cases event; rfl

def source : SourceNativeSource
    (N (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
    (V (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition) where
  initial := initial (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
  law := sourceLaw (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition

def emitted (current : (V (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition).Current) :
    (source (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition).toRootSource.actual.OccurrenceAt current :=
  ⟨supportAt (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current, .emitted current⟩

theorem occurrence_eq_emitted {current : (V (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition).Current}
    (occurrence : (source (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition).toRootSource.actual.OccurrenceAt current) :
    occurrence = emitted (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current := by
  rcases occurrence with ⟨support, event⟩
  cases event
  rfl

theorem a_no_write_source_cannot_mint_native_authority
    (current : (V (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition).Current)
    (done : writes (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current = false) :
    IsEmpty ((V (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition).NativeWriteAt current) := by
  refine ⟨fun write => ?_⟩
  have impossible := write.down
  rw [done] at impossible
  cases impossible

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Accounting
