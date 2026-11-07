import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Reentry.State

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Reentry

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat)
  (start : Physical.Cursor Party Good Port Technology Instrument)
  (proposal : Compile.RawInput Party Good Port Technology Instrument)
  {review : Option (ReviewPhase.ContextAt input)}
  {world : WorldRelationNetwork} {anchor : (Epoch.Finance.process input depth count).GeneratedState}
  (family : Epoch.Finance.Future.Continuation.AccountFamily input depth count world anchor)
  (seed_eq : Accounting.seedAccount (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal 0 = anchor)

local notation "C" => Accounting.Current (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal 0
local notation "supp" => supportAt (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq
local notation "advance" => Accounting.next (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal 0
local notation "writes" => Accounting.writes (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal 0

abbrev V : ConstructiveRoot.Vocabulary where
  Current := C
  Anchor := world.Anchor
  Incidence := world.Incidence
  Lineage := world.Lineage
  anchorAt := fun current => world.anchorAt (supp current)
  incidenceAt := fun current => world.incidenceAt (supp current)
  lineageAt := fun current => world.lineageAt (supp current)
  NativeWriteAt := fun current => PLift (writes current = true)
  ContinuedTransportAt := fun current => PLift (writes current = false)
  RelationWriteAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := fun {current} _ => advance current
  continuedTarget := fun {current} _ => advance current
  relationTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

inductive EventAt : (V (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq).Current → world.Support → Type
  | emitted (current) : EventAt current (supp current)

def sourceLaw : SourceNativeEventAlgebra world
    (V (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq) where
  EventAt := EventAt (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq
  compile := by
    intro current support event
    cases event
    by_cases written : writes current = true
    · exact .nativeWrite ⟨written⟩
    · exact .continuedTransport ⟨Bool.eq_false_of_not_eq_true written⟩
  AffectedInventoryAt := fun {_} {support} _ => OpenResponsibilityAt world support
  affectedInventoryPresentation := fun _ => ConstructivePresentation.refl _
  anchorKey := id
  incidenceKey := id
  lineageKey := id
  anchor_commutes := by intro current support event; cases event; rfl
  incidence_commutes := by intro current support event; cases event; rfl
  lineage_commutes := by intro current support event; cases event; rfl

def source : SourceNativeSource world (V (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq) where
  initial := Accounting.initial (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal 0
  law := sourceLaw (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq

def emitted (current : C) :
    (source (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq).toRootSource.actual.OccurrenceAt current :=
  ⟨supp current, .emitted current⟩

theorem occurrence_eq_emitted {current : C}
    (occurrence : (source (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq).toRootSource.actual.OccurrenceAt current) :
    occurrence = emitted (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq current := by
  rcases occurrence with ⟨support, event⟩
  cases event
  rfl

theorem source_choice (current : C) :
    (source (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq).toRootSource.actual.compile
      (emitted (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq current) =
    if written : writes current = true then EvolutionAt.nativeWrite
      (V := V (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq) ⟨written⟩
    else .continuedTransport ⟨Bool.eq_false_of_not_eq_true written⟩ := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Reentry
