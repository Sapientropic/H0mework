import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Current

/-! The physical source is below the financial macro. Its occurrence keeps
the original network support and computes raw effects; native debt updates
must consume these very items in the financial installation. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)

abbrev N := Actual.N input depth count

def supportAt (current : Cursor Party Good Port Technology Instrument) : (N input depth count).Support :=
  (Continuation.oldSupport input (Migration.frame input depth count),
    (stateAt input depth count prefixLimit renewalLimit current.past).raw)

def resultAt (current : Cursor Party Good Port Technology Instrument) :=
  Compile.compile input depth count prefixLimit renewalLimit
    (stateAt input depth count prefixLimit renewalLimit current.past) current.incoming

def materialWrite (current : Cursor Party Good Port Technology Instrument) : Bool :=
  match current.incoming with
  | .code _ => false
  | _ => (resultAt input depth count prefixLimit renewalLimit current).isAccepted

abbrev V : ConstructiveRoot.Vocabulary where
  Current := Cursor Party Good Port Technology Instrument
  Anchor := (N input depth count).Anchor
  Incidence := (N input depth count).Incidence
  Lineage := (N input depth count).Lineage
  anchorAt := fun current => (N input depth count).anchorAt (supportAt input depth count prefixLimit renewalLimit current)
  incidenceAt := fun current => (N input depth count).incidenceAt (supportAt input depth count prefixLimit renewalLimit current)
  lineageAt := fun current => (N input depth count).lineageAt (supportAt input depth count prefixLimit renewalLimit current)
  NativeWriteAt := fun current => PLift (materialWrite input depth count prefixLimit renewalLimit current = true)
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun current => PLift (materialWrite input depth count prefixLimit renewalLimit current = false)
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := fun {current} _ => next current
  relationTarget := PEmpty.elim
  continuedTarget := fun {current} _ => next current
  redirectTarget := PEmpty.elim

inductive EventAt : (V input depth count prefixLimit renewalLimit).Current → (N input depth count).Support → Type
  | emitted (current) : EventAt current (supportAt input depth count prefixLimit renewalLimit current)

def sourceLaw : SourceNativeEventAlgebra (N input depth count) (V input depth count prefixLimit renewalLimit) where
  EventAt := EventAt input depth count prefixLimit renewalLimit
  compile := by
    intro current support event
    cases event
    by_cases written : materialWrite input depth count prefixLimit renewalLimit current = true
    · exact .nativeWrite (PLift.up written)
    · exact .continuedTransport (PLift.up (Bool.eq_false_of_not_eq_true written))
  AffectedInventoryAt := fun {_} {support} _ => OpenResponsibilityAt (N input depth count) support
  affectedInventoryPresentation := fun _ => ConstructivePresentation.refl _
  anchorKey := id
  incidenceKey := id
  lineageKey := id
  anchor_commutes := by intro current support event; cases event; rfl
  incidence_commutes := by intro current support event; cases event; rfl
  lineage_commutes := by intro current support event; cases event; rfl

def sourceAt (start : Cursor Party Good Port Technology Instrument) :
    SourceNativeSource (N input depth count) (V input depth count prefixLimit renewalLimit) where
  initial := start
  law := sourceLaw input depth count prefixLimit renewalLimit

def emitted (start current : Cursor Party Good Port Technology Instrument) :
    (sourceAt input depth count prefixLimit renewalLimit start).toRootSource.actual.OccurrenceAt current :=
  ⟨supportAt input depth count prefixLimit renewalLimit current, .emitted current⟩

theorem compiler_eq_source_choice (start current : Cursor Party Good Port Technology Instrument) :
    (sourceAt input depth count prefixLimit renewalLimit start).toRootSource.actual.compile
        (emitted input depth count prefixLimit renewalLimit start current) =
      if written : materialWrite input depth count prefixLimit renewalLimit current = true then
        .nativeWrite ⟨written⟩
      else .continuedTransport ⟨Bool.eq_false_of_not_eq_true written⟩ := rfl

theorem occurrence_eq_emitted (start current : Cursor Party Good Port Technology Instrument)
    (occurrence : (sourceAt input depth count prefixLimit renewalLimit start).toRootSource.actual.OccurrenceAt current) :
    occurrence = emitted input depth count prefixLimit renewalLimit start current := by
  rcases occurrence with ⟨support, event⟩
  cases event
  rfl

theorem blocked_advance_is_transport (current : Cursor Party Good Port Technology Instrument)
    (incoming : current.incoming = .advance)
    (refusal : (resultAt input depth count prefixLimit renewalLimit current).isAccepted = false) :
    materialWrite input depth count prefixLimit renewalLimit current = false := by
  simp only [materialWrite, incoming]
  exact refusal

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical
