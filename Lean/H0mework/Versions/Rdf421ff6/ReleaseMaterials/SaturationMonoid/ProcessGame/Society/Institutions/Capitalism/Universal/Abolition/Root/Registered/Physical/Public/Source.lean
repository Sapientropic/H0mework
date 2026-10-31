import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Public.Current

/-! The physical source is below the financial macro. Its occurrence keeps
the original network support and computes raw effects; native debt updates
must consume these very items in the financial installation. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Public

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (oldPast : List (Compile.RawInput Party Good Port Technology Instrument))

abbrev N := Actual.N input depth count

def supportAt (current : Cursor Party Good Port Technology Instrument) : (N input depth count).Support :=
  (Continuation.oldSupport input (Migration.frame input depth count),
    (stateAt input depth count prefixLimit renewalLimit oldPast current.past).raw)

def materialWrite (current : Cursor Party Good Port Technology Instrument) : Bool :=
  match current.incoming with
  | .code _ | .review _ => false
  | _ => (resultAt input depth count prefixLimit renewalLimit oldPast current).isAccepted

abbrev V : ConstructiveRoot.Vocabulary where
  Current := Cursor Party Good Port Technology Instrument
  Anchor := (N input depth count).Anchor
  Incidence := (N input depth count).Incidence
  Lineage := (N input depth count).Lineage
  anchorAt := fun current => (N input depth count).anchorAt (supportAt input depth count prefixLimit renewalLimit oldPast current)
  incidenceAt := fun current => (N input depth count).incidenceAt (supportAt input depth count prefixLimit renewalLimit oldPast current)
  lineageAt := fun current => (N input depth count).lineageAt (supportAt input depth count prefixLimit renewalLimit oldPast current)
  NativeWriteAt := fun current => PLift (materialWrite input depth count prefixLimit renewalLimit oldPast current = true)
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun current => PLift (materialWrite input depth count prefixLimit renewalLimit oldPast current = false)
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := fun {current} _ => next current
  relationTarget := PEmpty.elim
  continuedTarget := fun {current} _ => next current
  redirectTarget := PEmpty.elim

inductive EventAt : (V input depth count prefixLimit renewalLimit oldPast).Current → (N input depth count).Support → Type
  | emitted (current) : EventAt current (supportAt input depth count prefixLimit renewalLimit oldPast current)

def sourceLaw : SourceNativeEventAlgebra (N input depth count) (V input depth count prefixLimit renewalLimit oldPast) where
  EventAt := EventAt input depth count prefixLimit renewalLimit oldPast
  compile := by
    intro current support event
    cases event
    by_cases written : materialWrite input depth count prefixLimit renewalLimit oldPast current = true
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
    SourceNativeSource (N input depth count) (V input depth count prefixLimit renewalLimit oldPast) where
  initial := start
  law := sourceLaw input depth count prefixLimit renewalLimit oldPast

def emitted (start current : Cursor Party Good Port Technology Instrument) :
    (sourceAt input depth count prefixLimit renewalLimit oldPast start).toRootSource.actual.OccurrenceAt current :=
  ⟨supportAt input depth count prefixLimit renewalLimit oldPast current, .emitted current⟩

theorem compiler_eq_source_choice (start current : Cursor Party Good Port Technology Instrument) :
    (sourceAt input depth count prefixLimit renewalLimit oldPast start).toRootSource.actual.compile
        (emitted input depth count prefixLimit renewalLimit oldPast start current) =
      if written : materialWrite input depth count prefixLimit renewalLimit oldPast current = true then
        .nativeWrite ⟨written⟩
      else .continuedTransport ⟨Bool.eq_false_of_not_eq_true written⟩ := rfl

theorem occurrence_eq_emitted (start current : Cursor Party Good Port Technology Instrument)
    (occurrence : (sourceAt input depth count prefixLimit renewalLimit oldPast start).toRootSource.actual.OccurrenceAt current) :
    occurrence = emitted input depth count prefixLimit renewalLimit oldPast start current := by
  rcases occurrence with ⟨support, event⟩
  cases event
  rfl

theorem blocked_advance_is_transport (current : Cursor Party Good Port Technology Instrument)
    (incoming : current.incoming = .advance)
    (refusal : (resultAt input depth count prefixLimit renewalLimit oldPast current).isAccepted = false) :
    materialWrite input depth count prefixLimit renewalLimit oldPast current = false := by
  simp only [materialWrite, incoming]
  exact refusal

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Public
