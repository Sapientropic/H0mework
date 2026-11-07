import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Finite

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section
variable {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
  (root : SourceNativeLivingRootClosure N V)
  (boundary : SourceNativeCofinalVisitAt root.toAuthoritativeRoot.toLedgerRoot)

abbrev CofinalEvent := { event : V.cofinal.Event // V.cofinal.emit? = some event }

inductive WriteAt : Current → Type
  | computed (current : Current) : WriteAt current

def schemaVocabulary : ConstructiveRoot.Vocabulary where
  Current := Current
  Anchor := N.Anchor
  Incidence := N.Incidence
  Lineage := N.Lineage
  anchorAt := fun current => (W root boundary).anchorAt (supportAt root boundary current)
  incidenceAt := fun current => (W root boundary).incidenceAt (supportAt root boundary current)
  lineageAt := fun current => (W root boundary).lineageAt (supportAt root boundary current)
  NativeWriteAt := WriteAt
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := fun {current} _ => next current
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim
  cofinal := {
    Event := CofinalEvent (V := V)
    emit? := some ⟨boundary.event,boundary.emitted_eq_event⟩
    pathAt := fun _ cut => .inl cut
    target := fun _ => .inr 0 }

abbrev SchemaV := schemaVocabulary root boundary

inductive EventAt : Current → (W root boundary).Support → Type
  | finite (cut : Nat) : EventAt (.inl cut) (supportAt root boundary (.inl cut))
  | landing (phase : Nat) : EventAt (.inr phase) (supportAt root boundary (.inr phase))

def eventAlgebra : SourceNativeEventAlgebra (W root boundary) (SchemaV root boundary) where
  EventAt := EventAt root boundary
  compile := by intro current support event; cases event <;> exact .nativeWrite (.computed _)
  AffectedInventoryAt := fun {_} {support} _ => OpenResponsibilityAt (W root boundary) support
  affectedInventoryPresentation := fun _ => ConstructivePresentation.refl _
  anchorKey := id
  incidenceKey := id
  lineageKey := id
  anchor_commutes := by intro current support event; cases event <;> rfl
  incidence_commutes := by intro current support event; cases event <;> rfl
  lineage_commutes := by intro current support event; cases event <;> rfl

def source : SourceNativeSource (W root boundary) (SchemaV root boundary) where
  initial := .inl 0
  law := eventAlgebra root boundary

def emitted : (current : Current) → (source root boundary).toRootSource.actual.OccurrenceAt current
  | .inl cut => ⟨supportAt root boundary (.inl cut),.finite cut⟩
  | .inr phase => ⟨supportAt root boundary (.inr phase),.landing phase⟩

theorem occurrence_is_the_source_emission {current : Current}
    (occurrence : (source root boundary).toRootSource.actual.OccurrenceAt current) :
    occurrence = emitted root boundary current := by
  rcases occurrence with ⟨support,event⟩
  cases event <;> rfl

def rawOccurrence (current : Current) := root.emitted (rawCurrent root boundary current)

theorem the_cofinal_event_is_the_original_source_event :
    Option.map Subtype.val (SchemaV root boundary).cofinal.emit? = V.cofinal.emit? :=
  boundary.emitted_eq_event.symm

theorem every_emittable_event_keeps_the_original_path
    (event : (SchemaV root boundary).cofinal.Event) (cut : Nat) :
    rawCurrent root boundary ((SchemaV root boundary).cofinal.pathAt event cut) = V.cofinal.pathAt event.val cut := by
  have same : event.val = boundary.event := Option.some.inj (event.property.symm.trans boundary.emitted_eq_event)
  change (boundary.history.visitAt cut).current = V.cofinal.pathAt event.val cut
  exact (boundary.history.visitAt_current cut).trans
    (congrArg (fun original => V.cofinal.pathAt original cut) same.symm)

theorem every_emittable_event_keeps_the_original_target
    (event : (SchemaV root boundary).cofinal.Event) :
    rawCurrent root boundary ((SchemaV root boundary).cofinal.target event) = V.cofinal.target event.val := by
  have same : event.val = boundary.event := Option.some.inj (event.property.symm.trans boundary.emitted_eq_event)
  change V.cofinal.target boundary.event = V.cofinal.target event.val
  exact congrArg V.cofinal.target same.symm

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing
