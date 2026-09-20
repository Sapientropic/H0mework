import H0mework.Realization.SourceComparison.GroundedRealization

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RawGeneratedRoot

universe u

set_option genInjectivity false in
/-- Raw event dynamics, before any registration, ledger or realization. -/
structure Dynamics where
  State : Type u
  EventAt : State → Type u
  initial : State
  emit : (state : State) → EventAt state
  update : {state : State} → EventAt state → State

variable (D : Dynamics.{u})

def network : WorldRelationNetwork.{u} where
  Support := D.State
  Anchor := PUnit
  Incidence := D.State
  Lineage := PUnit
  Responsibility := PUnit
  Claim := PUnit
  anchorAt := fun _ => PUnit.unit
  incidenceAt := id
  lineageAt := fun _ => PUnit.unit
  OpenAt := fun _ _ => PUnit
  openClaimAt := fun _ => PUnit.unit
  HoldsAt := fun _ _ => PEmpty
  ObstructionAt := fun _ => PEmpty
  obstructionClaim := PEmpty.elim
  SemanticChangeAt := fun _ _ _ => PEmpty
  DispositionAt := fun state kind => match kind with
    | .transfer => D.EventAt state
    | .supportSettlement | .lawSurfaceExtension => PEmpty

def vocabulary : Vocabulary.{u} where
  Current := D.State
  Anchor := PUnit
  Incidence := D.State
  Lineage := PUnit
  anchorAt := fun _ => PUnit.unit
  incidenceAt := id
  lineageAt := fun _ => PUnit.unit
  NativeWriteAt := D.EventAt
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := D.update
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

def entry (state : D.State) : OpenResponsibilityAt (network D) state :=
  ⟨PUnit.unit, PUnit.unit⟩

theorem entry_unique (state : D.State) (row : OpenResponsibilityAt (network D) state) :
    row = entry D state := by
  rcases row with ⟨⟨⟩, ⟨⟩⟩
  rfl

def inventory (state : D.State) :
    ConstructivePresentation PUnit (OpenResponsibilityAt (network D) state) where
  forward := fun _ => entry D state
  backward := fun _ => PUnit.unit
  backward_forward := fun _ => rfl
  forward_backward := fun row => (entry_unique D state row).symm

set_option genInjectivity false in
structure EventAt (state support : D.State) where
  event : D.EventAt state
  support_eq : support = state

def eventLaw : SourceNativeEventAlgebra (network D) (vocabulary D) where
  EventAt := EventAt D
  compile := fun event => .nativeWrite event.event
  AffectedInventoryAt := fun _ => PUnit
  affectedInventoryPresentation := fun {state} {_support} event => by
    cases event.support_eq
    exact inventory D state
  anchorKey := id
  incidenceKey := id
  lineageKey := id
  anchor_commutes := fun _ => rfl
  incidence_commutes := fun event => event.support_eq.symm
  lineage_commutes := fun _ => rfl

def source : SourceNativeSource (network D) (vocabulary D) where
  initial := D.initial
  law := eventLaw D

def emitted (state : D.State) : (source D).toRootSource.actual.OccurrenceAt state :=
  ⟨state, ⟨D.emit state, rfl⟩⟩

set_option genInjectivity false in
structure ExactTransitionAt {state : D.State}
    (occurrence : (source D).toRootSource.actual.OccurrenceAt state)
    (target : D.State) : Type u where
  target_eq : target = D.update occurrence.2.event

def rowSource : LedgerWriteRowSourceAt (source D)
    (fun occurrence target _ _ => ExactTransitionAt D occurrence target) where
  IncidenceOccurrenceAt := fun occurrence target _ _ => ExactTransitionAt D occurrence target
  compileEvolution := by
    intro state occurrence target oldRow newRow transition
    rcases occurrence with ⟨support, event, same⟩
    cases same
    cases transition.target_eq
    exact .transferred event rfl rfl (Nat.le_refl _)
  compileExact := fun event => event

def rows {state : D.State} (occurrence : (source D).toRootSource.actual.OccurrenceAt state) :
    FiniteGeneratedLedgerWriteRowsAt (rowSource D) occurrence
      (⟨D.update occurrence.2.event⟩ : CompleteLiveLedgerAt (network D)) where
  size := 1
  sourceEntryAt := fun _ => entry D occurrence.1
  targetEntryAt := fun _ => entry D (D.update occurrence.2.event)
  rowAt := fun _ => (rowSource D).generate ⟨rfl⟩

def coverage {state : D.State}
    (occurrence : (source D).toRootSource.actual.OccurrenceAt state) :
    LedgerCompleteFiniteCoverageAt (rows D occurrence) where
  destinationIndex := fun _ => ⟨0, Nat.zero_lt_one⟩
  originIndex := fun _ => ⟨0, Nat.zero_lt_one⟩
  destination_sound := fun row => (entry_unique D _ row).symm
  origin_sound := fun row => (entry_unique D _ row).symm

def patch {state : D.State} (occurrence : (source D).toRootSource.actual.OccurrenceAt state) :
    FiniteGeneratedLedgerWritePatchAt (rowSource D) occurrence
      (⟨D.update occurrence.2.event⟩ : CompleteLiveLedgerAt (network D)) :=
  .complete (rows D occurrence) (coverage D occurrence)

def evolution {state : D.State}
    (occurrence : (source D).toRootSource.actual.OccurrenceAt state) :
    SourceNativeLedgerEvolutionAt (source D) occurrence :=
  .nativeWrite occurrence.2.event rfl (emitted D (D.update occurrence.2.event))
    (patch D occurrence).toLedgerWriteEvolution

def ledgerCompiler : SourceNativeLedgerCompiler (source D) where
  IncidenceTransitionAt := fun _ _ _ => PUnit
  ExactTransitionAt := fun occurrence target _ _ => ExactTransitionAt D occurrence target
  exact_incidence := fun _ => PUnit.unit
  exact_lineage := fun _ => rfl
  writeRowSource := rowSource D
  terminalRowSource := LedgerTerminalRowSourceAt.empty _
  compile := evolution D
  compilePatch := fun occurrence => ⟨patch D occurrence, rfl⟩

private def restructuringLaw : SourceNativeLedgerRestructuringLaw (source D) :=
  identityOnlyWorldLedgerRestructuringLaw (source D) PUnit.unit <| by
    intro _ _
    exact ⟨fun ⟨⟩ ⟨⟩ => rfl⟩

private def restructuringCompiler : SourceNativeRestructuringLedgerCompiler (source D) where
  ledgerCompiler := ledgerCompiler D
  restructuringLaw := restructuringLaw D
  certifyRestructuring := fun _ => ExactLedgerRestructuringCertificationAt.ofInjective
    (fun left right _ => (entry_unique D _ left).trans (entry_unique D _ right).symm)
    (fun left right _ => (entry_unique D _ left).trans (entry_unique D _ right).symm)

def restructuringSource : SourceNativeRestructuringLedgerSource (network D) (vocabulary D) where
  source := source D
  compiler := restructuringCompiler D

def projectionLaw : SourceNativeProjectionLaw (restructuringSource D).toLedgerSource where
  Projection := PUnit
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun _ {_} _ _ => Sigma D.EventAt
  project := fun _ {state} occurrence _ => ⟨state, occurrence.2.event⟩

def authoritySource : SourceNativeAuthoritySource (network D) (vocabulary D) where
  restructuringSource := restructuringSource D
  eventInventoryAdmission := .reflOfNoFaithfulTerminal (restructuringSource D)
    (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := .rootSemantic (network D)
  projectionLaw := projectionLaw D

def rawWorld : SourceNativeLivingRawWorld (network D) (vocabulary D) where
  source := ⟨authoritySource D, (authoritySource D).emptyFaithfulTerminalHandoff
    (fun _ => ⟨fun terminal => nomatch terminal⟩)⟩
  emitted := emitted D

theorem generated_commuting : SourceNativeLivingRootCommutingAt (rawWorld D) :=
  ⟨fun _ => rfl⟩

def root : SourceNativeLivingRootClosure (network D) (vocabulary D) :=
  (rawWorld D).toLivingRoot (generated_commuting D)

def realization := (rawWorld D).canonicalRepresentation (generated_commuting D)

end RawGeneratedRoot
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
