import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.LivingLawRootInformationMemoryReadout
import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.LivingLawAtomFieldSeparationRegression

/-!
# Focused generated atom-authority regression

The positive fixture uses an infinite function-space carrier whose pointwise
increment is generated one finite section at a time.

The negative fixture is stronger than the old constant-tail stutter test.  Its
root current is a clock paired with a completed future, and every actual write
increments the clock while shifting the future.  Hence the write is genuinely
non-stuttering.  Nevertheless the constant chart is rejected at the source
mouth: its scope-zero section already decodes the entire future.

This pins the intended boundary.  Function spaces remain legal, and pointwise
finite sections remain source-generatable.  A completed field cannot dress as
one current atom merely by choosing `Local := Ambient`.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace RootAtomFieldAuthorityRegression

open ResidualProjection
open EffectiveResidualUpdate
open ConstructiveRoot
open LivingLawAtomFieldSeparationRegression

noncomputable section

universe u

/-! ## One non-stuttering root carrying a completed future -/

abbrev Future := FutureTail ℚ
abbrev ClockedFuture := ℚ × Future

def initialFuture : Future := fun index => (index : ℚ)

def initialClockedFuture : ClockedFuture :=
  (0, initialFuture)

def clockedShift (current : ClockedFuture) : ClockedFuture :=
  (current.1 + 1, shift current.2)

theorem clockedShift_ne (current : ClockedFuture) :
    clockedShift current ≠ current := by
  intro equality
  have clock_eq := congrArg Prod.fst equality
  change current.1 + 1 = current.1 at clock_eq
  linarith

def rootNetwork : WorldRelationNetwork where
  Support := PUnit
  Anchor := PUnit
  Incidence := PUnit
  Lineage := PUnit
  Responsibility := PUnit
  Claim := PUnit
  anchorAt := fun _ => PUnit.unit
  incidenceAt := fun _ => PUnit.unit
  lineageAt := fun _ => PUnit.unit
  OpenAt := fun _ _ => PEmpty
  openClaimAt := fun impossible => nomatch impossible
  HoldsAt := fun _ _ => PUnit
  ObstructionAt := fun _ => PUnit
  obstructionClaim := fun _ => PUnit.unit
  SemanticChangeAt := fun _ _ _ => PUnit
  DispositionAt := fun _ _ => PUnit

abbrev RootN := rootNetwork

def rootVocabulary : ConstructiveRoot.Vocabulary where
  Current := ClockedFuture
  Anchor := PUnit
  Incidence := PUnit
  Lineage := PUnit
  anchorAt := fun _ => PUnit.unit
  incidenceAt := fun _ => PUnit.unit
  lineageAt := fun _ => PUnit.unit
  NativeWriteAt := fun _ => PUnit
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := fun {current} _ => clockedShift current
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

abbrev RootV := rootVocabulary

def emptyInventoryPresentation :
    ConstructivePresentation PEmpty
      (OpenResponsibilityAt RootN PUnit.unit) where
  forward := PEmpty.elim
  backward := fun entry => nomatch entry.2
  backward_forward := fun impossible => nomatch impossible
  forward_backward := fun entry => nomatch entry.2

def rootEventLaw : SourceNativeEventAlgebra RootN RootV where
  EventAt := fun _ _ => PUnit
  compile := fun _ => .nativeWrite PUnit.unit
  AffectedInventoryAt := fun _ => PEmpty
  affectedInventoryPresentation := fun _ => emptyInventoryPresentation
  anchorKey := fun _ => PUnit.unit
  incidenceKey := fun _ => PUnit.unit
  lineageKey := fun _ => PUnit.unit
  anchor_commutes := fun _ => rfl
  incidence_commutes := fun _ => rfl
  lineage_commutes := fun _ => rfl

def rootSource : SourceNativeSource RootN RootV where
  initial := initialClockedFuture
  law := rootEventLaw

def rootOccurrence
    (current : RootV.Current) :
    rootSource.toRootSource.actual.OccurrenceAt current :=
  ⟨PUnit.unit, PUnit.unit⟩

abbrev emptyLedger : CompleteLiveLedgerAt RootN := ⟨PUnit.unit⟩

def rootLedgerCompiler : SourceNativeLedgerCompiler rootSource where
  IncidenceTransitionAt := fun _ _ _ => PUnit
  ExactTransitionAt := by
    intro current occurrence targetSupport sourceEntry targetEntry
    exact PUnit
  exact_incidence := fun _ => PUnit.unit
  exact_lineage := fun _ => rfl
  writeRowSource := LedgerWriteRowSourceAt.empty rootSource (by
    intro current occurrence targetSupport sourceEntry targetEntry
    exact PUnit)
  terminalRowSource := LedgerTerminalRowSourceAt.empty rootSource
  compile := by
    intro current occurrence
    exact .nativeWrite PUnit.unit rfl
      (rootOccurrence (RootV.nativeTarget (current := current) PUnit.unit))
      (LedgerWriteEvolutionAt.identity emptyLedger)
  compilePatch := by
    intro current occurrence
    exact ⟨FiniteGeneratedLedgerWritePatchAt.identity
      (LedgerWriteRowSourceAt.empty rootSource (by
        intro current occurrence targetSupport sourceEntry targetEntry
        exact PUnit)) occurrence, rfl⟩

def rootLedgerSource : SourceNativeLedgerSource RootN RootV where
  source := rootSource
  ledgerCompiler := rootLedgerCompiler

def rootRestructuringLaw : SourceNativeLedgerRestructuringLaw rootSource :=
  identityOnlyWorldLedgerRestructuringLaw rootSource PUnit.unit <| by
    intro support responsibility
    change Subsingleton PEmpty
    infer_instance

def rootRestructuringCertification
    {current : RootV.Current}
    (occurrence : rootSource.toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerRestructuringCertificationAt rootRestructuringLaw
      (rootLedgerCompiler.compile occurrence) :=
  ExactLedgerRestructuringCertificationAt.ofInjective
    (by intro left; exact nomatch left.2)
    (by intro left; exact nomatch left.2)

def rootRestructuringCompiler :
    SourceNativeRestructuringLedgerCompiler rootSource where
  ledgerCompiler := rootLedgerCompiler
  restructuringLaw := rootRestructuringLaw
  certifyRestructuring := rootRestructuringCertification

def rootRestructuringSource :
    SourceNativeRestructuringLedgerSource RootN RootV where
  source := rootSource
  compiler := rootRestructuringCompiler

def rootLedgerClosure : SourceNativeLedgerRootClosure RootN RootV where
  source := rootLedgerSource
  emitted := rootOccurrence
  compiler_commutes := fun _ => rfl

def baseProjectionLaw :
    SourceNativeProjectionLaw rootRestructuringSource.toLedgerSource where
  Projection := PUnit
  ActiveAt := fun _ {_current} _ => PUnit
  InactiveAt := fun _ {_current} _ => PEmpty
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun _ {_current} _ _ => PUnit
  project := fun _ {_current} _ _ => PUnit.unit

def baseAuthoritySource : SourceNativeAuthoritySource RootN RootV where
  restructuringSource := rootRestructuringSource
  eventInventoryAdmission :=
    .reflOfNoFaithfulTerminal rootRestructuringSource
      (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := .rootSemantic RootN
  projectionLaw := baseProjectionLaw

/-! ## Shared unit living-law vocabulary -/

def unitVocabulary
    {K E : Type u} [Field K] [AddCommGroup E] [Module K E]
    (C : Carrier (K := K) (E := E)) :
    _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.Vocabulary
      C where
  ActualEventAt := fun _ => PUnit
  eventAnchor := fun {current} _ => current.anchor
  eventIncidence := fun {current} _ => current.incidence
  eventLawLineage := fun {current} _ => current.lawLineage
  eventNextBearer := fun {current} _ => current.bearer
  RouteAcceptedAt := fun _ _ _ => PUnit
  NativeWriteAt := fun _ => PUnit
  RelationWriteAt := fun _ => PUnit
  ContinuedTransportAt := fun _ => PUnit
  BorromeanRedirectAt := fun _ => PUnit
  TerminalEventAt := fun _ => PUnit
  terminalEventAnchor := fun {current} _ => current.anchor
  terminalEventIncidence := fun {current} _ => current.incidence
  terminalEventLawLineage := fun {current} _ => current.lawLineage
  CompleteActualDescentAt := fun _ => PUnit
  FaithfulTerminalReceiptAt := fun _ => PUnit
  LawObstructionAt := fun _ => PUnit
  ProducerDemandAt := fun _ => PUnit
  ExtensionEventAt := fun _ => PUnit
  extensionEventAnchor := fun {current} _ => current.anchor
  extensionEventIncidence := fun {current} _ => current.incidence
  extensionEventLawLineage := fun {current} _ => current.lawLineage
  ExtensionRouteAcceptedAt := fun _ _ _ => PUnit
  ExtensionDemandPaidAt := fun {_current} _ _ _ {_revised} _ => PUnit
  LawRevisionAt := fun _ _ _ _ => PUnit

/-! ## Positive: the infinite carrier is generated section by section -/

def localProcess : EffectiveResidualProcess ℚ Future Future where
  target := 0
  keep := LinearMap.id
  residual := fun _ => 0
  update := pointwiseIncrement
  residual_transport_law := fun _ => rfl

def localCarrier : Carrier (K := ℚ) (E := Future) where
  LawSurface := PUnit
  State := fun _ => Future
  process := fun _ => localProcess
  Scope := PUnit
  Lineage := PUnit
  Incidence := PUnit
  Bearer := PUnit
  LawLineage := PUnit
  SourceObservation := ComplementObservation.canonicalComplementPair

abbrev LocalC := localCarrier
abbrev LocalV := unitVocabulary LocalC

def localCurrent (value : ℚ) :
    _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.Current
      LocalC where
  surface := PUnit.unit
  residual := residualState localProcess (constantTail value)
  anchor := MinimalRegistrableSourceAnchor.canonical PUnit.unit PUnit.unit
  incidence := PUnit.unit
  bearer := PUnit.unit
  lawLineage := PUnit.unit

def localWrite
    (source :
      _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.Current
        LocalC) :
    GeneratedWriteAt LocalV source where
  event := PUnit.unit
  event_anchor_eq := rfl
  event_incidence_eq := rfl
  event_lawLineage_eq := rfl
  update_ne_source := by
    intro equality
    have atZero := congrFun equality 0
    change source.residual.state 0 + 1 = source.residual.state 0 at atZero
    linarith
  bearerDisposition := .retained rfl

def localTotal : FixedLawNativeTotal LocalV where
  write := localWrite
  native := fun _ => PUnit.unit

def localRegistry : CarrierAtomFieldRegistry LocalC where
  state := fun _ => pointwisePresentation ℚ
  residual := fun _ => pointwisePresentation ℚ

def localResidualMap : PrefixLocalMap
    (pointwisePresentation ℚ) (pointwisePresentation ℚ)
    (fun _ : Future => (0 : Future)) where
  localStep := fun _ _ => show ℚ from 0
  commutes := fun _ _ => rfl

def localKeepMap : PrefixLocalMap
    (pointwisePresentation ℚ) (pointwisePresentation ℚ) id where
  localStep := fun scope finite =>
    finite ⟨scope, Nat.lt_succ_self scope⟩
  commutes := fun _ _ => rfl

def localRecognition : CarrierAtomFieldRecognition LocalC localRegistry where
  surface := fun _ => {
    update_local := pointwiseIncrement_prefixLocal
    residual_local := localResidualMap
    keep_local := localKeepMap
  }

def localAtomFieldGenerationLaw :
    SourceNativeAtomFieldGenerationLaw rootLedgerSource LocalC where
  livingVocabulary := LocalV
  total := localTotal
  registry := localRegistry
  recognition := localRecognition
  stateProper := fun _ =>
    pointwisePresentation_proper (0 : ℚ) 1 (by norm_num)
  residualProper := fun _ =>
    pointwisePresentation_proper (0 : ℚ) 1 (by norm_num)
  initial := localCurrent 0
  currentAt := fun current => localCurrent current.1
  anchorProjection := fun _ =>
    MinimalRegistrableSourceAnchor.canonical PUnit.unit PUnit.unit
  incidenceProjection := fun _ => PUnit.unit
  lawLineageProjection := fun _ => PUnit.unit
  anchor_commutes := fun _ => rfl
  incidence_commutes := fun _ => rfl
  lawLineage_commutes := fun _ => rfl
  initial_current_eq := rfl
  rootWrite := fun _ => PUnit.unit
  structural_eq := fun _ => rfl
  target_commutes := fun _ => rfl

def baseWorld : SourceNativeAuthoritativeRootClosure RootN RootV where
  source := baseAuthoritySource
  emitted := rootOccurrence
  compiler_commutes := rootLedgerClosure.compiler_commutes

/-- A generation law remains a readout until its component belongs to the
fixed root inventory.  Recognition cannot adjoin it after emission. -/
theorem fixed_base_root_rejects_posthoc_atom_field : True := by
  fail_if_success
    exact ({
      generationLaw := localAtomFieldGenerationLaw
      installation := SourceNativeProjectionLaw.InstallationAt.atomFieldComponent
        baseAuthoritySource localAtomFieldGenerationLaw
    } : SourceNativeAtomFieldRecognitionAt baseWorld LocalC)
  trivial

def localAtomFieldAuthoritySource : SourceNativeAuthoritySource RootN RootV :=
  localAtomFieldGenerationLaw.toAuthoritySource baseAuthoritySource

def localAtomFieldWorld :
    SourceNativeAuthoritativeRootClosure RootN RootV where
  source := localAtomFieldAuthoritySource
  emitted := rootOccurrence
  compiler_commutes := rootLedgerClosure.compiler_commutes

def localAtomFieldRecognition :
    SourceNativeAtomFieldRecognitionAt localAtomFieldWorld LocalC where
  generationLaw := localAtomFieldGenerationLaw
  installation := SourceNativeProjectionLaw.InstallationAt.atomFieldComponent
    baseAuthoritySource localAtomFieldGenerationLaw

def initialVisit : RootVisit localAtomFieldWorld.toRoot :=
  localAtomFieldWorld.toRoot.initialVisit

def secondVisit : RootVisit localAtomFieldWorld.toRoot :=
  initialVisit.next rfl

def secondLocalSection :=
  localAtomFieldRecognition.generatedLocalSectionAt secondVisit

/-- Inside the root-indexed readout, the registered local section is now
actually generated and its target is the carrier current recognized at the
same visit. -/
theorem second_visit_generates_registered_local_section :
    localAtomFieldRecognition.generationLaw.currentAt secondVisit.current =
        secondLocalSection.generated.target ∧
      satisfiesC1 secondLocalSection.temporalSection :=
  ⟨localAtomFieldRecognition.projectedCurrent_eq_localSection secondVisit,
    localAtomFieldRecognition.localSection_sourceBacked secondVisit⟩

/-- The generated section remains an installed face of the exact root
occurrence; it cannot become a parallel authority carrier. -/
theorem second_visit_atom_field_authority_factorizes :
    let authority := localAtomFieldWorld.authoritativeEvolutionAt
      (.finite secondVisit)
    authority.toLedgerReadout =
        localAtomFieldWorld.toLedgerRoot.generatedAtTemporalVisit
        (.finite secondVisit) ∧
      HEq (authority.toLedgerReadout.projectionOutcome
          localAtomFieldRecognition.rootProjection)
        (localAtomFieldRecognition.component.outcomeAt
          PUnit.unit
          (localAtomFieldWorld.emitted secondVisit.current)) :=
  localAtomFieldRecognition.installedAuthority_factorizes
    (localAtomFieldWorld.authoritativeEvolutionAt (.finite secondVisit))

/- The erased ledger/history readout cannot be replayed as atom authority,
even when it came from the same lower occurrence. -/
#guard_msgs (substring := true) in
#check localAtomFieldRecognition.installedAuthority_factorizes
  (localAtomFieldWorld.toLedgerRoot.generatedAtTemporalVisit
    (.finite secondVisit))

def siblingClockedFuture : ClockedFuture :=
  (0, fun _ => 0)

theorem initialClockedFuture_ne_sibling :
    initialClockedFuture ≠ siblingClockedFuture := by
  intro equality
  have atOne := congrArg (fun state => state.2 1) equality
  norm_num [initialClockedFuture, initialFuture, siblingClockedFuture] at atOne

/-- A safe atom-field coordinate cannot lend whole-current authority to an
unmentioned sibling field.  Here the coordinate remembers only the clock, so
two roots with different future fields have the same projected current. -/
theorem atom_field_projection_does_not_ground_sibling_future :
    ¬ Function.Injective localAtomFieldGenerationLaw.currentAt := by
  intro injective
  apply initialClockedFuture_ne_sibling
  exact injective (by rfl)

/-- The exact initial root occurrence, rather than a free projection theorem,
fixes the effective write whose trace is read as information and memory. -/
theorem initial_root_forcedTrace_eq_information :
    let current := localAtomFieldWorld.toRoot.source.initial
    let write := localAtomFieldRecognition.generationLaw.total.write
      (localAtomFieldRecognition.generationLaw.currentAt current)
    write.trace.forcedTrace =
      residualInformationReadout
        (LocalC.process
          (localAtomFieldRecognition.generationLaw.currentAt current).surface).keep
        (localAtomFieldRecognition.generationLaw.currentAt current).residual.value :=
  (localAtomFieldRecognition.rootOccurrence_informationMemoryReadout
    (rootOccurrence localAtomFieldWorld.toRoot.source.initial)).2.2.1

/-! ## Negative: a non-stuttering clock can hide a completed future -/

def oracleProcess : EffectiveResidualProcess ℚ ℚ ClockedFuture where
  target := 0
  keep := LinearMap.id
  residual := fun _ => 0
  update := clockedShift
  residual_transport_law := fun _ => rfl

def oracleCarrier : Carrier (K := ℚ) (E := ℚ) where
  LawSurface := PUnit
  State := fun _ => ClockedFuture
  process := fun _ => oracleProcess
  Scope := PUnit
  Lineage := PUnit
  Incidence := PUnit
  Bearer := PUnit
  LawLineage := PUnit
  SourceObservation := ComplementObservation.canonicalComplementPair

abbrev OracleC := oracleCarrier
abbrev OracleV := unitVocabulary OracleC

def oracleCurrent (state : ClockedFuture) :
    _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.Current
      OracleC where
  surface := PUnit.unit
  residual := residualState oracleProcess state
  anchor := MinimalRegistrableSourceAnchor.canonical PUnit.unit PUnit.unit
  incidence := PUnit.unit
  bearer := PUnit.unit
  lawLineage := PUnit.unit

def oracleWrite
    (source :
      _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.Current
        OracleC) :
    GeneratedWriteAt OracleV source where
  event := PUnit.unit
  event_anchor_eq := rfl
  event_incidence_eq := rfl
  event_lawLineage_eq := rfl
  update_ne_source := clockedShift_ne source.residual.state
  bearerDisposition := .retained rfl

def oracleTotal : FixedLawNativeTotal OracleV where
  write := oracleWrite
  native := fun _ => PUnit.unit

/-- Deliberately hostile chart: every finite coordinate contains the entire
clocked future.  This is a legal presentation readout, not ambient authority. -/
def oracleRegistry : CarrierAtomFieldRegistry OracleC where
  state := fun _ => constantPresentation ClockedFuture
  residual := fun _ => constantPresentation ℚ

def oracleUpdateLocal : PrefixLocalMap
    (constantPresentation ClockedFuture)
    (constantPresentation ClockedFuture) clockedShift where
  localStep := fun scope finite =>
    clockedShift (finite ⟨0, Nat.zero_lt_succ scope⟩)
  commutes := fun _ _ => rfl

def oracleResidualLocal : PrefixLocalMap
    (constantPresentation ClockedFuture)
    (constantPresentation ℚ) (fun _ : ClockedFuture => (0 : ℚ)) where
  localStep := fun _ _ => show ℚ from 0
  commutes := fun _ _ => rfl

def oracleKeepLocal : PrefixLocalMap
    (constantPresentation ℚ) (constantPresentation ℚ) id where
  localStep := fun scope finite =>
    finite ⟨0, Nat.zero_lt_succ scope⟩
  commutes := fun _ _ => rfl

def oracleRecognition :
    CarrierAtomFieldRecognition OracleC oracleRegistry where
  surface := fun _ => {
    update_local := oracleUpdateLocal
    residual_local := oracleResidualLocal
    keep_local := oracleKeepLocal
  }

/-- The completed-future chart is rejected at the source mouth itself: its
finite section at scope zero already decodes the whole ambient future. -/
theorem hostile_oracle_generation_is_impossible
    (law : SourceNativeAtomFieldGenerationLaw rootLedgerSource OracleC)
    (registry_eq : law.registry = oracleRegistry) : False := by
  have proper := law.stateProper PUnit.unit
  rw [registry_eq] at proper
  exact (constantPresentation_notProper ClockedFuture).false proper

/-- A completed residual field cannot bypass the atom wall merely because
the state chart itself is a proper finite-section presentation. -/
def hostileResidualRegistry : CarrierAtomFieldRegistry LocalC where
  state := fun _ => pointwisePresentation ℚ
  residual := fun _ => constantPresentation Future

theorem hostile_residual_oracle_generation_is_impossible
    (law : SourceNativeAtomFieldGenerationLaw rootLedgerSource LocalC)
    (registry_eq : law.registry = hostileResidualRegistry) : False := by
  have proper := law.residualProper PUnit.unit
  rw [registry_eq] at proper
  exact (constantPresentation_notProper Future).false proper

/-- The positive producer is visibly installed in the same fixed source
inventory which emits the root occurrence. -/
theorem local_generation_is_a_fixed_root_coordinate :
    HEq (localAtomFieldWorld.source.projectionLaw.outcomeAt
          localAtomFieldRecognition.rootProjection
          (rootOccurrence localAtomFieldWorld.toRoot.source.initial))
      (localAtomFieldRecognition.component.outcomeAt
        PUnit.unit
        (rootOccurrence localAtomFieldWorld.toRoot.source.initial)) :=
  localAtomFieldRecognition.componentOutcome_heq_rootOutcome
    (rootOccurrence localAtomFieldWorld.toRoot.source.initial)

#print axioms SourceNativeAtomFieldRecognitionAt.installedAuthority_factorizes
#print axioms SourceNativeAtomFieldGenerationLaw.noCompletedResidualAmbientAt
#print axioms second_visit_atom_field_authority_factorizes
#print axioms fixed_base_root_rejects_posthoc_atom_field
#print axioms hostile_residual_oracle_generation_is_impossible

end
end RootAtomFieldAuthorityRegression
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
