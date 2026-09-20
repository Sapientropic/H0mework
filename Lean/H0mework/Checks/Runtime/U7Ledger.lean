import H0mework.Checks.Runtime.OperationalSeparation
import H0mework.Foundation.Authority.OperationalInstallation

/-!
# Operational cut / U7 root-ledger regression

The existing reverse-query cut is installed behind one source-native root
emitter.  Its generated U7 event must carry an exact entry of that occurrence's
complete live ledger and the source-generated root disposition.  No parallel
lifecycle obligation or `ResponsibilityState.empty` admission is exported.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace OperationalU7RootLedgerRegression

abbrev N := OperationalSeparationRegression.N
abbrev C := OperationalSeparationRegression.C
abbrev S := OperationalSeparationRegression.S
abbrev U7 := OperationalSeparationRegression.U7

def vocabulary : Vocabulary where
  Current := Unit
  Anchor := Unit
  Incidence := Unit
  Lineage := Unit
  anchorAt := fun _ => ()
  incidenceAt := fun _ => ()
  lineageAt := fun _ => ()
  NativeWriteAt := fun _ => Unit
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  cofinal :=
    { Event := Unit
      emit? := some ()
      pathAt := fun _ _ => ()
      target := fun _ => () }
  nativeTarget := fun _ => ()
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

abbrev V := vocabulary

def openPresentation (support : N.Support) :
    ConstructivePresentation Unit (OpenResponsibilityAt N support) where
  forward := fun _ => ⟨(), ()⟩
  backward := fun _ => ()
  backward_forward := fun _ => rfl
  forward_backward := by
    rintro ⟨responsibility, receipt⟩
    cases responsibility
    cases receipt
    rfl

def eventLaw : SourceNativeEventAlgebra N V where
  EventAt := fun _ support => match support with
    | false => PEmpty
    | true => Unit
  compile := by
    intro current support event
    cases support
    · exact nomatch event
    · exact .nativeWrite ()
  AffectedInventoryAt := fun _ => Unit
  affectedInventoryPresentation := by
    intro current support event
    cases support
    · exact nomatch event
    · exact openPresentation true
  anchorKey := fun _ => ()
  incidenceKey := fun _ => ()
  lineageKey := fun _ => ()
  anchor_commutes := by
    intro current support event
    cases support
    · exact nomatch event
    · rfl
  incidence_commutes := by
    intro current support event
    cases support
    · exact nomatch event
    · rfl
  lineage_commutes := by
    intro current support event
    cases support
    · exact nomatch event
    · rfl

def nativeSource : SourceNativeSource N V where
  initial := ()
  law := eventLaw

def emitted (_current : V.Current) :
    nativeSource.toRootSource.actual.OccurrenceAt () :=
  ⟨true, ()⟩

def rootEntry : OpenResponsibilityAt N true := ⟨(), ()⟩

theorem rootEntry_eq (entry : OpenResponsibilityAt N true) :
    rootEntry = entry := by
  rcases entry with ⟨responsibility, receipt⟩
  cases responsibility
  cases receipt
  rfl

def writeRowSource : LedgerWriteRowSourceAt nativeSource
    (fun _ _ _ _ => Unit) where
  IncidenceOccurrenceAt := fun _ _ sourceEntry targetEntry =>
    LedgerEntryEvolutionAt N sourceEntry targetEntry
  compileEvolution := fun event => event
  compileExact := fun _ => ()

def terminalRowSource : LedgerTerminalRowSourceAt nativeSource :=
  LedgerTerminalRowSourceAt.empty nativeSource

def generatedPatchWith
    (evolution : LedgerEntryEvolutionAt N rootEntry rootEntry)
    (occurrence : nativeSource.toRootSource.actual.OccurrenceAt ()) :
    FiniteGeneratedLedgerWritePatchAt writeRowSource occurrence
      ⟨nativeSource.toRootSource.account.supportOf occurrence⟩ := by
  rcases occurrence with ⟨support, event⟩
  cases support
  · exact nomatch event
  · exact .complete
      { size := 1
        sourceEntryAt := fun _ => rootEntry
        targetEntryAt := fun _ => rootEntry
        rowAt := fun _ => writeRowSource.generate evolution }
      { destinationIndex := fun _ => ⟨0, Nat.zero_lt_succ 0⟩
        originIndex := fun _ => ⟨0, Nat.zero_lt_succ 0⟩
        destination_sound := rootEntry_eq
        origin_sound := rootEntry_eq }

def generatedPatch
    (occurrence : nativeSource.toRootSource.actual.OccurrenceAt ()) :
    FiniteGeneratedLedgerWritePatchAt writeRowSource occurrence
      ⟨nativeSource.toRootSource.account.supportOf occurrence⟩ :=
  generatedPatchWith
    (OperationalSeparationRegression.u7TransferEvolution true) occurrence

def generatedRootEntryRow :
    (generatedPatch (emitted ())).CanonicalGeneratedSourceRowAt rootEntry :=
  ((generatedPatch (emitted ())).canonicalGeneratedSourceRow? rootEntry).get
    (by rfl)

def ledgerCompilerWith
    (evolution : LedgerEntryEvolutionAt N rootEntry rootEntry) :
    SourceNativeLedgerCompiler nativeSource where
  IncidenceTransitionAt := fun _ _ _ => Unit
  ExactTransitionAt := fun _ _ _ _ => Unit
  exact_incidence := fun _ => ()
  exact_lineage := fun _ => rfl
  writeRowSource := writeRowSource
  terminalRowSource := terminalRowSource
  compile := by
    intro current occurrence
    rcases occurrence with ⟨support, event⟩
    cases support
    · exact nomatch event
    · exact .nativeWrite () rfl ⟨true, event⟩
        (generatedPatchWith evolution ⟨true, event⟩).toLedgerWriteEvolution
  compilePatch := by
    intro current occurrence
    rcases occurrence with ⟨support, event⟩
    cases support
    · exact nomatch event
    · exact ⟨generatedPatchWith evolution ⟨true, event⟩, rfl⟩

def ledgerCompiler : SourceNativeLedgerCompiler nativeSource :=
  ledgerCompilerWith (OperationalSeparationRegression.u7TransferEvolution true)

def ledgerSource : SourceNativeLedgerSource N V where
  source := nativeSource
  ledgerCompiler := ledgerCompiler

abbrev settledU7Calculus : U7ObstructionEvolutionCalculus N U7 where
  source := OperationalSeparationRegression.u7Source
  compile := by
    intro support obstruction demand event
    exact
      { disposition := .settled ()
        demandEntryDisposition := ⟨⟨()⟩, rfl⟩ }

def settledU7Event :=
  settledU7Calculus.source.emit
    (S.cutObstruction OperationalSeparationRegression.CutEventAt.reverse)

/-- A subsystem settlement cannot borrow authority from a root compiler that
continues the same exact ledger entry. -/
theorem settled_u7_cannot_share_continuing_root_row :
    IsEmpty
      (U7DemandEntryRootDispositionCommutesAt settledU7Calculus
        settledU7Event rootEntry
        ((ledgerCompiler.compile (emitted ())).entryDisposition rootEntry)) := by
  constructor
  intro commutes
  rcases commutes with ⟨_, disposition_heq⟩
  change HEq (LedgerEntryDispositionAt.evolved _)
    (LedgerEntryDispositionAt.terminal _) at disposition_heq
  cases disposition_heq

def restructuringLaw : SourceNativeLedgerRestructuringLaw nativeSource :=
  identityOnlyWorldLedgerRestructuringLaw nativeSource () <| by
    intro support responsibility
    change Subsingleton Unit
    infer_instance

def restructuringCertificationWith
    (evolution : LedgerEntryEvolutionAt N rootEntry rootEntry)
    {current : V.Current}
    (occurrence : nativeSource.toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerRestructuringCertificationAt restructuringLaw
      ((ledgerCompilerWith evolution).compile occurrence) := by
  rcases occurrence with ⟨support, event⟩
  cases support
  · exact nomatch event
  · exact ExactLedgerRestructuringCertificationAt.ofInjective
      (fun _ _ equality => equality)
      (fun _ _ equality => equality)

def restructuringCertification
    {current : V.Current}
    (occurrence : nativeSource.toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerRestructuringCertificationAt restructuringLaw
      (ledgerCompiler.compile occurrence) :=
  restructuringCertificationWith
    (OperationalSeparationRegression.u7TransferEvolution true) occurrence

def restructuringCompilerWith
    (evolution : LedgerEntryEvolutionAt N rootEntry rootEntry) :
    SourceNativeRestructuringLedgerCompiler nativeSource where
  ledgerCompiler := ledgerCompilerWith evolution
  restructuringLaw := restructuringLaw
  certifyRestructuring := restructuringCertificationWith evolution

def restructuringCompiler :
    SourceNativeRestructuringLedgerCompiler nativeSource :=
  restructuringCompilerWith
    (OperationalSeparationRegression.u7TransferEvolution true)

def restructuringSourceWith
    (evolution : LedgerEntryEvolutionAt N rootEntry rootEntry) :
    SourceNativeRestructuringLedgerSource N V where
  source := nativeSource
  compiler := restructuringCompilerWith evolution

def restructuringSource : SourceNativeRestructuringLedgerSource N V :=
  restructuringSourceWith
    (OperationalSeparationRegression.u7TransferEvolution true)

def projectionLaw :
    SourceNativeProjectionLaw restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {_} _ _ => Unit
  project := fun _ {_} _ _ => ()

def authoritySource : SourceNativeAuthoritySource N V where
  restructuringSource := restructuringSource
  eventInventoryAdmission :=
    .reflOfNoFaithfulTerminal restructuringSource
      (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := .rootSemantic N
  projectionLaw := projectionLaw

def operationalLaw : SourceNativeOperationalSearchLaw ledgerSource where
  communication := C
  sources := S
  U7 := U7
  calculus := OperationalSeparationRegression.u7Calculus
  process := OperationalSeparationRegression.P
  positionAt := by
    intro current occurrence
    rcases occurrence with ⟨support, event⟩
    cases support
    · exact nomatch event
    · exact
        { source := true
          target := false
          query := OperationalSeparationRegression.reverseQuery
          searchCurrent := OperationalSeparationRegression.reverseInitial
          rootSupport_eq_frontier := rfl
          steps := 0
          history := OperationalSeparationRegression.reverseHistory0 }
  continuation_commutes := by
    intro current occurrence continuation
    rcases occurrence with ⟨support, event⟩
    cases support
    · exact nomatch event
    · cases continuation.emitted_eq
  cut_disposition_commutes := by
    intro current occurrence cutEvent emitted_eq
    rcases occurrence with ⟨support, event⟩
    cases support
    · exact nomatch event
    · cases current
      cases event
      cases cutEvent
      simp [U7DemandEntryRootDispositionCommutesAt,
        SourceNativeOperationalSearchPositionAt.rootDemandEntryAtCut,
        SourceNativeLedgerEvolutionAt.entryDisposition, ledgerSource,
        ledgerCompiler,
        OperationalSeparationRegression.u7Calculus,
        OperationalSeparationRegression.u7Source,
        U7ActualSuccessorSource.demandEntry]
      have evolution_heq := generatedRootEntryRow.evolution_heq_fold
      cases evolution_heq
      rfl

def root : SourceNativeLivingRootClosure N V where
  source :=
    { base := authoritySource.withOperationalSearch operationalLaw
      terminalHandoff :=
        (authoritySource.withOperationalSearch
          operationalLaw).emptyFaithfulTerminalHandoff
          (fun _ => ⟨fun terminal => nomatch terminal⟩) }
  emitted := emitted
  compiler_commutes := fun _ => rfl

def recognition : SourceNativeOperationalSearchRecognitionAt root where
  operationalLaw := operationalLaw
  installation := SourceNativeProjectionLaw.InstallationAt.operationalComponent
    authoritySource operationalLaw

def visit : RootVisit root.toAuthoritativeRoot.toRoot where
  current := ()
  history := .initial

def obstruction : SourceNativeOperationalObstructionAt
    recognition.operationalLaw (root.emitted visit.current) := by
  match outcome_eq : recognition.generatedTemporalOutcomeAt (.finite visit) with
  | .inl _ => cases outcome_eq
  | .inr (.inl obstruction) => exact obstruction
  | .inr (.inr _) => cases outcome_eq

def initialDemandEntryRow
    (generated : SourceNativeOperationalObstructionAt
      recognition.operationalLaw (root.emitted visit.current)) :
    (root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (.finite visit)).GeneratedEntryRowAt generated.rootDemandEntry :=
  ((root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
    (.finite visit)).canonicalGeneratedEntryRow?
      generated.rootDemandEntry).get (by rfl)

def initialDemandTemporalCausalAuthority
    (generated : SourceNativeOperationalObstructionAt
      recognition.operationalLaw (root.emitted visit.current)) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt root (.finite visit)
        generated.rootDemandEntry :=
  ((SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitial?
      root generated.rootDemandEntry .initial).get (by rfl)).2

theorem authority_emits_exact_obstruction :
    recognition.generatedTemporalOutcomeAt (.finite visit) =
      .inr (.inl obstruction) :=
  rfl

def demandIncidence :
    SourceNativeOperationalObstructionAt.SourceNativeRootU7DemandIncidenceAt
      (root := root)
      (.finite visit) obstruction :=
  recognition.generatedRootDemandIncidence (.finite visit) obstruction
    (initialDemandTemporalCausalAuthority obstruction)

def demandIncidence_answerAndNext :
    SourceNativeLivingCausalEntryAnswerAndNextAt root (.finite visit)
      obstruction.rootDemandEntry demandIncidence.causalEntryAuthority :=
  demandIncidence.answerAndNext

def productiveHistory : ProductiveFiniteRootHistoryAt
    root.toAuthoritativeRoot.toLedgerRoot where
  currentAt := fun _ => ()
  initial_eq := rfl
  next_eq := fun _ => rfl

def cofinalVisit : SourceNativeCofinalVisitAt
    root.toAuthoritativeRoot.toLedgerRoot :=
  (productiveHistory.generatedCofinalVisit? (fun _emitted_eq _index => rfl)).get
    (by rfl)

def cofinalObstruction : SourceNativeOperationalObstructionAt
    recognition.operationalLaw (root.emitted cofinalVisit.current) := by
  match outcome_eq : recognition.generatedTemporalOutcomeAt
      (.cofinal cofinalVisit) with
  | .inl _ => cases outcome_eq
  | .inr (.inl obstruction) => exact obstruction
  | .inr (.inr _) => cases outcome_eq

def cofinalDemandEntryRow :
    (root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (.cofinal cofinalVisit)).GeneratedEntryRowAt
        cofinalObstruction.rootDemandEntry :=
  ((root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (.cofinal cofinalVisit)).canonicalGeneratedEntryRow?
        cofinalObstruction.rootDemandEntry).get (by rfl)

def cofinalDemandCausalAuthority :
    SourceNativeLivingTemporalCausalEntryAuthorityAt root (.cofinal cofinalVisit)
        cofinalObstruction.rootDemandEntry :=
  (SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromCofinal?
    root cofinalVisit cofinalObstruction.rootDemandEntry).get (by rfl)

def cofinalDemandIncidence :
    SourceNativeOperationalObstructionAt.SourceNativeRootU7DemandIncidenceAt
      (root := root)
      (.cofinal cofinalVisit) cofinalObstruction :=
  recognition.generatedRootDemandIncidence (.cofinal cofinalVisit)
    cofinalObstruction cofinalDemandCausalAuthority

/-- A cofinal cut enters the same living answer-and-next compiler as a finite
cut.  Its exact boundary row supplies the causal authority index. -/
def cofinalDemandIncidence_answerAndNext :
    SourceNativeLivingCausalEntryAnswerAndNextAt root
      (.cofinal cofinalVisit) cofinalObstruction.rootDemandEntry
      cofinalDemandIncidence.causalEntryAuthority :=
  cofinalDemandIncidence.answerAndNext

/-- The U7 demand incidence retains its per-entry causal authority, not merely
the row visible at the current occurrence. -/
def demandIncidence_causalEntryAuthority :=
  demandIncidence.causalEntryAuthority

/-- The public incidence cannot recover a parallel lifecycle obligation or
classifier.  Removing the field is not enough unless these eliminators are
also absent from the exported type. -/
theorem demand_incidence_exposes_no_parallel_lifecycle : True := by
  fail_if_success exact demandIncidence.lifecycleObligation
  fail_if_success exact demandIncidence.lifecycleObligation_eq
  fail_if_success exact demandIncidence.canonicalLifecycleDisposition
  trivial

/-- The next causal visit is the distinct temporal occurrence generated by the
fixed root evolution. -/
def nextVisit : RootVisit root.toAuthoritativeRoot.toRoot :=
  visit.next (by rfl)

/-- Equal current, occurrence, and row payloads at a self-loop do not let the
initial temporal authority token masquerade as a row emitted at the successor
visit.  Renewal must pass through the causal constructor below. -/
theorem initial_row_cannot_replay_as_successor_row : True := by
  fail_if_success
    exact (initialDemandEntryRow obstruction :
      (root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
        (.finite nextVisit)).GeneratedEntryRowAt obstruction.rootDemandEntry)
  trivial

/-- The successor visit is authoritative because the predecessor demand was
already admitted and the complete ledger evolution transports that exact
entry.  The local patch does not readmit it. -/
def nextVisitDemandTemporalCausalAuthority :
    SourceNativeLivingTemporalCausalEntryAuthorityAt root (.finite nextVisit)
        obstruction.rootDemandEntry :=
  SourceNativeLivingTemporalCausalEntryAuthorityAt.next
    (initialDemandTemporalCausalAuthority obstruction) rfl

/-- Lookalike negative: complete-ledger membership plus an identity remainder
does not register the U7 demand.  The generated incidence row is essential. -/
theorem empty_identity_patch_cannot_register_u7_demand :
    IsEmpty
      (FiniteGeneratedLedgerWritePatchAt.GeneratedSourceEntryAt
        (FiniteGeneratedLedgerWritePatchAt.identity writeRowSource (emitted ()))
        obstruction.rootDemandEntry) := by
  constructor
  intro authority
  exact Fin.elim0 authority.1

end OperationalU7RootLedgerRegression
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
