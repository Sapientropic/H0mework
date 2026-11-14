import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.GoalCursor
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.InitialColourPass
import H0mework.Foundation.Ledger.SourceCompiler
import H0mework.Foundation.Ledger.ProofRelevantRestructuring
import H0mework.Foundation.Authority.Representation

/-!
The fixed 19x19 goal cursor is the source of every calculation event and target.
The complete ledger carries its single original critical-komi responsibility.
A terminal event contains the actual two-policy answer returned by the cursor.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.CalculationRuntime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

abbrev Current := GoalCursor.Current

def originalOccurrence := initialReplay19.toOccurrence

inductive Responsibility where
  | initialCriticalKomi

inductive Claim where
  | initialCriticalKomi

inductive OpenAt : Current → Responsibility → Type
  | original (current : Current) : OpenAt current .initialCriticalKomi

inductive CalculationAt : Current → Type
  | run (state : GoalCursor.State) : CalculationAt (.calculating state)

inductive TerminalAt : Current → Type
  | delivered (solution : ExactInitialMargin) : TerminalAt (.solved solution)

def TerminalAt.solution {current : Current} : TerminalAt current → ExactInitialMargin
  | .delivered solution => solution

def calculationTarget {current : Current} : CalculationAt current → Current
  | .run state => GoalCursor.generatedNext state

inductive NativeTransition : Current → Current → Type
  | generated (state : GoalCursor.State) :
      NativeTransition (.calculating state) (GoalCursor.generatedNext state)

def network : WorldRelationNetwork where
  Support := Current
  Anchor := RootedAccountedUnfolding (Frame 19)
  Incidence := Current
  Lineage := RootedAccountedUnfolding (Frame 19)
  Responsibility := Responsibility
  Claim := Claim
  anchorAt := fun _ => originalOccurrence
  incidenceAt := id
  lineageAt := fun _ => originalOccurrence
  OpenAt := OpenAt
  openClaimAt := fun _ => .initialCriticalKomi
  HoldsAt := fun _ _ => ExactInitialMargin
  ObstructionAt := fun _ => PEmpty
  obstructionClaim := fun impossible => nomatch impossible
  SemanticChangeAt := fun _ _ _ => PEmpty
  DispositionAt := fun current kind =>
    match kind with
    | .transfer => CalculationAt current
    | .supportSettlement => TerminalAt current
    | .lawSurfaceExtension => PEmpty

def ledgerAt (current : Current) : CompleteLiveLedgerAt network := ⟨current⟩

def entryAt (current : Current) : (ledgerAt current).Entry :=
  ⟨.initialCriticalKomi, .original current⟩

theorem entry_eq {current : Current} (entry : (ledgerAt current).Entry) :
    entry = entryAt current := by
  rcases entry with ⟨responsibility, opened⟩
  cases opened
  rfl

def inventory (current : Current) :
    ConstructivePresentation Responsibility (OpenResponsibilityAt network current) where
  forward := fun _ => entryAt current
  backward := fun _ => .initialCriticalKomi
  backward_forward := by intro responsibility; cases responsibility; rfl
  forward_backward := fun entry => (entry_eq entry).symm

def vocabulary : ConstructiveRoot.Vocabulary where
  Current := Current
  Anchor := RootedAccountedUnfolding (Frame 19)
  Incidence := Current
  Lineage := RootedAccountedUnfolding (Frame 19)
  anchorAt := fun _ => originalOccurrence
  incidenceAt := id
  lineageAt := fun _ => originalOccurrence
  NativeWriteAt := CalculationAt
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := TerminalAt
  nativeTarget := calculationTarget
  relationTarget := fun impossible => nomatch impossible
  continuedTarget := fun impossible => nomatch impossible
  redirectTarget := fun impossible => nomatch impossible

abbrev V := vocabulary

/-- Event identity retains the exact cursor current and its source-fixed support. -/
inductive EventAt : V.Current → network.Support → Type
  | calculate (state : GoalCursor.State) : EventAt (.calculating state) (.calculating state)
  | delivered (solution : ExactInitialMargin) : EventAt (.solved solution) (.solved solution)

def eventAlgebra : SourceNativeEventAlgebra network V where
  EventAt := EventAt
  compile := by
    intro current support event
    cases event with
    | calculate state => exact .nativeWrite (.run state)
    | delivered solution => exact .faithfulTerminal (.delivered solution)
  AffectedInventoryAt := fun _ => Responsibility
  affectedInventoryPresentation := by
    intro current support event
    cases event <;> exact inventory _
  anchorKey := id
  incidenceKey := id
  lineageKey := id
  anchor_commutes := by intro current support event; cases event <;> rfl
  incidence_commutes := by intro current support event; cases event <;> rfl
  lineage_commutes := by intro current support event; cases event <;> rfl

def source : SourceNativeSource network V where
  initial := GoalCursor.seed
  law := eventAlgebra

def emitted (current : V.Current) : source.toRootSource.actual.OccurrenceAt current :=
  ⟨current, match current with
    | .calculating state => .calculate state
    | .solved solution => .delivered solution⟩

def ExactTransitionAt {current : V.Current}
    (occurrence : source.toRootSource.actual.OccurrenceAt current)
    {targetSupport : network.Support}
    (_sourceEntry : OpenResponsibilityAt network occurrence.1)
    (_targetEntry : OpenResponsibilityAt network targetSupport) : Type :=
  NativeTransition occurrence.1 targetSupport

def writeRowSource : LedgerWriteRowSourceAt source ExactTransitionAt where
  IncidenceOccurrenceAt := fun {_current} occurrence {_targetSupport} _sourceEntry _targetEntry =>
    NativeTransition occurrence.1 _targetSupport
  compileEvolution := by
    intro current occurrence targetSupport sourceEntry targetEntry event
    rcases occurrence with ⟨support, sourceEvent⟩
    cases sourceEvent with
    | calculate state =>
        cases event
        exact .transferred (.run state) rfl rfl (Nat.le_refl _)
    | delivered solution => exact nomatch event
  compileExact := fun event => event

def writeRows (state : GoalCursor.State) : FiniteGeneratedLedgerWriteRowsAt
    writeRowSource (emitted (.calculating state)) (ledgerAt (GoalCursor.generatedNext state)) where
  size := 1
  sourceEntryAt := fun _ => entryAt (.calculating state)
  targetEntryAt := fun _ => entryAt (GoalCursor.generatedNext state)
  rowAt := fun _ => writeRowSource.generate (.generated state)

def writeCoverage (state : GoalCursor.State) :
    LedgerCompleteFiniteCoverageAt (writeRows state) where
  destinationIndex := fun _ => ⟨0, Nat.zero_lt_one⟩
  originIndex := fun _ => ⟨0, Nat.zero_lt_one⟩
  destination_sound := fun entry => (entry_eq entry).symm
  origin_sound := fun entry => (entry_eq entry).symm

def writePatch (state : GoalCursor.State) : FiniteGeneratedLedgerWritePatchAt
    writeRowSource (emitted (.calculating state)) (ledgerAt (GoalCursor.generatedNext state)) :=
  .complete (writeRows state) (writeCoverage state)

inductive SupportSettlementEventAt :
    {current : V.Current} → source.toRootSource.actual.OccurrenceAt current → Type
  | delivered (solution : ExactInitialMargin) :
      SupportSettlementEventAt (emitted (.solved solution))

def terminalRowSource : LedgerTerminalRowSourceAt source where
  IncidenceOccurrenceAt := fun _ _ => PEmpty
  compile := fun impossible => nomatch impossible
  supportSettlementSource := {
    OccurrenceAt := SupportSettlementEventAt
    emit? := by
      intro current occurrence
      rcases occurrence with ⟨support, event⟩
      cases event with
      | calculate state => exact none
      | delivered solution => exact some (.delivered solution)
    compile := by
      intro current occurrence event
      cases event with
      | delivered solution => exact .delivered solution
  }

def generatedTerminalSettlement (solution : ExactInitialMargin) :
    GeneratedLedgerSupportSettlementAt terminalRowSource (emitted (.solved solution)) :=
  (terminalRowSource.generateSupportSettlement? (emitted (.solved solution))).get (by rfl)

def terminalPatch (solution : ExactInitialMargin) :
    SourceGeneratedLedgerTerminalPatchAt terminalRowSource (emitted (.solved solution)) :=
  .supportSettlement (generatedTerminalSettlement solution)

def generatedLedger : {current : V.Current} →
    (occurrence : source.toRootSource.actual.OccurrenceAt current) →
      SourceNativeLedgerEvolutionAt source occurrence := by
  intro current occurrence
  rcases occurrence with ⟨support, event⟩
  cases event with
  | calculate state =>
      exact .nativeWrite (.run state) rfl (emitted (GoalCursor.generatedNext state))
        (writePatch state).toLedgerWriteEvolution
  | delivered solution =>
      exact .faithfulTerminal (.delivered solution) rfl
        (terminalPatch solution).toLedgerTerminalEvolution

def ledgerCompiler : SourceNativeLedgerCompiler source where
  IncidenceTransitionAt := fun _ before after => NativeTransition before after
  ExactTransitionAt := ExactTransitionAt
  exact_incidence := fun event => event
  exact_lineage := fun _ => rfl
  writeRowSource := writeRowSource
  terminalRowSource := terminalRowSource
  compile := generatedLedger
  compilePatch := by
    intro current occurrence
    rcases occurrence with ⟨support, event⟩
    cases event with
    | calculate state => exact ⟨writePatch state, rfl⟩
    | delivered solution => exact ⟨terminalPatch solution, rfl⟩

def ledgerSource : SourceNativeLedgerSource network V where
  source := source
  ledgerCompiler := ledgerCompiler

def ledgerRoot : SourceNativeLedgerRootClosure network V where
  source := ledgerSource
  emitted := emitted
  compiler_commutes := by
    intro current
    cases current with
    | calculating state => rfl
    | solved solution => trivial

theorem next_is_cursor (state : GoalCursor.State) :
    (ledgerRoot.toRoot.evolutionAt (.calculating state)).nextCurrent? =
      some (GoalCursor.generatedNext state) :=
  rfl

theorem original_source (current : Current) :
    ledgerRoot.toRoot.supportAt current = current ∧
      network.anchorAt current = initialReplay19.toOccurrence ∧
      network.lineageAt current = initialReplay19.toOccurrence := by
  constructor
  · cases current <;> rfl
  · exact ⟨rfl, rfl⟩

/-- The terminal receipt exposes the actual integer and the two executable policies. -/
def terminal_solution {current : Current}
    (terminal : network.DispositionAt current .supportSettlement) : ExactInitialMargin :=
  terminal.solution

def restructuringLaw : SourceNativeLedgerRestructuringLaw source :=
  RootGeneratedProofRelevantRestructuring.law network GoalCursor.seed source

def restructuringCertification {current : V.Current}
    (occurrence : source.toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerRestructuringCertificationAt restructuringLaw
      (ledgerCompiler.compile occurrence) := by
  rcases occurrence with ⟨support, event⟩
  cases event with
  | calculate state =>
      exact ExactLedgerRestructuringCertificationAt.ofInjective
        (fun left right _ => (entry_eq left).trans (entry_eq right).symm)
        (fun left right _ => (entry_eq left).trans (entry_eq right).symm)
  | delivered solution => exact PUnit.unit

def restructuringSource : SourceNativeRestructuringLedgerSource network V where
  source := source
  compiler := {
    ledgerCompiler := ledgerCompiler
    restructuringLaw := restructuringLaw
    certifyRestructuring := restructuringCertification
  }

def eventInventoryAdmission : SourceNativeCompleteEventInventoryAdmission restructuringSource :=
  .refl restructuringSource <| by
    intro current occurrence terminal terminal_eq
    cases terminal with
    | delivered solution =>
        constructor
        rintro ⟨⟨support, event⟩, outgoing⟩
        cases event
        exact nomatch outgoing

/-- This face records mathematical facts about the original value. It contains
no policy data and is never consumed as an executable Bracket receipt. -/
structure MathematicalRange where
  lower : Int
  upper : Int
  correct : ∀ solution : ExactInitialMargin,
    lower ≤ solution.value ∧ solution.value ≤ upper

def mathematicalRange : MathematicalRange :=
  ⟨0, 361, InitialColourPass.exact_value_bounds⟩

/-- The complete public face inventory of this fixed finite calculator. -/
inductive Face where
  | origin
  | current
  | solution
  | mathematicalBounds

def solutionAt? : Current → Option ExactInitialMargin
  | .calculating _ => none
  | .solved solution => some solution

def projectionLaw : SourceNativeProjectionLaw ledgerSource where
  Projection := Face
  ActiveAt := fun _ {_current} _occurrence => PUnit
  InactiveAt := fun _ {_current} _occurrence => PEmpty
  classify := fun _ {_current} _occurrence => .inl PUnit.unit
  PayloadAt := fun face {_current} _occurrence _active =>
    match face with
    | .origin => RootedAccountedUnfolding (Frame 19)
    | .current => Current
    | .solution => Option ExactInitialMargin
    | .mathematicalBounds => MathematicalRange
  project := by
    intro face current occurrence active
    cases face with
    | origin => exact originalOccurrence
    | current => exact occurrence.1
    | solution => exact solutionAt? occurrence.1
    | mathematicalBounds => exact mathematicalRange

def authoritySource : SourceNativeAuthoritySource network V where
  restructuringSource := restructuringSource
  eventInventoryAdmission := eventInventoryAdmission
  lawSurface := .rootSemantic network
  projectionLaw := projectionLaw

def authoritativeRoot : SourceNativeAuthoritativeRootClosure network V where
  source := authoritySource
  emitted := emitted
  compiler_commutes := ledgerRoot.compiler_commutes

abbrev Visit := RootVisit authoritativeRoot.toRoot

def seed : Visit := authoritativeRoot.toRoot.initialVisit

def nativeNext? : Current → Option Current
  | .calculating state => some (GoalCursor.generatedNext state)
  | .solved _ => none

theorem authoritative_next (current : Current) :
    (authoritativeRoot.toRoot.evolutionAt current).nextCurrent? = nativeNext? current := by
  cases current <;> rfl

/-- Finite observation uses only the fixed root's registered initial/next
constructors.  A genuine terminal returns immediately; zero fuel only ends
observation, and no post-terminal world is invented. -/
def run : Nat → Visit → Visit
  | 0, visit => visit
  | fuel + 1, visit =>
      match currentEq : visit.current with
      | .solved _ => visit
      | .calculating state =>
          run fuel (visit.next (by
            rw [currentEq]
            exact next_is_cursor state))

theorem run_current (fuel : Nat) (visit : Visit) :
    (run fuel visit).current = GoalCursor.observe fuel visit.current := by
  induction fuel generalizing visit with
  | zero => rfl
  | succ fuel ih =>
      rcases visit with ⟨current, history⟩
      cases current with
      | calculating state => exact ih _
      | solved solution => rfl

def observe (fuel : Nat) : Visit := run fuel seed

theorem observe_is_original_cursor (fuel : Nat) :
    (observe fuel).current = GoalCursor.observe fuel GoalCursor.seed :=
  run_current fuel seed

def temporalVisit (visit : Visit) : SourceNativeTemporalVisitAt authoritativeRoot.toLedgerRoot :=
  .finite visit

def authorityAt (visit : Visit) :=
  authoritativeRoot.authoritativeEvolutionAt (temporalVisit visit)

def faceAt (visit : Visit) (face : Face) :=
  (authorityAt visit).toLedgerReadout.projectionOutcome face

/-- Every exported face consumes the installed authority factorization in
the same proof as its complete ledger and original-program next. -/
theorem faceAt_factorizes (visit : Visit) (face : Face) :
    (authorityAt visit).toLedgerReadout =
        authoritativeRoot.toLedgerRoot.generatedAtTemporalVisit (temporalVisit visit) ∧
    (authorityAt visit).toLedgerReadout.occurrence = emitted visit.current ∧
    HEq (authorityAt visit).toLedgerReadout.wholeLedgerWriteBack
      (authoritativeRoot.generatedLedgerAt visit.current) ∧
    HEq (faceAt visit face) (projectionLaw.outcomeAt face (emitted visit.current)) ∧
    (authoritativeRoot.toRoot.evolutionAt visit.current).nextCurrent? = nativeNext? visit.current := by
  have factor := (authorityAt visit).installedSubsystemAuthority_factorizes
    (SourceNativeProjectionLaw.InstallationAt.refl projectionLaw) face
  exact ⟨factor.1, rfl,
    (authorityAt visit).toLedgerReadout.wholeLedgerWriteBack_eq,
    factor.2, authoritative_next visit.current⟩

/-- The same root consumes the head receipt and writes its generated next;
receipt admission is separate from proving a new initial strategy. -/
theorem received_next (current : GoalCursor.State) (bound : GoalBracket.InitialBound)
    (later : List GoalBracket.InitialBound) (received : current.received = bound :: later) :
    (authoritativeRoot.toRoot.evolutionAt (.calculating current)).nextCurrent? =
      some (match GoalCursor.absorb {current with received := later} bound with
        | .inl solution => .solved solution
        | .inr next => .calculating next) := by
  rw [authoritative_next]
  simp only [nativeNext?, GoalCursor.generatedNext, GoalCursor.advance_receipt current bound later received]
  rfl

def mathematicalAt (visit : Visit) : MathematicalRange :=
  projectionLaw.project .mathematicalBounds (emitted visit.current) PUnit.unit

theorem mathematicalAt_authority (visit : Visit) :
    HEq (faceAt visit .mathematicalBounds)
      (projectionLaw.outcomeAt .mathematicalBounds (emitted visit.current)) := by
  exact (faceAt_factorizes visit .mathematicalBounds).2.2.2.1

end SaturationMonoid.ProcessGame.Go.CriticalKomi.CalculationRuntime
