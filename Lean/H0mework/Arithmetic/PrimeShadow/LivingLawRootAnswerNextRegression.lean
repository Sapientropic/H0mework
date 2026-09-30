import H0mework.Foundation.Cofinal.TemporalAnswer
import H0mework.Arithmetic.PrimeShadow.LivingLawRootSourceNativeAuthorityRegression

/-!
# Regression: a faithful local terminal generates the next root

The old fixture has a compiler-generated whole-ledger terminal.  Its living
source fixes, before emission, a handoff event whose canonical target is the
existing source-native write root.  The public result retains the terminal as
the typed answer while exposing only the next generated current.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace RootAnswerNextRegression

open SourceNativeLedgerCompilerRegression
open SourceNativeRootAuthorityRegression

/-! The terminal side uses an actually empty source ledger.  Its finite
terminal patch therefore has no function-extensional compatibility proof:
the source-native producer, not a total readout equality, is the authority. -/

def constructiveTerminalInventoryPresentation :
    ConstructivePresentation PEmpty (OpenResponsibilityAt N true) where
  forward := PEmpty.elim
  backward := fun entry => nomatch entry.2
  backward_forward := fun value => nomatch value
  forward_backward := by
    rintro ⟨responsibility, openReceipt⟩
    nomatch openReceipt

inductive ConstructiveTerminalEventAt : Unit → Bool → Type
  | emitted : ConstructiveTerminalEventAt () true

def constructiveTerminalSourceLaw :
    SourceNativeEventAlgebra N TerminalV where
  EventAt := ConstructiveTerminalEventAt
  compile := fun _ => .faithfulTerminal ()
  AffectedInventoryAt := fun _ => PEmpty
  affectedInventoryPresentation := by
    intro current support event
    cases event
    exact constructiveTerminalInventoryPresentation
  anchorKey := fun _ => ()
  incidenceKey := fun _ => true
  lineageKey := fun _ => true
  anchor_commutes := by
    intro current support event
    cases event
    rfl
  incidence_commutes := by
    intro current support event
    cases event
    rfl
  lineage_commutes := by
    intro current support event
    cases event
    rfl

def constructiveTerminalSource : SourceNativeSource N TerminalV where
  initial := ()
  law := constructiveTerminalSourceLaw

def constructiveTerminalEmitted : (current : TerminalV.Current) →
    constructiveTerminalSource.toRootSource.actual.OccurrenceAt current :=
  fun _ => ⟨true, .emitted⟩

def constructiveTerminalWriteRowSource : LedgerWriteRowSourceAt
    constructiveTerminalSource (by
      intro current occurrence targetSupport sourceEntry targetEntry
      exact ExactPairTransition occurrence.1 targetSupport
        sourceEntry.1 targetEntry.1) where
  IncidenceOccurrenceAt := fun _ _ _ _ => PEmpty
  compileEvolution := fun {_} {_} {_} {_} {_} event => nomatch event
  compileExact := fun {_} {_} {_} {_} {_} event => nomatch event

def constructiveTerminalRowSource :
    LedgerTerminalRowSourceAt constructiveTerminalSource where
  IncidenceOccurrenceAt := fun _ _ => PEmpty
  compile := fun event => nomatch event

def constructiveTerminalFinitePatch : FiniteGeneratedLedgerTerminalPatchAt
    constructiveTerminalRowSource (constructiveTerminalEmitted ()) where
  size := 0
  entryAt := fun index => index.elim0
  rowAt := fun index => index.elim0
  entryIndex := fun entry => nomatch entry.2
  entry_sound := fun entry => nomatch entry.2

def constructiveTerminalLedgerCompiler :
    SourceNativeLedgerCompiler constructiveTerminalSource where
  IncidenceTransitionAt := fun _ sourceIncidence targetIncidence =>
    IncidenceStep sourceIncidence targetIncidence
  ExactTransitionAt := by
    intro current occurrence targetSupport sourceEntry targetEntry
    exact ExactPairTransition occurrence.1 targetSupport
      sourceEntry.1 targetEntry.1
  exact_incidence := by
    intro current occurrence targetSupport sourceEntry targetEntry exact
    exact ⟨ExactPairTransition.support_eq exact⟩
  exact_lineage := by
    intro current occurrence targetSupport sourceEntry targetEntry exact
    exact ExactPairTransition.support_eq exact
  writeRowSource := constructiveTerminalWriteRowSource
  terminalRowSource := constructiveTerminalRowSource
  compile := by
    intro current occurrence
    rcases occurrence with ⟨support, event⟩
    cases event
    exact .faithfulTerminal () rfl
      constructiveTerminalFinitePatch.toLedgerTerminalEvolution
  compilePatch := by
    intro current occurrence
    rcases occurrence with ⟨support, event⟩
    cases event
    exact ⟨.finite constructiveTerminalFinitePatch, rfl⟩

def constructiveTerminalRestructuringCompiler :
    SourceNativeRestructuringLedgerCompiler constructiveTerminalSource where
  ledgerCompiler := constructiveTerminalLedgerCompiler
  restructuringLaw := identityOnlyWorldLedgerRestructuringLaw
    constructiveTerminalSource () <| by
      intro support responsibility
      cases support
      · change Subsingleton Unit
        infer_instance
      · change Subsingleton PEmpty
        infer_instance
  certifyRestructuring := by
    intro current occurrence
    rcases occurrence with ⟨support, event⟩
    cases event
    exact PUnit.unit

def constructiveTerminalRestructuringSource :
    SourceNativeRestructuringLedgerSource N TerminalV where
  source := constructiveTerminalSource
  compiler := constructiveTerminalRestructuringCompiler

def constructiveTerminalProjectionLaw : SourceNativeProjectionLaw
    constructiveTerminalRestructuringSource.toLedgerSource where
  Projection := PUnit
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun _ {_} _ _ => PUnit
  project := fun _ {_} _ _ => PUnit.unit

def constructiveTerminalAuthoritySource :
    SourceNativeAuthoritySource N TerminalV where
  restructuringSource := constructiveTerminalRestructuringSource
  eventInventoryAdmission :=
    .reflOfNoActualSuccessor constructiveTerminalRestructuringSource <| by
      intro current
      refine ⟨?_⟩
      rintro ⟨occurrence, successor⟩
      rcases occurrence with ⟨support, event⟩
      cases event
      exact nomatch successor
  lawSurface := .rootSemantic N
  projectionLaw := constructiveTerminalProjectionLaw

def constructiveTerminalAuthorityWorld :
    SourceNativeAuthoritativeRootClosure N TerminalV where
  source := constructiveTerminalAuthoritySource
  emitted := constructiveTerminalEmitted
  compiler_commutes := fun _ => True.intro

def writeOccurrenceUnitPresentation : ConstructivePresentation
    ((boolWorld false).toRoot.actual.OccurrenceAt
      (boolWorld false).toRoot.source.initial) Unit where
  forward := fun _ => ()
  backward := fun _ =>
    (boolWorld false).emitted (boolWorld false).toRoot.source.initial
  backward_forward := by
    rintro ⟨support, event⟩
    cases event
    rfl
  forward_backward := by
    intro value
    cases value
    rfl

/-- The handoff compiler is part of the complete source identity before the
terminal root emitter is installed. -/
def terminalToWriteHandoff :
    SourceNativeTerminalHandoffLaw constructiveTerminalAuthoritySource :=
  SourceNativeTerminalHandoffLaw.create
    (fun {_current} _history {_occurrence} _terminal => Unit)
    (fun {_current} _history {_occurrence} _terminal => ())
    (fun _event => V)
    (fun _event => boolWorld false)
    (fun _event => writeOccurrenceUnitPresentation)
    (by
      intro current history occurrence terminal event
      cases event
      rfl)
    (by
      intro current history occurrence terminal event
      cases event
      rfl)
    (by
      intro current history occurrence terminal event targetEntry
      rcases occurrence with ⟨support, sourceEvent⟩
      cases sourceEvent
      exact .inr ⟨fun sourceEntry _sameDebt => nomatch sourceEntry.2⟩)
    (by
      intro current history occurrence terminal event sourceEntry targetEntry
        sameStanding
      rcases occurrence with ⟨support, sourceEvent⟩
      cases sourceEvent
      exact nomatch sourceEntry.2)
    (by
      intro current history occurrence terminal event sourceEntry left right
        leftIdentity rightIdentity
      rcases occurrence with ⟨support, sourceEvent⟩
      cases sourceEvent
      exact nomatch sourceEntry.2)

def livingTerminalSource : SourceNativeLivingAuthoritySource N TerminalV where
  base := constructiveTerminalAuthoritySource
  terminalHandoff := terminalToWriteHandoff

def livingTerminalRoot : SourceNativeLivingRootClosure N TerminalV where
  source := livingTerminalSource
  emitted := constructiveTerminalAuthorityWorld.emitted
  compiler_commutes := constructiveTerminalAuthorityWorld.compiler_commutes

def terminalVisit : RootVisit livingTerminalRoot.toAuthoritativeRoot.toRoot :=
  livingTerminalRoot.toAuthoritativeRoot.toRoot.initialVisit

def generated : SourceNativeAuthoritativeRootCurrentAt N :=
  livingTerminalRoot.generatedNextCurrentAt (.finite terminalVisit)

theorem terminal_generates_write_root :
    generated.V = V ∧ generated.root = boolWorld false :=
  ⟨rfl, rfl⟩

theorem old_terminal_is_typed_answer :
    livingTerminalRoot.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        terminalVisit.current = .faithfulTerminal () rfl
      constructiveTerminalFinitePatch.toLedgerTerminalEvolution :=
  rfl

theorem old_terminal_generates_next_current :
    generated.visit.current =
      (boolWorld false).toRoot.source.initial :=
  rfl

theorem old_terminal_is_answer_not_world_stop :
    livingTerminalRoot.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        terminalVisit.current = .faithfulTerminal () rfl
        constructiveTerminalFinitePatch.toLedgerTerminalEvolution ∧
      generated.visit.current =
        (boolWorld false).toRoot.source.initial :=
  ⟨old_terminal_is_typed_answer, old_terminal_generates_next_current⟩

/-- The handoff compiler consumes the exact finite causal history, not only
the terminal current label. -/
theorem terminal_handoff_history_is_finite :
    (livingTerminalRoot.terminalHistoryAt (.finite terminalVisit)).hasCofinalBoundary =
      false :=
  rfl

/-- Finite and post-cofinal terminal occurrences cannot share one causal
handoff index even when their current carriers happen to be equal. -/
theorem finite_and_postCofinal_handoff_histories_are_distinct
    {source : SourceNativeAuthoritySource N V}
    {current : V.Current}
    (finite : SourceNativeAuthorityFiniteHistoryAt source current)
    (postCofinal : SourceNativeAuthorityPostCofinalHistoryAt source current) :
    SourceNativeAuthorityTemporalHistoryAt.finite finite ≠
      SourceNativeAuthorityTemporalHistoryAt.postCofinal postCofinal := by
  intro equality
  cases equality

def exactTerminalOccurrence :
    SourceFaithfulTerminalOccurrenceAt constructiveTerminalAuthoritySource
      (constructiveTerminalEmitted ()) where
  terminal := ()
  structural_eq := rfl
  ledgerEvolution := constructiveTerminalFinitePatch.toLedgerTerminalEvolution
  generated_eq := rfl

theorem terminal_handoff_preserves_root_law_surface :
    generated.root.source.lawSurface =
      livingTerminalRoot.source.base.lawSurface :=
  livingTerminalRoot.generatedTerminalHandoff_lawSurface_eq
    (.finite terminalVisit) exactTerminalOccurrence

#print axioms SourceNativeLivingRootClosure.generatedTerminalHandoff_lawSurface_eq
#print axioms terminal_handoff_preserves_root_law_surface

/-- The target ledger is not accepted as an unclassified fresh world.  Every
row is checked against the complete old ledger; here it is genuinely fresh
because that ledger is constructively empty. -/
def terminalTargetDebtFresh
    (targetEntry : OpenResponsibilityAt N false) :
    RootDebtFreshAt N true targetEntry :=
  match livingTerminalRoot.generatedTerminalHandoff_targetDebtOrigin
      (.finite terminalVisit) exactTerminalOccurrence targetEntry with
  | .inl inherited => nomatch inherited.1.2
  | .inr fresh => fresh

/-- Relabelling responsibility while retaining lineage and claim cannot turn
an old row into a fresh debt. -/
theorem responsibility_relabel_cannot_mint_fresh_debt :
    IsEmpty (RootDebtFreshAt N false trueEntry) :=
  ⟨fun fresh => PEmpty.elim
    (fresh.excludesPrior falseEntry ⟨rfl, rfl⟩)⟩

/- A base authoritative root has no public next-current generator; it must
already carry the pre-emitter terminal-handoff source law. -/
/-- error: Invalid field `generatedNextCurrentAt` -/
#guard_msgs (substring := true) in
#check constructiveTerminalAuthorityWorld.generatedNextCurrentAt
  (.finite constructiveTerminalAuthorityWorld.toRoot.initialVisit)

end RootAnswerNextRegression
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
