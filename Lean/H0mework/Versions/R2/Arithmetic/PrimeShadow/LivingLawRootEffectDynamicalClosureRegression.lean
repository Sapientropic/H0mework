import H0mework.Versions.R2.Foundation.Runtime.EffectDynamics
import H0mework.Versions.R2.Checks.Runtime.U7Ledger

/-!
# Root effect / dynamical closure regression

An occurrence-generated effect may continue only by recursively generating
the canonical target effect, operational state, whole-ledger transport, and
actual change or debit.  Otherwise the same live ledger row must be settled
or enter the source-native U7 cut.  A literal stutter cannot be relabelled as
progress.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace RootEffectDynamicalClosureRegression

open ConstructiveRoot
open ConstructiveRoot.OperationalU7RootLedgerRegression

abbrev U7Calculus := OperationalSeparationRegression.u7Calculus

abbrev SettledU7Calculus :
    U7ObstructionEvolutionCalculus
      OperationalSeparationRegression.N
      OperationalSeparationRegression.U7 where
  source := OperationalSeparationRegression.u7Source
  compile := by
    intro support obstruction demand event
    exact
      { disposition := .settled ()
        demandEntryDisposition := ⟨⟨()⟩, rfl⟩ }

def generatedEntryAt
    {current : V.Current}
    (occurrence : ledgerSource.source.toRootSource.actual.OccurrenceAt current) :
    SourceNativeEffectGeneratedEntryAt (source := ledgerSource)
      (occurrence := occurrence) rootEntry := by
  rcases occurrence with ⟨support, event⟩
  cases support
  · exact nomatch event
  · exact ⟨(sourceNativeFiniteLedgerPatchGeneratedEntry?
      nativeSource (fun _ _ _ _ => Unit) writeRowSource terminalRowSource
      (ledgerCompiler.compile ⟨true, event⟩)
      (ledgerCompiler.compilePatch ⟨true, event⟩) rootEntry).get (by rfl)⟩

def cutEventVocabulary : SourceNativeEffectEventVocabulary ledgerSource where
  Effect := Nat
  Operational := Unit
  effectAt := fun _ => 7
  operationalAt := fun _ => ()

def cutVocabulary : SourceNativeEffectDynamicalVocabulary cutEventVocabulary where
  ActiveAt := fun _ => Unit
  InactiveAt := fun _ => PEmpty
  classify := fun _ => .inl ()
  effectEntryAt := fun _ _ => rootEntry
  updateEffectAt := fun occurrence _ _ => occurrence.effect
  updateOperationalAt := fun occurrence _ _ _ => occurrence.operational

/-- Once the source event vocabulary is fixed, an exact effect occurrence
cannot be relabelled with a different complete effect value. -/
theorem source_native_effect_cannot_be_relabelled
    {current : V.Current}
    (occurrence : SourceNativeEffectOccurrenceAt cutEventVocabulary current) :
    occurrence.effect ≠ (8 : Nat) := by
  intro relabelled
  have sourceEffect_eq : occurrence.effect = (7 : Nat) :=
    occurrence.effect_eq
  exact (by decide : (7 : Nat) ≠ 8) (sourceEffect_eq.symm.trans relabelled)

/-- A literal self-loop with unchanged complete effect, unchanged operational
state, and unchanged budget cannot buy one more recurrence. -/
theorem stutter_has_no_recursive_effect_progress
    {current : V.Current}
    (occurrence : SourceNativeEffectOccurrenceAt cutEventVocabulary current)
    (sourceActive targetActive : cutVocabulary.ActiveAt occurrence) :
    IsEmpty (SourceNativeRecursiveEffectProgressAt cutVocabulary
      occurrence sourceActive occurrence targetActive) := by
  constructor
  intro progress
  cases progress with
  | effectChanged changed => exact changed rfl
  | operationalChanged changed => exact changed rfl
  | debited strictDebit =>
      have impossible :
          cutVocabulary.progressBudgetAt occurrence targetActive =
            cutVocabulary.progressBudgetAt occurrence sourceActive := by
        rfl
      exact (Nat.lt_irrefl _) (impossible ▸ strictDebit)

/-- A different structural occurrence still cannot buy recursive progress
when the complete effect, operational state, and source debit are unchanged. -/
theorem static_effect_has_no_recursive_progress_between_occurrences
    {sourceCurrent targetCurrent : V.Current}
    (sourceOccurrence :
      SourceNativeEffectOccurrenceAt cutEventVocabulary sourceCurrent)
    (targetOccurrence :
      SourceNativeEffectOccurrenceAt cutEventVocabulary targetCurrent)
    (sourceActive : cutVocabulary.ActiveAt sourceOccurrence)
    (targetActive : cutVocabulary.ActiveAt targetOccurrence) :
    IsEmpty (SourceNativeRecursiveEffectProgressAt cutVocabulary
      sourceOccurrence sourceActive targetOccurrence targetActive) := by
  constructor
  intro progress
  cases progress with
  | effectChanged changed =>
      exact changed (sourceOccurrence.effect_eq.trans
        targetOccurrence.effect_eq.symm)
  | operationalChanged changed =>
      exact changed (sourceOccurrence.operational_eq.trans
        targetOccurrence.operational_eq.symm)
  | debited strictDebit =>
      have impossible :
          cutVocabulary.progressBudgetAt targetOccurrence targetActive =
            cutVocabulary.progressBudgetAt sourceOccurrence sourceActive := by
        rfl
      exact (Nat.lt_irrefl _) (impossible ▸ strictDebit)

def cutLaw : SourceNativeEffectDynamicalClosureLaw ledgerSource :=
  .create OperationalSeparationRegression.U7 U7Calculus
    cutEventVocabulary cutVocabulary <| by
    intro current occurrence active
    rcases occurrence with ⟨lower⟩
    rcases lower with ⟨support, event⟩
    cases support
    · exact nomatch event
    · let successor :=
        (@SourceNativeEffectGeneratedSuccessorAt.ofGenerated? N V ledgerSource
          current ⟨true, event⟩
          (ledgerCompiler.compile ⟨true, event⟩)).get (by rfl)
      let row := generatedEntryAt ⟨true, event⟩
      refine .cut row successor () rfl ?_
      have commutes := row.down.commutes_with_world
      rcases commutes with ⟨_, evolution_heq⟩
      cases evolution_heq
      rfl

def relabelledEventVocabulary :
    SourceNativeEffectEventVocabulary ledgerSource where
  Effect := Nat
  Operational := Unit
  effectAt := fun _ => 8
  operationalAt := fun _ => ()

def relabelledVocabulary :
    SourceNativeEffectDynamicalVocabulary relabelledEventVocabulary where
  ActiveAt := fun _ => PEmpty
  InactiveAt := fun _ => Unit
  classify := fun _ => .inr ()
  effectEntryAt := fun _ active => nomatch active
  updateEffectAt := fun _ active _ => nomatch active
  updateOperationalAt := fun _ active _ _ => nomatch active

def relabelledLaw : SourceNativeEffectDynamicalClosureLaw ledgerSource :=
  .create OperationalSeparationRegression.U7 U7Calculus
    relabelledEventVocabulary relabelledVocabulary <| by
      intro _current _occurrence active
      exact nomatch active

/-- The same exact root row cannot continue while its U7 demand is declared
globally settled.  Settlement must come from the source terminal ledger, not
from a second disposition compiler attached to a continuing cut. -/
theorem settled_u7_cannot_double_book_a_continuing_effect_row
    {current : V.Current}
    (occurrence : SourceNativeEffectOccurrenceAt cutEventVocabulary current)
    (active : cutVocabulary.ActiveAt occurrence)
    (successor : SourceNativeEffectGeneratedSuccessorAt occurrence.lower
      (ledgerCompiler.compile occurrence.lower))
    (obstruction : OperationalSeparationRegression.N.ObstructionAt
      (ledgerSource.source.toRootSource.account.supportOf occurrence.lower)) :
    IsEmpty (SourceNativeEffectU7CutCommutesAt (active := active)
      cutVocabulary SettledU7Calculus successor obstruction) := by
  constructor
  intro commutes
  rcases occurrence with ⟨lower⟩
  rcases lower with ⟨support, event⟩
  cases support
  · exact nomatch event
  · change HEq (LedgerEntryDispositionAt.evolved _)
      (LedgerEntryDispositionAt.terminal _) at commutes
    cases commutes

def effectSource : SourceNativeLivingAuthoritySource N V where
  base := cutLaw.toAuthoritySource
    ConstructiveRoot.OperationalU7RootLedgerRegression.authoritySource
  terminalHandoff :=
    (cutLaw.toAuthoritySource
      ConstructiveRoot.OperationalU7RootLedgerRegression.authoritySource)
      |>.emptyFaithfulTerminalHandoff
        (fun _ => ⟨fun terminal => nomatch terminal⟩)

def world : SourceNativeLivingRootClosure N V where
  source := effectSource
  emitted := emitted
  compiler_commutes := fun _ => rfl

def recognition : SourceNativeEffectDynamicalRecognitionAt world where
  effectLaw := cutLaw
  installation :=
    SourceNativeProjectionLaw.InstallationAt.effectDynamicalComponent
      ConstructiveRoot.OperationalU7RootLedgerRegression.authoritySource cutLaw

/-- A fixed living root rejects a sibling effect vocabulary absent from its
source projection inventory. -/
theorem fixed_living_root_rejects_sibling_effect_recognition : True := by
  fail_if_success
    exact ({
      effectLaw := relabelledLaw
      installation :=
        SourceNativeProjectionLaw.InstallationAt.effectDynamicalComponent
          ConstructiveRoot.OperationalU7RootLedgerRegression.authoritySource
          relabelledLaw
    } : SourceNativeEffectDynamicalRecognitionAt world)
  trivial

def visit : SourceNativeTemporalVisitAt
    world.toAuthoritativeRoot.toLedgerRoot :=
  .finite world.toAuthoritativeRoot.toRoot.initialVisit

def sourceAuthority : recognition.CausalEntryAuthorityAt visit rootEntry :=
  ((SourceNativeEffectDynamicalRecognitionAt.CausalEntryAuthorityAt.generatedFromInitial?
      recognition rootEntry .initial).get
      (by rfl)).2

def rootedActive : recognition.RootedActiveOutcomeAt visit :=
  recognition.generatedRootedActiveAtVisit visit () rfl sourceAuthority

/-- Re-registering the same installed effect face cannot change its complete
source-generated disposition, even when the active fibre is proof-relevant. -/
theorem fixed_visit_effect_disposition_is_unique
    (left right : recognition.RootedActiveOutcomeAt visit) :
    HEq left.payload right.payload :=
  left.payload_heq_of_same_visit right

theorem cut_effect_factorizes_through_root :
    let evolution := world.canonicalCausalAnswerAndNext
      (ULift.up visit)
    evolution.generated =
        world.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
          visit ∧
      HEq (evolution.generated.projectionOutcome
          recognition.rootEffectProjection)
        rootedActive.installedFiber ∧
      evolution.nextCurrent = world.generatedNextCurrentAt visit :=
  rootedActive.installedAuthority_factorizes

def cutClosure : rootedActive.CausalCutClosureAt := by
  change rootedActive.CausalClosureAt
  exact rootedActive.generatedCausalClosure

def cutCausalSuccessor : rootedActive.CausalSuccessorAt :=
  cutClosure.1

def cutU7SourceAuthority := cutClosure.2

def cutTargetAuthority : recognition.CausalEntryAuthorityAt
      cutCausalSuccessor.successor.targetVisit
      cutCausalSuccessor.successor.targetEntry :=
  cutCausalSuccessor.targetAuthority

/-- Even the correct source-local outcome cannot be wrapped as temporal
authority without passing through the registered visit constructor. -/
theorem raw_projection_is_not_registered_authority : True := by
  fail_if_success
    exact ({ active := ()
             sourceAuthority := sourceAuthority } :
      recognition.RootedActiveOutcomeAt visit)
  trivial

/-- A caller cannot install another effect law on the already emitted generic
root and then ask the authority API to accept it as the joint source. -/
theorem posthoc_effect_recognition_is_not_authority : True := by
  fail_if_success
    exact ({ effectLaw := cutLaw
             installation :=
               SourceNativeProjectionLaw.InstallationAt.effectDynamicalComponent
                 ConstructiveRoot.OperationalU7RootLedgerRegression.authoritySource
                 cutLaw } :
      SourceNativeEffectDynamicalRecognitionAt
        ConstructiveRoot.OperationalU7RootLedgerRegression.world)
  trivial

/-- A sibling effect source may erase to the same primitive ledger root, but
its causal authority remains a different dependent type.  The original
source's admitted row cannot be replayed through the sibling law. -/
def relabelledEffectSource : SourceNativeLivingAuthoritySource N V where
  base := relabelledLaw.toAuthoritySource
    ConstructiveRoot.OperationalU7RootLedgerRegression.authoritySource
  terminalHandoff :=
    (relabelledLaw.toAuthoritySource
      ConstructiveRoot.OperationalU7RootLedgerRegression.authoritySource)
      |>.emptyFaithfulTerminalHandoff
        (fun _ => ⟨fun terminal => nomatch terminal⟩)

def relabelledWorld : SourceNativeLivingRootClosure N V where
  source := relabelledEffectSource
  emitted := emitted
  compiler_commutes := fun _ => rfl

def relabelledRecognition :
    SourceNativeEffectDynamicalRecognitionAt relabelledWorld where
  effectLaw := relabelledLaw
  installation :=
    SourceNativeProjectionLaw.InstallationAt.effectDynamicalComponent
      ConstructiveRoot.OperationalU7RootLedgerRegression.authoritySource
      relabelledLaw

def relabelledVisit : SourceNativeTemporalVisitAt
    relabelledWorld.toAuthoritativeRoot.toLedgerRoot :=
  .finite relabelledWorld.toAuthoritativeRoot.toRoot.initialVisit

theorem sibling_effect_source_cannot_replay_causal_authority : True := by
  fail_if_success
    exact (sourceAuthority : relabelledRecognition.CausalEntryAuthorityAt
      relabelledVisit rootEntry)
  trivial

def isNext
    {current : V.Current}
    {occurrence : SourceNativeEffectOccurrenceAt cutEventVocabulary current}
    {active : cutVocabulary.ActiveAt occurrence}
    {generated : SourceNativeLedgerEvolutionAt ledgerSource.source occurrence.lower}
    (disposition : SourceNativeEffectDynamicalDispositionAt cutVocabulary
      U7Calculus occurrence active generated) : Type :=
  match disposition with
  | .next .. => PUnit
  | .settled .. | .cut .. => PEmpty

theorem stutter_disposition_cannot_claim_next
    {current : V.Current}
    {occurrence : SourceNativeEffectOccurrenceAt cutEventVocabulary current}
    {active : cutVocabulary.ActiveAt occurrence}
    {generated : SourceNativeLedgerEvolutionAt ledgerSource.source occurrence.lower}
    (disposition : SourceNativeEffectDynamicalDispositionAt cutVocabulary
      U7Calculus occurrence active generated) : IsEmpty (isNext disposition) := by
  cases disposition with
  | settled => exact ⟨fun value => nomatch value⟩
  | next row successor targetActive target_classify_eq ledgerTransport
      effect_commutes operational_commutes progress =>
      exact ⟨fun _ => by
        cases progress with
        | effectChanged changed =>
            apply changed
            have sourceEffect_eq : occurrence.effect = (7 : Nat) :=
              occurrence.effect_eq
            exact sourceEffect_eq.trans (by rfl)
        | operationalChanged changed =>
            apply changed
            exact occurrence.operational_eq.trans (by rfl)
        | debited strictDebit =>
            have impossible :
                cutVocabulary.progressBudgetAt
                    (SourceNativeEffectEventVocabulary.emit
                      cutEventVocabulary successor.targetOccurrence)
                    targetActive =
                  cutVocabulary.progressBudgetAt
                    occurrence active := by
              rfl
            exact (Nat.lt_irrefl _) (impossible ▸ strictDebit)⟩
  | cut => exact ⟨fun value => nomatch value⟩

def isCut
    {current : V.Current}
    {occurrence : SourceNativeEffectOccurrenceAt cutEventVocabulary current}
    {active : cutVocabulary.ActiveAt occurrence}
    {generated : SourceNativeLedgerEvolutionAt ledgerSource.source occurrence.lower}
    (disposition : SourceNativeEffectDynamicalDispositionAt cutVocabulary
      U7Calculus occurrence active generated) : Prop :=
  match disposition with
  | .cut .. => True
  | .settled .. | .next .. => False

/-- For the actual continuing compiler used by this regression, a static
complete effect cannot hide behind an empty cut vocabulary.  Exhaustiveness
forces every lawful disposition to be the exact U7 cut. -/
theorem static_effect_disposition_must_cut
    {current : V.Current}
    (occurrence : SourceNativeEffectOccurrenceAt cutEventVocabulary current)
    (active : cutVocabulary.ActiveAt occurrence)
    (disposition : SourceNativeEffectDynamicalDispositionAt cutVocabulary
      U7Calculus occurrence active
        (ledgerCompiler.compile occurrence.lower)) : isCut disposition := by
  cases disposition with
  | settled terminal =>
      rcases occurrence with ⟨lower⟩
      rcases lower with ⟨support, event⟩
      cases support
      · exact nomatch event
      · exact nomatch terminal
  | next row successor targetActive target_classify_eq ledgerTransport
      effect_commutes operational_commutes progress =>
      exact False.elim
        ((static_effect_has_no_recursive_progress_between_occurrences
          occurrence
          (cutEventVocabulary.emit successor.targetOccurrence)
          active targetActive).false progress)
  | cut => trivial

namespace RecursiveNext

abbrev RecursiveN := ConstructiveRoot.OperationalU7RootLedgerRegression.N

def recursiveVocabulary : ConstructiveRoot.Vocabulary where
  Current := Bool
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
  nativeTarget := fun {current} _ => !current
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

abbrev RecursiveV := recursiveVocabulary

def recursiveEventLaw : SourceNativeEventAlgebra RecursiveN RecursiveV where
  EventAt := fun _ support => if support then Unit else PEmpty
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
    · exact ConstructiveRoot.OperationalU7RootLedgerRegression.openPresentation true
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

def recursiveNativeSource : SourceNativeSource RecursiveN RecursiveV where
  initial := false
  law := recursiveEventLaw

def recursiveEmitted (current : RecursiveV.Current) :
    recursiveNativeSource.toRootSource.actual.OccurrenceAt current :=
  ⟨true, ()⟩

abbrev recursiveEntry : OpenResponsibilityAt RecursiveN true :=
  ConstructiveRoot.OperationalU7RootLedgerRegression.rootEntry

def recursiveWriteRowSource : LedgerWriteRowSourceAt recursiveNativeSource
    (fun _ _ _ _ => Unit) where
  IncidenceOccurrenceAt := fun _ _ sourceEntry targetEntry =>
    LedgerEntryEvolutionAt RecursiveN sourceEntry targetEntry
  compileEvolution := fun event => event
  compileExact := fun _ => ()

def recursiveTerminalRowSource : LedgerTerminalRowSourceAt recursiveNativeSource :=
  LedgerTerminalRowSourceAt.empty recursiveNativeSource

def recursivePatch
    {current : RecursiveV.Current}
    (occurrence :
      recursiveNativeSource.toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWritePatchAt recursiveWriteRowSource occurrence
      ⟨recursiveNativeSource.toRootSource.account.supportOf occurrence⟩ := by
  rcases occurrence with ⟨support, event⟩
  cases support
  · exact nomatch event
  · exact .identityRemainder
      { size := 1
        sourceEntryAt := fun _ => recursiveEntry
        targetEntryAt := fun _ => recursiveEntry
        rowAt := fun _ =>
          recursiveWriteRowSource.generate
            (.transferred () rfl rfl (Nat.le_refl _)) }
      { destinationIndex := fun entry =>
          some ⟨⟨0, Nat.zero_lt_succ 0⟩,
            ConstructiveRoot.OperationalU7RootLedgerRegression.rootEntry_eq
              entry⟩
        originIndex := fun entry =>
          some ⟨⟨0, Nat.zero_lt_succ 0⟩,
            ConstructiveRoot.OperationalU7RootLedgerRegression.rootEntry_eq
              entry⟩ }

def recursiveLedgerCompiler :
    SourceNativeLedgerCompiler recursiveNativeSource where
  IncidenceTransitionAt := fun _ _ _ => Unit
  ExactTransitionAt := fun _ _ _ _ => Unit
  exact_incidence := fun _ => ()
  exact_lineage := fun _ => rfl
  writeRowSource := recursiveWriteRowSource
  terminalRowSource := recursiveTerminalRowSource
  compile := by
    intro current occurrence
    rcases occurrence with ⟨support, event⟩
    cases support
    · exact nomatch event
    · exact .nativeWrite () rfl (recursiveEmitted (!current))
        (recursivePatch ⟨true, event⟩).toLedgerWriteEvolution
  compilePatch := by
    intro current occurrence
    rcases occurrence with ⟨support, event⟩
    cases support
    · exact nomatch event
    · exact ⟨recursivePatch ⟨true, event⟩, rfl⟩

def recursiveLedgerSource : SourceNativeLedgerSource RecursiveN RecursiveV where
  source := recursiveNativeSource
  ledgerCompiler := recursiveLedgerCompiler

def recursiveGeneratedEntryAt
    {current : RecursiveV.Current}
    (occurrence :
      recursiveNativeSource.toRootSource.actual.OccurrenceAt current) :
    SourceNativeEffectGeneratedEntryAt (source := recursiveLedgerSource)
      (occurrence := occurrence) recursiveEntry := by
  rcases occurrence with ⟨support, event⟩
  cases support
  · exact nomatch event
  · exact ⟨(sourceNativeFiniteLedgerPatchGeneratedEntry?
      recursiveNativeSource (fun _ _ _ _ => Unit) recursiveWriteRowSource
      recursiveTerminalRowSource
      (recursiveLedgerCompiler.compile ⟨true, event⟩)
      (recursiveLedgerCompiler.compilePatch ⟨true, event⟩)
      recursiveEntry).get (by rfl)⟩

def recursiveRestructuringLaw :
    SourceNativeLedgerRestructuringLaw recursiveNativeSource :=
  identityOnlyWorldLedgerRestructuringLaw recursiveNativeSource () <| by
    intro support responsibility
    cases support
    · change Subsingleton Unit
      infer_instance
    · change Subsingleton Unit
      infer_instance

theorem recursiveOpenEntry_eq
    {support : RecursiveN.Support}
    (left right : OpenResponsibilityAt RecursiveN support) : left = right := by
  rcases left with ⟨leftResponsibility, leftOpen⟩
  rcases right with ⟨rightResponsibility, rightOpen⟩
  cases leftResponsibility
  cases rightResponsibility
  cases leftOpen
  cases rightOpen
  rfl

def recursiveRestructuringCompiler :
    SourceNativeRestructuringLedgerCompiler recursiveNativeSource where
  ledgerCompiler := recursiveLedgerCompiler
  restructuringLaw := recursiveRestructuringLaw
  certifyRestructuring := by
    intro current occurrence
    rcases occurrence with ⟨support, event⟩
    cases support
    · exact nomatch event
    · exact ExactLedgerRestructuringCertificationAt.ofInjective
        (fun left right _ => recursiveOpenEntry_eq left right)
        (fun left right _ => recursiveOpenEntry_eq left right)

def recursiveRestructuringSource :
    SourceNativeRestructuringLedgerSource RecursiveN RecursiveV where
  source := recursiveNativeSource
  compiler := recursiveRestructuringCompiler

def recursiveBaseProjection :
    SourceNativeProjectionLaw recursiveLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {_} _ _ => Unit
  project := fun _ {_} _ _ => ()

def recursiveBaseAuthority : SourceNativeAuthoritySource RecursiveN RecursiveV where
  restructuringSource := recursiveRestructuringSource
  eventInventoryAdmission :=
    .reflOfNoFaithfulTerminal recursiveRestructuringSource
      (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := .rootSemantic RecursiveN
  projectionLaw := recursiveBaseProjection

def recursiveEffectEventVocabulary :
    SourceNativeEffectEventVocabulary recursiveLedgerSource where
  Effect := Bool
  Operational := Bool
  effectAt := fun {current} _ => current
  operationalAt := fun {current} _ => current

def recursiveEffectVocabulary :
    SourceNativeEffectDynamicalVocabulary recursiveEffectEventVocabulary where
  ActiveAt := fun _ => Unit
  InactiveAt := fun _ => PEmpty
  classify := fun _ => .inl ()
  effectEntryAt := fun _ _ => recursiveEntry
  updateEffectAt := fun _ _ sourceEffect => !sourceEffect
  updateOperationalAt := fun _ _ _ sourceOperational =>
    !sourceOperational

theorem bool_ne_not (value : Bool) : value ≠ !value := by
  cases value <;> decide

def recursiveEffectLaw :
    SourceNativeEffectDynamicalClosureLaw recursiveLedgerSource :=
  .create OperationalSeparationRegression.U7 U7Calculus
    recursiveEffectEventVocabulary recursiveEffectVocabulary <| by
      intro current occurrence active
      rcases occurrence with ⟨lower⟩
      rcases lower with ⟨support, event⟩
      cases support
      · exact nomatch event
      · let successor :=
          (@SourceNativeEffectGeneratedSuccessorAt.ofGenerated? RecursiveN
            RecursiveV recursiveLedgerSource current ⟨true, event⟩
            (recursiveLedgerCompiler.compile ⟨true, event⟩)).get (by rfl)
        have targetEntry_eq :
            (successor.ledgerEvolution.destination recursiveEntry).1 =
              recursiveEntry :=
          ConstructiveRoot.OperationalU7RootLedgerRegression.rootEntry_eq _
        exact .next (recursiveGeneratedEntryAt ⟨true, event⟩)
          successor () rfl ⟨targetEntry_eq⟩
          (by cases current <;> rfl) (by cases current <;> rfl)
          (.effectChanged (fun equality =>
            bool_ne_not current equality))

def recursiveEffectSource :
    SourceNativeLivingAuthoritySource RecursiveN RecursiveV where
  base := recursiveEffectLaw.toAuthoritySource recursiveBaseAuthority
  terminalHandoff :=
    (recursiveEffectLaw.toAuthoritySource recursiveBaseAuthority)
      |>.emptyFaithfulTerminalHandoff
        (fun _ => ⟨fun terminal => nomatch terminal⟩)

def recursiveWorld :
    SourceNativeLivingRootClosure RecursiveN RecursiveV where
  source := recursiveEffectSource
  emitted := recursiveEmitted
  compiler_commutes := fun _ => rfl

def recursiveRecognition :
    SourceNativeEffectDynamicalRecognitionAt recursiveWorld where
  effectLaw := recursiveEffectLaw
  installation :=
    SourceNativeProjectionLaw.InstallationAt.effectDynamicalComponent
      recursiveBaseAuthority recursiveEffectLaw

def recursiveVisit : SourceNativeTemporalVisitAt
    recursiveWorld.toAuthoritativeRoot.toLedgerRoot :=
  .finite recursiveWorld.toAuthoritativeRoot.toRoot.initialVisit

def recursiveSourceAuthority : recursiveRecognition.CausalEntryAuthorityAt
    recursiveVisit recursiveEntry :=
  ((SourceNativeEffectDynamicalRecognitionAt.CausalEntryAuthorityAt.generatedFromInitial?
      recursiveRecognition recursiveEntry .initial).get
      (by rfl)).2

def recursiveRootedActive : recursiveRecognition.RootedActiveOutcomeAt
    recursiveVisit :=
  recursiveRecognition.generatedRootedActiveAtVisit recursiveVisit () rfl
    recursiveSourceAuthority

theorem recursively_generated_effect_next_factorizes_through_root :
    let evolution := recursiveWorld.canonicalCausalAnswerAndNext
      (ULift.up recursiveVisit)
    evolution.generated =
        recursiveWorld.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
          recursiveVisit ∧
      HEq (evolution.generated.projectionOutcome
          recursiveRecognition.rootEffectProjection)
        recursiveRootedActive.installedFiber ∧
      evolution.nextCurrent =
        recursiveWorld.generatedNextCurrentAt recursiveVisit :=
  recursiveRootedActive.installedAuthority_factorizes

def recursiveCausalSuccessor : recursiveRootedActive.CausalSuccessorAt := by
  change recursiveRootedActive.CausalClosureAt
  exact recursiveRootedActive.generatedCausalClosure

def recursiveTargetAuthority : recursiveRecognition.CausalEntryAuthorityAt
      recursiveCausalSuccessor.successor.targetVisit
      recursiveCausalSuccessor.successor.targetEntry :=
  recursiveCausalSuccessor.targetAuthority

#print axioms SourceNativeEffectDynamicalRecognitionAt.RootedActiveOutcomeAt.active_eq_of_same_visit
#print axioms SourceNativeEffectDynamicalRecognitionAt.RootedActiveOutcomeAt.installedFiber_eq_of_same_visit
#print axioms SourceNativeEffectDynamicalRecognitionAt.RootedActiveOutcomeAt.payload_heq_of_same_visit
#print axioms SourceNativeEffectDynamicalRecognitionAt.RootedActiveOutcomeAt.installedAuthority_factorizes
#print axioms SourceNativeProjectionLaw.active_eq_of_classify_eq
#print axioms SourceNativeProjectionLaw.project_heq_of_classify_eq
#print axioms fixed_visit_effect_disposition_is_unique
#print axioms recursively_generated_effect_next_factorizes_through_root

end RecursiveNext

end RootEffectDynamicalClosureRegression
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
