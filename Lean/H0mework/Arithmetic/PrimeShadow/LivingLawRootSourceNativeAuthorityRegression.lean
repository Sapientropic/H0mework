import H0mework.Foundation.Authority.SourceProjectionInventory
import H0mework.Checks.Runtime.RootNativeLedgerCompilerRegression

/-!
# Source-first root projection/readout regression

The fixture keeps one complete source-native ledger law fixed and varies a
Boolean domain projection.  Both projections are legitimate source laws, but
the projection law is fixed before the root emitter is installed.  Therefore
they are different complete sources and cannot reuse one another's generated
readout.

This does not say that an already existing ledger source may acquire a new
projection shell while silently inheriting the old authority.  Such an
inheritance requires an explicit source/law-epoch change outside this kernel.

Arbitrary fine projections remain static source-law readouts.  No post-root
query wrapper or repeated total-inventory record can mint a second authority
source.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace SourceNativeRootAuthorityRegression

open ConstructiveRoot
open SourceNativeLedgerCompilerRegression

abbrev LedgerRoot := SourceNativeLedgerCompilerRegression.root
abbrev RestructuringSource :=
  SourceNativeLedgerCompilerRegression.restructuringSource

/-- A tiny source-owned observer.  Both branch token types are inhabited so
the raw syntax admits forged alternatives; the classifier nevertheless fixes
the canonical branch to `active`. -/
def boolProjectionLaw (flag : Bool) :
    SourceNativeProjectionLaw RestructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Unit
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {_} _ _ => Bool
  project := fun _ {_} _ _ => flag

def boolSource (flag : Bool) : SourceNativeAuthoritySource N V where
  restructuringSource := RestructuringSource
  eventInventoryAdmission :=
    .reflOfNoFaithfulTerminal RestructuringSource
      (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := .rootSemantic N
  projectionLaw := boolProjectionLaw flag

def boolWorld (flag : Bool) :
    SourceNativeAuthoritativeRootClosure N V where
  source := boolSource flag
  emitted := LedgerRoot.emitted
  compiler_commutes := LedgerRoot.compiler_commutes

def initialVisit (flag : Bool) : RootVisit (boolWorld flag).toRoot :=
  (boolWorld flag).toRoot.initialVisit

def generatedBoolOutcome (flag : Bool) : Bool :=
  match (boolWorld flag).projectionOutcomeAt ()
      (initialVisit flag).current with
  | .inl ⟨_, payload⟩ => payload
  | .inr _ => false

/-- The lower event/ledger root is shared, but the Boolean readout is fixed in
the pre-emitter source law. -/
theorem projection_boolean_is_part_of_source_identity :
    (boolWorld false).toLedgerRoot = LedgerRoot ∧
      (boolWorld true).toLedgerRoot = LedgerRoot ∧
      generatedBoolOutcome false = false ∧
      generatedBoolOutcome true = true :=
  ⟨rfl, rfl, rfl, rfl⟩

def outcomeCode
    {world : SourceNativeAuthoritativeRootClosure N V}
    {projection : world.source.projectionLaw.Projection}
    {current : V.Current} :
    SourceNativeProjectionOutcomeAt world projection current -> Bool
  | .inl _ => true
  | .inr _ => false

theorem canonical_outcome_is_active_false :
    outcomeCode
        ((boolWorld false).projectionOutcomeAt ()
          (initialVisit false).current) = true ∧
      generatedBoolOutcome false = false :=
  ⟨rfl, rfl⟩

/-- The false source's readout cannot be retyped as the true source's readout
merely because both forget to the same lower ledger root. -/
theorem projection_source_cannot_be_erased_and_reused : True := by
  fail_if_success
    exact ((boolWorld false).projectionOutcomeAt ()
      (initialVisit false).current :
        SourceNativeProjectionOutcomeAt (boolWorld true)
          ()
          (initialVisit true).current)
  trivial

/-- A projection cannot accept a caller-selected sibling ledger evolution.
Its only ledger authority is the compiler already owned by the fixed source. -/
theorem projection_has_no_caller_ledger_mouth
    {current : V.Current}
    (occurrence : RestructuringSource.toLedgerSource.source.toRootSource.actual.OccurrenceAt
      current)
    (_active : (boolProjectionLaw false).ActiveAt () occurrence)
    (_callerLedger : SourceNativeLedgerEvolutionAt
      RestructuringSource.toLedgerSource.source occurrence) : True := by
  fail_if_success
    exact (boolProjectionLaw false).project
      () occurrence _active _callerLedger
  trivial

/-! ## Inactive receipts cannot carry a hidden choice -/

def inactiveBoolProjectionLaw :
    SourceNativeProjectionLaw RestructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => PEmpty
  InactiveAt := fun _ {_} _ => Bool
  classify := fun _ {_} _ => .inr false
  PayloadAt := fun _ {_} _ active => nomatch active
  project := fun _ {_} _ active => nomatch active

/-- Even when the inactive fibre has multiple inhabitants, the fixed source
classifier cannot certify a sibling receipt. -/
theorem inactive_classifier_cannot_select_true
    {current : V.Current}
    {occurrence : RestructuringSource.toLedgerSource.source.toRootSource.actual.OccurrenceAt
      current}
    (forged : inactiveBoolProjectionLaw.classify () occurrence = .inr true) :
    False := by
  have receipt_eq : false = true :=
    inactiveBoolProjectionLaw.inactive_eq_of_classify_eq rfl forged
  exact Bool.noConfusion receipt_eq

#print axioms SourceNativeProjectionLaw.inactive_eq_of_classify_eq
#print axioms inactive_classifier_cannot_select_true

/-! ## A complete inventory prevents post-selection laundering -/

/-- Two legitimate Boolean questions belong to one fixed source inventory. -/
def questionProjectionLaw :
    SourceNativeProjectionLaw RestructuringSource.toLedgerSource where
  Projection := Bool
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {_} _ _ => Bool
  project := fun question {_} _ _ => question

def questionSource : SourceNativeAuthoritySource N V where
  restructuringSource := RestructuringSource
  eventInventoryAdmission :=
    .reflOfNoFaithfulTerminal RestructuringSource
      (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := .rootSemantic N
  projectionLaw := questionProjectionLaw

def questionWorld : SourceNativeAuthoritativeRootClosure N V where
  source := questionSource
  emitted := LedgerRoot.emitted
  compiler_commutes := LedgerRoot.compiler_commutes

def questionVisit : RootVisit questionWorld.toRoot :=
  questionWorld.toRoot.initialVisit

/-! ## Completed fields remain readouts -/

/-- A complete function-valued field remains legal source data.  The generic
projection layer may read it, but cannot turn it into atom/action/U8
operational authority. -/
def completedOracleProjectionLaw (oracle : Nat -> Bool) :
    SourceNativeProjectionLaw RestructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {_} _ _ => Nat -> Bool
  project := fun _ {_} _ _ => oracle

def completedOracleSource (oracle : Nat -> Bool) :
    SourceNativeAuthoritySource N V where
  restructuringSource := RestructuringSource
  eventInventoryAdmission :=
    .reflOfNoFaithfulTerminal RestructuringSource
      (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := .rootSemantic N
  projectionLaw := completedOracleProjectionLaw oracle

def completedOracleWorld (oracle : Nat -> Bool) :
    SourceNativeAuthoritativeRootClosure N V where
  source := completedOracleSource oracle
  emitted := LedgerRoot.emitted
  compiler_commutes := LedgerRoot.compiler_commutes

def completedOracleVisit (oracle : Nat -> Bool) :
    RootVisit (completedOracleWorld oracle).toRoot :=
  (completedOracleWorld oracle).toRoot.initialVisit

def completedOracleReadout (oracle : Nat -> Bool) :
    SourceNativeProjectionOutcomeAt (completedOracleWorld oracle)
      ()
      (completedOracleVisit oracle).current :=
  (completedOracleWorld oracle).projectionOutcomeAt ()
    (completedOracleVisit oracle).current

/-- Function-valued payloads are not banned: the complete oracle remains a
faithful field/readout of the fixed source law. -/
theorem completed_oracle_remains_a_readout
    (oracle : Nat -> Bool) (query : Nat) :
    (match completedOracleReadout oracle with
    | .inl ⟨_, payload⟩ => payload query
    | .inr impossible => nomatch impossible) = oracle query :=
  rfl

def questionPayload (question : Bool) : Bool :=
  match questionWorld.projectionOutcomeAt question questionVisit.current with
  | .inl ⟨_, payload⟩ => payload
  | .inr impossible => nomatch impossible

/-- Both answers are read from one source-fixed law; neither is an
independently selectable operational-authority object. -/
theorem both_questions_are_source_law_readouts :
    questionPayload false = false ∧ questionPayload true = true :=
  ⟨rfl, rfl⟩

/-! ## A truncated terminal vocabulary cannot represent a continuing source -/

/-- The concrete mixed source contains an actual write-bearing sibling at the
same current.  Its token is generated by the concrete ledger compiler, not by
the terminal wrapper vocabulary. -/
def mixedWriteIsActualOutgoing :
    SourceNativeActualOutgoingEventAt mixedTerminalLedgerSource () :=
  ⟨mixedWriteOccurrence, PUnit.unit⟩

/-- The deliberately thinner terminal occurrence fibre is a singleton. -/
theorem terminalOccurrence_subsingleton :
    Subsingleton
      (terminalSource.toRootSource.actual.OccurrenceAt ()) := by
  constructor
  rintro ⟨leftSupport, leftEvent⟩ ⟨rightSupport, rightEvent⟩
  cases leftEvent
  cases rightEvent
  rfl

def mixedOccurrenceCode :
    mixedTerminalSource.toRootSource.actual.OccurrenceAt () -> Bool
  | ⟨_, .terminal⟩ => false
  | ⟨_, .write⟩ => true

/-- Hostile regression for source pruning.  The concrete source has two exact
occurrences (terminal and write); the thin terminal source has one.  Hence no
two-sided occurrence presentation—and therefore no complete heterogeneous
event-inventory admission—can identify the thin source with the concrete one. -/
theorem mixed_inventory_cannot_be_pruned_to_terminal :
    IsEmpty
      (ConstructivePresentation
        (mixedTerminalSource.toRootSource.actual.OccurrenceAt ())
        (terminalSource.toRootSource.actual.OccurrenceAt ())) := by
  constructor
  intro presentation
  have image_eq :
      presentation.forward mixedTerminalOccurrence =
        presentation.forward mixedWriteOccurrence :=
    terminalOccurrence_subsingleton.elim _ _
  have source_eq : mixedTerminalOccurrence = mixedWriteOccurrence := by
    calc
      mixedTerminalOccurrence =
          presentation.backward
            (presentation.forward mixedTerminalOccurrence) :=
        (presentation.backward_forward mixedTerminalOccurrence).symm
      _ = presentation.backward
            (presentation.forward mixedWriteOccurrence) :=
        congrArg presentation.backward image_eq
      _ = mixedWriteOccurrence :=
        presentation.backward_forward mixedWriteOccurrence
  have code_eq := congrArg mixedOccurrenceCode source_eq
  exact Bool.noConfusion code_eq

/-- The concrete sibling continuation directly contradicts any claim that its
complete actual inventory is empty. -/
theorem mixed_inventory_is_not_terminally_exhausted :
    ¬ IsEmpty (SourceNativeActualOutgoingEventAt mixedTerminalLedgerSource ()) :=
  fun empty => empty.false mixedWriteIsActualOutgoing

/-- The exact exhaustiveness field required by identity admission is itself
uninhabited for the mixed source: its terminal occurrence cannot erase the
write-bearing sibling. -/
theorem mixed_terminal_cannot_pay_identity_admission
    (exhausts :
      (occurrence : mixedTerminalSource.toRootSource.actual.OccurrenceAt ()) ->
      (terminal : MixedTerminalV.FaithfulTerminalAt ()) ->
      mixedTerminalSource.toRootSource.actual.compile occurrence =
          .faithfulTerminal terminal ->
      IsEmpty (SourceNativeActualOutgoingEventAt mixedTerminalLedgerSource ())) :
    False :=
  (exhausts mixedTerminalOccurrence () rfl).false mixedWriteIsActualOutgoing

/-! ## Heterogeneous admission preserves structural branch identity -/

/-- Even an arbitrary heterogeneous presentation of the complete concrete
inventory cannot relabel this source's native occurrence as a relation write.
The contradiction is paid by the admission's branch-commuting law, not by
definitional equality of the two vocabularies. -/
theorem complete_admission_cannot_relabel_native_as_relation
    (admission :
      SourceNativeCompleteEventInventoryAdmission RestructuringSource)
    (occurrence :
      RestructuringSource.source.toRootSource.actual.OccurrenceAt ())
    (actualIsRelation :
      (admission.actualSource.source.toRootSource.actual.compile
        (admission.actualOccurrenceAt occurrence)).kind =
          .relationWrite) : False := by
  have representedIsNative :
      (RestructuringSource.source.toRootSource.actual.compile occurrence).kind =
        .nativeWrite := by
    rcases occurrence with ⟨support, event⟩
    cases event
    rfl
  have nativeIsRelation :
      RootEvolutionKind.nativeWrite = RootEvolutionKind.relationWrite :=
    representedIsNative.symm |>.trans <|
      (admission.actual_kind_eq occurrence).trans actualIsRelation
  exact RootEvolutionKind.noConfusion nativeIsRelation

/-! ## Cofinal boundary inventory is part of the admitted source -/

/-- The represented source emits its canonical cofinal event.  A complete
admission cannot obtain that event by recharting a concrete source whose
cofinal emitter is empty. -/
theorem complete_admission_cannot_invent_cofinal_boundary
    (admission :
      SourceNativeCompleteEventInventoryAdmission RestructuringSource)
    (actualEmpty : admission.ActualV.cofinal.emit? = none) : False :=
  admission.no_cofinal_insertion actualEmpty (event := false) rfl

/-- Conversely, the terminal fixture has no cofinal event in its vocabulary.
It cannot be presented as the complete inventory of a concrete source that
did emit one.  Local terminality and cofinal landing may coexist in a richer
source; the forbidden move is erasing that landing while claiming a complete
rechart of the same source. -/
theorem complete_admission_cannot_erase_cofinal_boundary
    (admission :
      SourceNativeCompleteEventInventoryAdmission terminalRestructuringSource)
    {event : admission.ActualV.cofinal.Event}
    (actualEmitted : admission.ActualV.cofinal.emit? = some event) : False := by
  exact admission.no_cofinal_erasure actualEmitted rfl

end SourceNativeRootAuthorityRegression
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
