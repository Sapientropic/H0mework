import H0mework.Foundation.Ledger.Restructuring

/-!
# Source-native ledger compiler focused regression

The structural root exposes no ledger receipt.
`SourceNativeLedgerRootClosure` is the only root ledger authority: its whole-ledger
evolution is definitionally the fold of one finite, occurrence-generated
incidence patch.  Only rows present in that patch carry exact-entry authority;
the identity remainder remains a compatibility readout.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace SourceNativeLedgerCompilerRegression

open ConstructiveRoot

/-- Type-valued certificate for the incidence leg of one exact pair. -/
structure IncidenceStep (source target : Bool) : Type where
  equality : source = target

/-- Exact source/target pair certificate used by the canonical compiler.  It
separately preserves the world support/lineage and the responsibility identity
for this regression. -/
structure ExactPairTransition
    (sourceSupport targetSupport source target : Bool) : Type where
  support_eq : sourceSupport = targetSupport
  responsibility_eq : source = target

def network : WorldRelationNetwork where
  Support := Bool
  Anchor := Unit
  Incidence := Bool
  Lineage := Bool
  Responsibility := Bool
  Claim := Unit
  anchorAt := fun _ => ()
  incidenceAt := id
  lineageAt := id
  OpenAt := fun support _ => if support then PEmpty else Unit
  openClaimAt := fun _ => ()
  HoldsAt := fun _ _ => Unit
  ObstructionAt := fun _ => Unit
  obstructionClaim := fun _ => ()
  SemanticChangeAt := fun _ _ _ => Unit
  DispositionAt := fun _ _ => Unit

abbrev N := network

def vocabulary : ConstructiveRoot.Vocabulary where
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
  nativeTarget := fun _ => ()
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim
  cofinal :=
    { Event := Bool
      emit? := some false
      pathAt := fun _ _ => ()
      target := fun _ => () }

abbrev V := vocabulary

/-- The only primitive event is indexed by source support `false`. -/
inductive NativeEventAt : Unit → Bool → Type
  | emitted : NativeEventAt () false

def inventoryPresentation :
    ConstructivePresentation Bool (OpenResponsibilityAt N false) where
  forward := fun responsibility => ⟨responsibility, ()⟩
  backward := Sigma.fst
  backward_forward := fun _ => rfl
  forward_backward := by
    rintro ⟨responsibility, receipt⟩
    cases responsibility <;> cases receipt <;> rfl

def sourceLaw : SourceNativeEventAlgebra N V where
  EventAt := NativeEventAt
  compile := fun _ => .nativeWrite ()
  AffectedInventoryAt := fun _ => Bool
  affectedInventoryPresentation := by
    intro current support event
    cases event
    exact inventoryPresentation
  anchorKey := fun _ => ()
  incidenceKey := fun _ => false
  lineageKey := fun _ => false
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

def source : SourceNativeSource N V where
  initial := ()
  law := sourceLaw

def emitted : (current : V.Current) →
    source.toRootSource.actual.OccurrenceAt current :=
  fun _ => ⟨false, .emitted⟩

abbrev ledger : CompleteLiveLedgerAt N := ⟨false⟩

def falseEntry : ledger.Entry := ⟨false, ()⟩

def trueEntry : ledger.Entry := ⟨true, ()⟩

def writeRowSource : LedgerWriteRowSourceAt source (by
    intro current occurrence targetSupport sourceEntry targetEntry
    exact ExactPairTransition occurrence.1 targetSupport
      sourceEntry.1 targetEntry.1) where
  IncidenceOccurrenceAt := fun _ _ _ _ => PEmpty
  compileEvolution := fun {_} {_} {_} {_} {_} event => nomatch event
  compileExact := fun {_} {_} {_} {_} {_} event => nomatch event

def emptyTerminalRowSource : LedgerTerminalRowSourceAt source where
  IncidenceOccurrenceAt := fun _ _ => PEmpty
  compile := fun event => nomatch event

def ledgerCompiler : SourceNativeLedgerCompiler source where
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
  writeRowSource := writeRowSource
  terminalRowSource := emptyTerminalRowSource
  compile := by
    intro current occurrence
    rcases occurrence with ⟨support, event⟩
    cases event
    exact .nativeWrite () rfl ⟨false, .emitted⟩
      (LedgerWriteEvolutionAt.identity ledger)
  compilePatch := by
    intro current occurrence
    rcases occurrence with ⟨support, event⟩
    cases event
    exact ⟨FiniteGeneratedLedgerWritePatchAt.identity writeRowSource
      ⟨false, .emitted⟩, rfl⟩

def ledgerSource : SourceNativeLedgerSource N V where
  source := source
  ledgerCompiler := ledgerCompiler

def root : SourceNativeLedgerRootClosure N V where
  source := ledgerSource
  emitted := emitted
  compiler_commutes := by
    intro current
    cases current
    rfl

/-! ## Identity-only restructuring authority -/

def restructuringLaw : SourceNativeLedgerRestructuringLaw source :=
  identityOnlyWorldLedgerRestructuringLaw source () <| by
    intro support responsibility
    cases support
    · change Subsingleton Unit
      infer_instance
    · change Subsingleton PEmpty
      infer_instance

def restructuringCertification
    (occurrence : source.toRootSource.actual.OccurrenceAt ()) :
    SourceNativeLedgerRestructuringCertificationAt restructuringLaw
      (ledgerCompiler.compile occurrence) := by
  rcases occurrence with ⟨support, event⟩
  cases event
  exact ExactLedgerRestructuringCertificationAt.ofInjective
    (fun _ _ equality => equality)
    (fun _ _ equality => equality)

def restructuringCompiler : SourceNativeRestructuringLedgerCompiler source where
  ledgerCompiler := ledgerCompiler
  restructuringLaw := restructuringLaw
  certifyRestructuring := restructuringCertification

def restructuringSource : SourceNativeRestructuringLedgerSource N V where
  source := source
  compiler := restructuringCompiler

/-- The exact pair certificate cannot certify an unregistered `false → true`
responsibility rewrite. -/
theorem exact_transition_cannot_rewrite_responsibility
    (transition : ledgerCompiler.ExactTransitionAt
      (emitted ()) falseEntry trueEntry) :
    False :=
  Bool.noConfusion transition.responsibility_eq

/-! ## Cross-support lineage laundering control -/

def lineageNetwork : WorldRelationNetwork where
  Support := Bool
  Anchor := Unit
  Incidence := Unit
  Lineage := Bool
  Responsibility := Unit
  Claim := Unit
  anchorAt := fun _ => ()
  incidenceAt := fun _ => ()
  lineageAt := id
  OpenAt := fun _ _ => Unit
  openClaimAt := fun _ => ()
  HoldsAt := fun _ _ => Unit
  ObstructionAt := fun _ => Unit
  obstructionClaim := fun _ => ()
  SemanticChangeAt := fun _ _ _ => Unit
  DispositionAt := fun _ _ => Unit

abbrev LineageN := lineageNetwork

def lineageVocabulary : ConstructiveRoot.Vocabulary where
  Current := Bool
  Anchor := Unit
  Incidence := Unit
  Lineage := Bool
  anchorAt := fun _ => ()
  incidenceAt := fun _ => ()
  lineageAt := id
  NativeWriteAt := fun _ => Unit
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := fun _ => true
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

abbrev LineageV := lineageVocabulary

inductive LineageEventAt : Bool → Bool → Type
  | atFalse : LineageEventAt false false
  | atTrue : LineageEventAt true true

def lineageInventoryPresentation (support : Bool) :
    ConstructivePresentation Unit (OpenResponsibilityAt LineageN support) where
  forward := fun _ => ⟨(), ()⟩
  backward := fun _ => ()
  backward_forward := fun _ => rfl
  forward_backward := by
    rintro ⟨responsibility, receipt⟩
    cases responsibility
    cases receipt
    rfl

def lineageSourceLaw : SourceNativeEventAlgebra LineageN LineageV where
  EventAt := LineageEventAt
  compile := fun _ => .nativeWrite ()
  AffectedInventoryAt := fun _ => Unit
  affectedInventoryPresentation := by
    intro current support event
    exact lineageInventoryPresentation support
  anchorKey := fun _ => ()
  incidenceKey := fun _ => ()
  lineageKey := id
  anchor_commutes := by
    intro current support event
    cases event <;> rfl
  incidence_commutes := by
    intro current support event
    cases event <;> rfl
  lineage_commutes := by
    intro current support event
    cases event <;> rfl

def lineageSource : SourceNativeSource LineageN LineageV where
  initial := false
  law := lineageSourceLaw

def lineageEmitted : (current : LineageV.Current) →
    lineageSource.toRootSource.actual.OccurrenceAt current
  | false => ⟨false, .atFalse⟩
  | true => ⟨true, .atTrue⟩

abbrev falseLineageLedger : CompleteLiveLedgerAt LineageN := ⟨false⟩
abbrev trueLineageLedger : CompleteLiveLedgerAt LineageN := ⟨true⟩

def falseLineageEntry : falseLineageLedger.Entry := ⟨(), ()⟩
def trueLineageEntry : trueLineageLedger.Entry := ⟨(), ()⟩

theorem weak_receipt_rewrites_world_lineage :
    LineageN.lineageAt false ≠ LineageN.lineageAt true :=
  Bool.noConfusion

/-- Any source-native ledger compiler rejects the same attack: an exact pair
would have to prove equality of the source and target world lineages. -/
theorem source_native_compiler_rejects_cross_lineage_transfer
    (compiler : SourceNativeLedgerCompiler lineageSource)
    (exact : compiler.ExactTransitionAt
      (lineageEmitted false) falseLineageEntry trueLineageEntry) :
    False :=
  Bool.noConfusion (compiler.exact_lineage exact)

/-! ## Terminal branch control -/

/-- The raw source event family contains a terminal-shaped occurrence and an
actual write-bearing sibling at one current.  A ledger compiler may classify
either occurrence, but the resulting raw root is not terminal authority until
its complete concrete inventory has been admitted. -/
def mixedTerminalVocabulary : ConstructiveRoot.Vocabulary where
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
  FaithfulTerminalAt := fun _ => Unit
  nativeTarget := fun _ => ()
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

abbrev MixedTerminalV := mixedTerminalVocabulary

inductive MixedTerminalEventAt : Unit → Bool → Type
  | terminal : MixedTerminalEventAt () true
  | write : MixedTerminalEventAt () true

def mixedTerminalInventoryPresentation :
    ConstructivePresentation PEmpty (OpenResponsibilityAt N true) where
  forward := PEmpty.elim
  backward := fun entry => nomatch entry.2
  backward_forward := fun value => nomatch value
  forward_backward := by
    rintro ⟨responsibility, openReceipt⟩
    nomatch openReceipt

def mixedTerminalSourceLaw : SourceNativeEventAlgebra N MixedTerminalV where
  EventAt := MixedTerminalEventAt
  compile := fun event => match event with
    | .terminal => .faithfulTerminal ()
    | .write => .nativeWrite ()
  AffectedInventoryAt := fun _ => PEmpty
  affectedInventoryPresentation := by
    intro current support event
    cases event <;> exact mixedTerminalInventoryPresentation
  anchorKey := fun _ => ()
  incidenceKey := fun _ => true
  lineageKey := fun _ => true
  anchor_commutes := by intro current support event; cases event <;> rfl
  incidence_commutes := by intro current support event; cases event <;> rfl
  lineage_commutes := by intro current support event; cases event <;> rfl

def mixedTerminalSource : SourceNativeSource N MixedTerminalV where
  initial := ()
  law := mixedTerminalSourceLaw

def mixedTerminalOccurrence :
    mixedTerminalSource.toRootSource.actual.OccurrenceAt () :=
  ⟨true, .terminal⟩

def mixedWriteOccurrence :
    mixedTerminalSource.toRootSource.actual.OccurrenceAt () :=
  ⟨true, .write⟩

def terminalVocabulary : ConstructiveRoot.Vocabulary where
  Current := Unit
  Anchor := Unit
  Incidence := Unit
  Lineage := Unit
  anchorAt := fun _ => ()
  incidenceAt := fun _ => ()
  lineageAt := fun _ => ()
  NativeWriteAt := fun _ => PEmpty
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => Unit
  nativeTarget := PEmpty.elim
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

abbrev TerminalV := terminalVocabulary

inductive TerminalEventAt : Unit → Bool → Type
  | emitted : TerminalEventAt () false

def terminalSourceLaw : SourceNativeEventAlgebra N TerminalV where
  EventAt := TerminalEventAt
  compile := fun _ => .faithfulTerminal ()
  AffectedInventoryAt := fun _ => Bool
  affectedInventoryPresentation := by
    intro current support event
    cases event
    exact inventoryPresentation
  anchorKey := fun _ => ()
  incidenceKey := fun _ => false
  lineageKey := fun _ => false
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

def terminalSource : SourceNativeSource N TerminalV where
  initial := ()
  law := terminalSourceLaw

def terminalEmitted : (current : TerminalV.Current) →
    terminalSource.toRootSource.actual.OccurrenceAt current :=
  fun _ => ⟨false, .emitted⟩

def terminalLedgerEvolution : LedgerTerminalEvolutionAt N ledger where
  discharge := fun _ => ⟨()⟩

def terminalWriteRowSource : LedgerWriteRowSourceAt terminalSource (by
    intro current occurrence targetSupport sourceEntry targetEntry
    exact ExactPairTransition occurrence.1 targetSupport
      sourceEntry.1 targetEntry.1) where
  IncidenceOccurrenceAt := fun _ _ _ _ => PEmpty
  compileEvolution := fun {_} {_} {_} {_} {_} event => nomatch event
  compileExact := fun {_} {_} {_} {_} {_} event => nomatch event

def terminalRowSource : LedgerTerminalRowSourceAt terminalSource where
  IncidenceOccurrenceAt := fun _ _ => Unit
  compile := fun _ => ⟨()⟩

def terminalEntryAt : Fin 2 → ledger.Entry
  | ⟨0, _⟩ => falseEntry
  | ⟨1, _⟩ => trueEntry

def terminalEntryIndex : ledger.Entry → Fin 2
  | ⟨false, _⟩ => ⟨0, by decide⟩
  | ⟨true, _⟩ => ⟨1, by decide⟩

theorem terminalEntryAt_index (entry : ledger.Entry) :
    terminalEntryAt (terminalEntryIndex entry) = entry := by
  rcases entry with ⟨responsibility, openReceipt⟩
  cases responsibility <;> cases openReceipt <;> rfl

def terminalFinitePatch : FiniteGeneratedLedgerTerminalPatchAt
    terminalRowSource (terminalEmitted ()) where
  size := 2
  entryAt := terminalEntryAt
  rowAt := fun _ => terminalRowSource.generate ()
  entryIndex := terminalEntryIndex
  entry_sound := terminalEntryAt_index

theorem terminalFinitePatch_readout :
    terminalFinitePatch.toLedgerTerminalEvolution = terminalLedgerEvolution := by
  apply congrArg (fun discharge => ({ discharge := discharge } :
    LedgerTerminalEvolutionAt N ledger))
  funext entry
  rcases entry with ⟨responsibility, openReceipt⟩
  cases responsibility <;> cases openReceipt <;> rfl

def terminalLedgerCompiler : SourceNativeLedgerCompiler terminalSource where
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
  writeRowSource := terminalWriteRowSource
  terminalRowSource := terminalRowSource
  compile := by
    intro current occurrence
    rcases occurrence with ⟨support, event⟩
    cases event
    exact .faithfulTerminal () rfl terminalLedgerEvolution
  compilePatch := by
    intro current occurrence
    rcases occurrence with ⟨support, event⟩
    cases event
    exact ⟨.finite terminalFinitePatch, terminalFinitePatch_readout⟩

def terminalLedgerSource : SourceNativeLedgerSource N TerminalV where
  source := terminalSource
  ledgerCompiler := terminalLedgerCompiler

def terminalRoot : SourceNativeLedgerRootClosure N TerminalV where
  source := terminalLedgerSource
  emitted := terminalEmitted
  compiler_commutes := fun _ => True.intro

/-! ## Raw emitted-terminal readout before inventory admission -/

def mixedTerminalEmitted : (current : MixedTerminalV.Current) →
    mixedTerminalSource.toRootSource.actual.OccurrenceAt current :=
  fun _ => mixedTerminalOccurrence

def mixedTerminalWriteRowSource : LedgerWriteRowSourceAt mixedTerminalSource (by
    intro current occurrence targetSupport sourceEntry targetEntry
    exact ExactPairTransition occurrence.1 targetSupport
      sourceEntry.1 targetEntry.1) where
  IncidenceOccurrenceAt := fun _ _ _ _ => PEmpty
  compileEvolution := fun {_} {_} {_} {_} {_} event => nomatch event
  compileExact := fun {_} {_} {_} {_} {_} event => nomatch event

def mixedTerminalRowSource : LedgerTerminalRowSourceAt mixedTerminalSource where
  IncidenceOccurrenceAt := fun _ _ => PEmpty
  compile := fun event => nomatch event

abbrev mixedTerminalLedger : CompleteLiveLedgerAt N := ⟨true⟩

def mixedTerminalFinitePatch : FiniteGeneratedLedgerTerminalPatchAt
    mixedTerminalRowSource mixedTerminalOccurrence where
  size := 0
  entryAt := fun index => index.elim0
  rowAt := fun index => index.elim0
  entryIndex := fun entry => nomatch entry.2
  entry_sound := fun entry => nomatch entry.2

def mixedTerminalLedgerEvolution :
    LedgerTerminalEvolutionAt N mixedTerminalLedger :=
  mixedTerminalFinitePatch.toLedgerTerminalEvolution

def mixedTerminalLedgerCompiler :
    SourceNativeLedgerCompiler mixedTerminalSource where
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
  writeRowSource := mixedTerminalWriteRowSource
  terminalRowSource := mixedTerminalRowSource
  compile := by
    intro current occurrence
    rcases occurrence with ⟨support, event⟩
    cases event with
    | terminal =>
        exact .faithfulTerminal () rfl mixedTerminalLedgerEvolution
    | write =>
        exact .nativeWrite () rfl mixedTerminalOccurrence
          (LedgerWriteEvolutionAt.identity mixedTerminalLedger)
  compilePatch := by
    intro current occurrence
    rcases occurrence with ⟨support, event⟩
    cases event with
    | terminal =>
        exact ⟨.finite mixedTerminalFinitePatch, rfl⟩
    | write =>
        exact ⟨FiniteGeneratedLedgerWritePatchAt.identity
          mixedTerminalWriteRowSource ⟨true, .write⟩, rfl⟩

def mixedTerminalLedgerSource : SourceNativeLedgerSource N MixedTerminalV where
  source := mixedTerminalSource
  ledgerCompiler := mixedTerminalLedgerCompiler

def mixedTerminalRoot : SourceNativeLedgerRootClosure N MixedTerminalV where
  source := mixedTerminalLedgerSource
  emitted := mixedTerminalEmitted
  compiler_commutes := fun _ => True.intro

/-- The raw ledger root reads the selected terminal compiler branch.  This is
intentionally only a compiler regression: the continuing sibling prevents this
source from acquiring admitted terminal authority. -/
theorem mixedTerminalRoot_generatedLedgerAt :
    mixedTerminalRoot.generatedLedgerAt () =
      .faithfulTerminal () rfl mixedTerminalLedgerEvolution :=
  rfl

def terminalRestructuringLaw :
    SourceNativeLedgerRestructuringLaw terminalSource :=
  identityOnlyWorldLedgerRestructuringLaw terminalSource () <| by
    intro support responsibility
    cases support
    · change Subsingleton Unit
      infer_instance
    · change Subsingleton PEmpty
      infer_instance

def terminalRestructuringCertification
    (occurrence : terminalSource.toRootSource.actual.OccurrenceAt ()) :
    SourceNativeLedgerRestructuringCertificationAt terminalRestructuringLaw
      (terminalLedgerCompiler.compile occurrence) := by
  rcases occurrence with ⟨support, event⟩
  cases event
  exact PUnit.unit

def terminalRestructuringCompiler :
    SourceNativeRestructuringLedgerCompiler terminalSource where
  ledgerCompiler := terminalLedgerCompiler
  restructuringLaw := terminalRestructuringLaw
  certifyRestructuring := terminalRestructuringCertification

def terminalRestructuringSource :
    SourceNativeRestructuringLedgerSource N TerminalV where
  source := terminalSource
  compiler := terminalRestructuringCompiler

/-- Terminal authority is the compiler-generated complete discharge, not a
separately supplied raw-world receipt. -/
theorem terminal_generatedLedgerAt_eq :
    terminalRoot.generatedLedgerAt () =
      .faithfulTerminal () rfl terminalLedgerEvolution :=
  rfl

/-- Both live Boolean entries are paid by that exact compiler image. -/
theorem source_native_terminal_disposes_every_entry :
    (terminalLedgerEvolution.discharge falseEntry).receipt = () ∧
    (terminalLedgerEvolution.discharge trueEntry).receipt = () :=
  ⟨rfl, rfl⟩

/-! ## No completed-oracle authority -/

abbrev oracleNetwork : WorldRelationNetwork where
  Support := Unit
  Anchor := Unit
  Incidence := Unit
  Lineage := Unit
  Responsibility := Nat
  Claim := Unit
  anchorAt := fun _ => ()
  incidenceAt := fun _ => ()
  lineageAt := fun _ => ()
  OpenAt := fun _ _ => Unit
  openClaimAt := fun _ => ()
  HoldsAt := fun _ _ => Unit
  ObstructionAt := fun _ => Unit
  obstructionClaim := fun _ => ()
  SemanticChangeAt := fun _ _ _ => Unit
  DispositionAt := fun _ kind =>
    match kind with
    | .transfer => Bool
    | _ => Unit

abbrev OracleN := oracleNetwork

def oracleVocabulary : ConstructiveRoot.Vocabulary where
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
  nativeTarget := fun _ => ()
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

abbrev OracleV := oracleVocabulary

def oracleInventoryPresentation :
    ConstructivePresentation Nat (OpenResponsibilityAt OracleN ()) where
  forward := fun responsibility => ⟨responsibility, ()⟩
  backward := Sigma.fst
  backward_forward := fun _ => rfl
  forward_backward := by
    rintro ⟨responsibility, receipt⟩
    cases receipt
    rfl

def oracleSourceLaw : SourceNativeEventAlgebra OracleN OracleV where
  EventAt := fun _ _ => Unit
  compile := fun _ => .nativeWrite ()
  AffectedInventoryAt := fun _ => Nat
  affectedInventoryPresentation := fun _ => oracleInventoryPresentation
  anchorKey := fun _ => ()
  incidenceKey := fun _ => ()
  lineageKey := fun _ => ()
  anchor_commutes := fun _ => rfl
  incidence_commutes := fun _ => rfl
  lineage_commutes := fun _ => rfl

def oracleSource : SourceNativeSource OracleN OracleV where
  initial := ()
  law := oracleSourceLaw

def oracleOccurrence :
    oracleSource.toRootSource.actual.OccurrenceAt () :=
  ⟨(), ()⟩

abbrev oracleLedger : CompleteLiveLedgerAt OracleN := ⟨()⟩

def oracleEntry (index : Nat) : oracleLedger.Entry := ⟨index, ()⟩

def oracleWriteRowSource : LedgerWriteRowSourceAt oracleSource
    (fun _ _ _ _ => Unit) where
  IncidenceOccurrenceAt := fun _ _ _ _ => Bool
  compileEvolution := fun event =>
    .transferred event rfl rfl (Nat.le_refl _)
  compileExact := fun _ => ()

def oracleTerminalRowSource : LedgerTerminalRowSourceAt oracleSource :=
  LedgerTerminalRowSourceAt.empty oracleSource

/-- The old total compatibility type can describe a completed infinite answer
table.  This value is intentionally retained as a hostile readout. -/
def completedOracleEvolution (oracle : Nat → Bool) :
    LedgerWriteEvolutionAt OracleN oracleLedger oracleLedger where
  destination := fun entry =>
    ⟨entry, .transferred (oracle entry.1) rfl rfl (Nat.le_refl _)⟩
  origin := fun entry =>
    ⟨entry, .transferred (oracle entry.1) rfl rfl (Nat.le_refl _)⟩

def oracleTransferBit
    {source target : oracleLedger.Entry} :
    LedgerEntryEvolutionAt OracleN source target → Option Bool
  | .carried _ _ => none
  | .maintained .. => none
  | .transferred receipt _ _ _ => some receipt

def oneRowIndex (entry : oracleLedger.Entry) : Option (Fin 1) :=
  if entry.1 = 0 then some ⟨0, by decide⟩ else none

theorem oneRowIndex_sound
    (entry : oracleLedger.Entry) (index : Fin 1)
    (index_eq : oneRowIndex entry = some index) : oracleEntry 0 = entry := by
  rcases entry with ⟨responsibility, openReceipt⟩
  cases openReceipt
  have responsibility_eq : responsibility = 0 := by
    simpa [oneRowIndex] using congrArg Option.isSome index_eq
  cases responsibility_eq
  rfl

def oneRowDependentIndex (entry : oracleLedger.Entry) :
    Option { _index : Fin 1 // oracleEntry 0 = entry } :=
  match index_eq : oneRowIndex entry with
  | none => none
  | some index => some ⟨index, oneRowIndex_sound entry index index_eq⟩

/-- Positive finite patch: one exact incidence event transfers entry `0`; all
other natural-numbered incidences are definitionally carried. -/
def oneRowPatch : FiniteGeneratedLedgerWritePatchAt oracleWriteRowSource
    oracleOccurrence oracleLedger :=
  .identityRemainder
    { size := 1
      sourceEntryAt := fun _ => oracleEntry 0
      targetEntryAt := fun _ => oracleEntry 0
      rowAt := fun _ => oracleWriteRowSource.generate true }
    { destinationIndex := oneRowDependentIndex
      originIndex := oneRowDependentIndex }

/-- Exact-entry authority is produced by the same selector that folds the
finite patch.  The caller cannot choose a sibling stored row. -/
def oneRowPatch_entryAuthority :
    oneRowPatch.CanonicalGeneratedSourceRowAt (oracleEntry 0) :=
  (oneRowPatch.canonicalGeneratedSourceRow? (oracleEntry 0)).get (by rfl)

/-- The empty identity patch still folds to an identity table, but it grants
no standing/renewal authority to any entry. -/
theorem empty_identity_patch_has_no_entry_authority
    (entry : oracleLedger.Entry) :
    IsEmpty
      ((FiniteGeneratedLedgerWritePatchAt.identity oracleWriteRowSource
        oracleOccurrence).CanonicalGeneratedSourceRowAt entry) := by
  constructor
  intro authority
  simpa using authority.selected

/-- Two generated rows may be retained as diagnostic inventory while the
identity-remainder fold selects neither.  They must not acquire authority. -/
def omittedDuplicatePatch : FiniteGeneratedLedgerWritePatchAt
    oracleWriteRowSource oracleOccurrence oracleLedger :=
  .identityRemainder
    { size := 2
      sourceEntryAt := fun _ => oracleEntry 0
      targetEntryAt := fun _ => oracleEntry 0
      rowAt := fun _ => oracleWriteRowSource.generate true }
    { destinationIndex := fun _ => none
      originIndex := fun _ => none }

/-- The omitted rows remain inspectable as stored inventory. -/
def omittedDuplicatePatch_firstStored :
    omittedDuplicatePatch.GeneratedSourceEntryAt (oracleEntry 0) :=
  ⟨⟨0, by decide⟩, rfl⟩

def omittedDuplicatePatch_secondStored :
    omittedDuplicatePatch.GeneratedSourceEntryAt (oracleEntry 0) :=
  ⟨⟨1, by decide⟩, rfl⟩

/-- Stored rows omitted by the world fold cannot mint causal authority. -/
theorem omitted_duplicate_rows_have_no_canonical_authority :
    IsEmpty
      (omittedDuplicatePatch.CanonicalGeneratedSourceRowAt (oracleEntry 0)) := by
  constructor
  intro authority
  simpa using authority.selected

/-- The omitted transfer receipts do not alter the folded world destination. -/
theorem omitted_duplicate_rows_fold_to_identity :
    oracleTransferBit
        (omittedDuplicatePatch.toLedgerWriteEvolution.destination
          (oracleEntry 0)).2 = none :=
  rfl

/-- The selected row's target and evolution are the exact target/evolution of
the folded world destination. -/
theorem selected_row_commutes_with_world_fold :
    oneRowPatch_entryAuthority.targetEntry =
        (oneRowPatch.toLedgerWriteEvolution.destination (oracleEntry 0)).1 ∧
      HEq oneRowPatch_entryAuthority.row.evolution
        (oneRowPatch.toLedgerWriteEvolution.destination (oracleEntry 0)).2 :=
  ⟨oneRowPatch_entryAuthority.target_eq_fold,
    oneRowPatch_entryAuthority.evolution_heq_fold⟩

def oneRowGenerated : SourceNativeLedgerEvolutionAt
    oracleSource oracleOccurrence :=
  .nativeWrite () rfl oracleOccurrence oneRowPatch.toLedgerWriteEvolution

def oneRowSourceNativePatch : SourceNativeFiniteLedgerPatchAt oracleSource
    (fun _ _ _ _ => Unit) oracleWriteRowSource oracleTerminalRowSource
    oneRowGenerated :=
  ⟨oneRowPatch, rfl⟩

/-- The whole-ledger destination records a genuine transfer of entry `0`. -/
theorem one_row_has_terminal_or_transferred_effect :
    SourceNativeLedgerTerminalOrTransferredAt oneRowGenerated
      (oracleEntry 0) :=
  rfl

/-- The semantic transfer effect itself forces the canonical row selected by
the same finite patch; no row or index is submitted to this producer. -/
def oneRowSourceNativeAuthorityFromEffect :
    SourceNativeFiniteLedgerPatchGeneratedEntryAt oracleSource
      (fun _ _ _ _ => Unit) oracleWriteRowSource oracleTerminalRowSource
      oneRowGenerated oneRowSourceNativePatch (oracleEntry 0) :=
  sourceNativeFiniteLedgerPatchGeneratedEntry_of_terminalOrTransferred
    oneRowSourceNativePatch (oracleEntry 0)
      one_row_has_terminal_or_transferred_effect

def oneRowSourceNativeAuthority :
    SourceNativeFiniteLedgerPatchGeneratedEntryAt oracleSource
      (fun _ _ _ _ => Unit) oracleWriteRowSource oracleTerminalRowSource
      oneRowGenerated oneRowSourceNativePatch (oracleEntry 0) :=
  (sourceNativeFiniteLedgerPatchGeneratedEntry? oracleSource
    (fun _ _ _ _ => Unit) oracleWriteRowSource oracleTerminalRowSource
    oneRowGenerated oneRowSourceNativePatch (oracleEntry 0)).get (by rfl)

/-- Source-native authority and the whole world ledger now share the same row
by construction, not by a consumer-provided alignment premise. -/
theorem source_native_selected_row_commutes_with_world :
    oneRowSourceNativeAuthority.CommutesWithWorld :=
  oneRowSourceNativeAuthority.commutes_with_world

def omittedRowsGenerated : SourceNativeLedgerEvolutionAt
    oracleSource oracleOccurrence :=
  .nativeWrite () rfl oracleOccurrence
    omittedDuplicatePatch.toLedgerWriteEvolution

/-- Omitted inventory rows do not create the semantic transfer effect needed
to force authority. -/
theorem omitted_rows_have_no_terminal_or_transferred_effect :
    IsEmpty (SourceNativeLedgerTerminalOrTransferredAt omittedRowsGenerated
      (oracleEntry 0)) := by
  constructor
  intro effect
  change false = true at effect
  contradiction

/-- The finite patch changes the emitted incidence and carries an unmentioned
incidence. -/
theorem finite_patch_changes_only_emitted_incidence :
    oracleTransferBit
        (oneRowPatch.toLedgerWriteEvolution.destination (oracleEntry 0)).2 =
        some true ∧
      oracleTransferBit
        (oneRowPatch.toLedgerWriteEvolution.destination (oracleEntry 1)).2 =
        none :=
  ⟨rfl, rfl⟩

def freshAbove : (size : Nat) → (Fin size → Nat) → Nat
  | 0, _ => 0
  | size + 1, valueAt =>
      freshAbove size (fun index => valueAt index.castSucc) +
        valueAt (Fin.last size) + 1

theorem value_lt_freshAbove
    {size : Nat} (valueAt : Fin size → Nat) (index : Fin size) :
    valueAt index < freshAbove size valueAt := by
  induction size with
  | zero => exact Fin.elim0 index
  | succ size inductionHypothesis =>
      have index_le : index.val ≤ size :=
        Nat.le_of_lt_succ index.isLt
      rcases Nat.lt_or_eq_of_le index_le with index_lt | index_eq
      · let earlier : Fin size := ⟨index.val, index_lt⟩
        have cast_eq : earlier.castSucc = index := Fin.ext rfl
        rw [← cast_eq]
        exact Nat.lt_succ_of_le <| Nat.le_trans
          (Nat.le_of_lt (inductionHypothesis
            (fun prior => valueAt prior.castSucc) earlier))
          (Nat.le_add_right _ _)
      · have last_eq : index = Fin.last size := Fin.ext index_eq
        rw [last_eq]
        exact Nat.lt_succ_of_le (Nat.le_add_left _ _)

def freshResponsibility
    {target : CompleteLiveLedgerAt OracleN}
    (rows : FiniteGeneratedLedgerWriteRowsAt oracleWriteRowSource
      oracleOccurrence target) : Nat :=
  freshAbove rows.size (fun index => (rows.sourceEntryAt index).1)

theorem row_lt_freshResponsibility
    {target : CompleteLiveLedgerAt OracleN}
    (rows : FiniteGeneratedLedgerWriteRowsAt oracleWriteRowSource
      oracleOccurrence target)
    (index : Fin rows.size) :
    (rows.sourceEntryAt index).1 < freshResponsibility rows := by
  exact value_lt_freshAbove
    (fun rowIndex => (rows.sourceEntryAt rowIndex).1) index

theorem freshEntry_ne_row
    {target : CompleteLiveLedgerAt OracleN}
    (rows : FiniteGeneratedLedgerWriteRowsAt oracleWriteRowSource
      oracleOccurrence target)
    (index : Fin rows.size) :
    rows.sourceEntryAt index ≠ oracleEntry (freshResponsibility rows) := by
  intro entry_eq
  have responsibility_eq := congrArg Sigma.fst entry_eq
  have row_lt := row_lt_freshResponsibility rows index
  exact (Nat.ne_of_lt row_lt) responsibility_eq

/-- No finite generated patch can equal the completed all-`true` transfer
oracle.  The proof constructs an exact unmentioned natural-number incidence;
identity remainder carries it, while complete finite coverage is impossible. -/
theorem finite_patch_ne_completed_true_oracle
    (patch : FiniteGeneratedLedgerWritePatchAt oracleWriteRowSource
      oracleOccurrence oracleLedger) :
    patch.toLedgerWriteEvolution ≠ completedOracleEvolution (fun _ => true) := by
  cases patch with
  | identityRemainder rows coverage =>
      let freshEntry := oracleEntry (freshResponsibility rows)
      have fresh_ne : (index : Fin rows.size) →
          rows.sourceEntryAt index ≠ freshEntry :=
        freshEntry_ne_row rows
      intro evolution_eq
      cases index_eq : coverage.destinationIndex freshEntry with
      | none =>
          have transfer_eq := congrArg
            (fun evolution =>
              FiniteGeneratedLedgerWritePatchAt.ledgerEntryIsTransferred
                (evolution.destination freshEntry).2)
            evolution_eq
          have left_eq :
              FiniteGeneratedLedgerWritePatchAt.ledgerEntryIsTransferred
                  ((FiniteGeneratedLedgerWritePatchAt.identityRemainder
                    rows coverage).toLedgerWriteEvolution.destination
                      freshEntry).2 = false := by
            rw [FiniteGeneratedLedgerWritePatchAt.toLedgerWriteEvolution_identityRemainder
              rows coverage]
            exact
              FiniteGeneratedLedgerWritePatchAt.identityRemainder_destination_isNotTransferred
                rows coverage freshEntry index_eq
          have right_eq :
              FiniteGeneratedLedgerWritePatchAt.ledgerEntryIsTransferred
                  ((completedOracleEvolution (fun _ => true)).destination
                    freshEntry).2 = true := rfl
          rw [left_eq, right_eq] at transfer_eq
          exact Bool.noConfusion transfer_eq
      | some indexed =>
          exact fresh_ne indexed.1 indexed.2
  | complete rows coverage =>
      exact fun _ =>
        freshEntry_ne_row rows (coverage.destinationIndex
          (oracleEntry (freshResponsibility rows)))
          (coverage.destination_sound (oracleEntry (freshResponsibility rows)))
  | transportedRemainder rows coverage remainder =>
      exact nomatch remainder.event

def completedOracleGenerated :
    SourceNativeLedgerEvolutionAt oracleSource oracleOccurrence :=
  .nativeWrite () rfl oracleOccurrence
    (completedOracleEvolution (fun _ => true))

/-- Hostile regression: the completed `Nat → Bool` table remains a legal
static readout, but there is no finite source-generated patch capable of
authorizing it. -/
theorem completed_oracle_has_no_source_native_patch :
    IsEmpty (SourceNativeFiniteLedgerPatchAt oracleSource
      (fun _ _ _ _ => Unit) oracleWriteRowSource oracleTerminalRowSource
      completedOracleGenerated) where
  false generated :=
    finite_patch_ne_completed_true_oracle generated.1 generated.2

end SourceNativeLedgerCompilerRegression
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
