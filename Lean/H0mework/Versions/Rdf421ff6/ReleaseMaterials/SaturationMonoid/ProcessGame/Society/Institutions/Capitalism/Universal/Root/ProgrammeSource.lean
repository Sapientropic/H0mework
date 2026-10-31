import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.ProgrammeWorld
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.RawProgram
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Compiler

/-!
# A registered material programme in the original root grammar

The first write creates the registered source slots.  A generated word is
selected by this source's local emission rule from its actual current;
the old slots retain their claims while the complete instruction trace is
read under the original interpreter row.  Financial liabilities still
enter through the original native admission operation.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.ProgrammeSource

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Source.Program
open ProgrammeWorld

variable {Party Good Port Technology Instrument : Type}

inductive ProgrammeReport (Party Good Port Technology Instrument : Type) where
  | original (current : RawCurrent Party Good Technology Instrument)
      (word : RawEvent Party Good Port Technology Instrument)
  | planning [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
      (law : RawLaw Party Good Port Technology Instrument)
      (current : RawCurrent Party Good Technology Instrument)
      (task : PublicFunction.PublicTaskSpec Party Good)
      (alphabet : List (Request Party Good Port Technology Instrument)) (budget : Nat)
      (outcome : PublicFunction.PlanningOutcome law current task alphabet budget)

def ProgrammeReport.word (report : ProgrammeReport Party Good Port Technology Instrument) :
    RawEvent Party Good Port Technology Instrument := by
  cases report with
  | original _ word => exact word
  | @planning decParty decGood decInstrument _ _ _ _ _ outcome =>
      letI := decParty
      letI := decGood
      letI := decInstrument
      exact outcome.word

structure ObservedEmission (Data Event Payload : Type) extends ObservationLaw Data Payload where
  word : Payload → Event

structure Input (Party Good Port Technology Instrument : Type) where
  law : RawLaw Party Good Port Technology Instrument
  initial : RawCurrent Party Good Technology Instrument
  instructions : RawEvent Party Good Port Technology Instrument
  emission? : Option (RawCurrent Party Good Technology Instrument →
    RawEvent Party Good Port Technology Instrument) := none
  localAttempts : RawCurrent Party Good Technology Instrument →
    List (Request Party Good Port Technology Instrument) := fun _ => []
  /-- For a dynamic source, one generated payload supplies both the word and
  transfer evidence. Static instruction sources ignore this optional code. -/
  observedEmission? : Option (ObservedEmission (RawCurrent Party Good Technology Instrument)
    (RawEvent Party Good Port Technology Instrument)
    (ProgrammeReport Party Good Port Technology Instrument)) := none

variable [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

abbrev Data := RawCurrent Party Good Technology Instrument

inductive Current (Data : Type)
  | bootstrap
  | running (current : Data) (past : List Data)

variable (input : Input Party Good Port Technology Instrument)

def registrationSize : Nat :=
  match input.emission? with
  | none => input.instructions.length
  | some _ => 1

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument] in
theorem registrationSize_fixed (fixed : input.emission? = none) :
    registrationSize input = input.instructions.length := by
  simp only [registrationSize, fixed]

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument] in
theorem registrationSize_generated
    (emit : RawCurrent Party Good Technology Instrument → RawEvent Party Good Port Technology Instrument)
    (generated : input.emission? = some emit) : registrationSize input = 1 := by
  simp only [registrationSize, generated]

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument] in
theorem generated_registration_positive
    (emit : RawCurrent Party Good Technology Instrument → RawEvent Party Good Port Technology Instrument)
    (generated : input.emission? = some emit) : 0 < registrationSize input := by
  rw [registrationSize_generated input emit generated]
  exact Nat.zero_lt_one

def wordAt (current : RawCurrent Party Good Technology Instrument) :
    RawEvent Party Good Port Technology Instrument :=
  match input.emission? with
  | none => input.instructions
  | some emit => match input.observedEmission? with
    | none => emit current
    | some emission => emission.word (emission.generate current)

def observation? : Option (ObservationLaw (Data (Party := Party) (Good := Good)
    (Technology := Technology) (Instrument := Instrument))
    (ProgrammeReport Party Good Port Technology Instrument)) :=
  match input.emission? with
  | none => none
  | some _ => input.observedEmission?.map ObservedEmission.toObservationLaw

abbrev N := ProgrammeWorld.network (Data (Party := Party) (Good := Good)
  (Technology := Technology) (Instrument := Instrument)) (registrationSize input)
    (ProgrammeReport Party Good Port Technology Instrument) (observation? input)

def supportAt : Current (Data (Party := Party) (Good := Good)
    (Technology := Technology) (Instrument := Instrument)) → (N input).Support
  | .bootstrap => .bootstrap
  | .running current past => .running current past

def rawCurrent : Current (Data (Party := Party) (Good := Good)
    (Technology := Technology) (Instrument := Instrument)) →
    RawCurrent Party Good Technology Instrument
  | .bootstrap => input.initial
  | .running current _ => current

def rawEvent : Current (Data (Party := Party) (Good := Good)
    (Technology := Technology) (Instrument := Instrument)) →
    RawEvent Party Good Port Technology Instrument
  | .bootstrap => []
  | .running current _ => wordAt input current

def next : Current (Data (Party := Party) (Good := Good)
    (Technology := Technology) (Instrument := Instrument)) →
    Current (RawCurrent Party Good Technology Instrument)
  | .bootstrap => .running (input.law.next input.initial []) [input.initial]
  | .running current past =>
      .running (input.law.next current (wordAt input current)) (past ++ [current])

def pastAt : Current (RawCurrent Party Good Technology Instrument) →
    List (RawCurrent Party Good Technology Instrument)
  | .bootstrap => []
  | .running _ past => past

theorem past_next (current : Current (RawCurrent Party Good Technology Instrument)) :
    pastAt (next input current) = pastAt current ++ [rawCurrent input current] := by
  cases current <;> rfl

abbrev vocabulary : ConstructiveRoot.Vocabulary where
  Current := Current (Data (Party := Party) (Good := Good)
    (Technology := Technology) (Instrument := Instrument))
  Anchor := (N input).Anchor
  Incidence := (N input).Incidence
  Lineage := (N input).Lineage
  anchorAt := fun current => (N input).anchorAt (supportAt input current)
  incidenceAt := fun current => (N input).incidenceAt (supportAt input current)
  lineageAt := fun current => (N input).lineageAt (supportAt input current)
  NativeWriteAt := fun _ => Unit
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := fun {current} _ => next input current
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

abbrev V := vocabulary input

inductive NativeEventAt : (V input).Current → (N input).Support → Type
  | emitted (current) : NativeEventAt current (supportAt input current)

def sourceLaw : SourceNativeEventAlgebra (N input) (V input) where
  EventAt := NativeEventAt input
  compile := fun _ => .nativeWrite ()
  AffectedInventoryAt := fun {_} {support} _ => OpenResponsibilityAt (N input) support
  affectedInventoryPresentation := fun _ => ConstructivePresentation.refl _
  anchorKey := id
  incidenceKey := id
  lineageKey := id
  anchor_commutes := by intro current support event; cases event; rfl
  incidence_commutes := by intro current support event; cases event; rfl
  lineage_commutes := by intro current support event; cases event; rfl

def source : SourceNativeSource (N input) (V input) where
  initial := .bootstrap
  law := sourceLaw input

def emitted (current : (V input).Current) :
    (source input).toRootSource.actual.OccurrenceAt current :=
  ⟨supportAt input current, .emitted current⟩

theorem occurrence_eq_emitted {current : (V input).Current}
    (occurrence : (source input).toRootSource.actual.OccurrenceAt current) :
    occurrence = emitted input current := by
  rcases occurrence with ⟨support, event⟩
  cases event
  rfl

theorem actual_raw_next (current : (V input).Current) :
    rawCurrent input (next input current) =
      input.law.next (rawCurrent input current) (rawEvent input current) := by
  cases current <;> rfl

def targetEntry (current : (V input).Current)
    (row : Row (registrationSize input)) :
    OpenResponsibilityAt (N input) (supportAt input (next input current)) := by
  cases current <;> exact ⟨row, ()⟩

def sourceEntry (current : (V input).Current)
    (row : Row (registrationSize input)) :
    OpenResponsibilityAt (N input) (supportAt input current) := by
  cases current with
  | bootstrap =>
      cases row with
      | inherited => exact ⟨.inherited, ()⟩
      | obstruction => exact ⟨.obstruction, ()⟩
      | instruction _ => exact ⟨.inherited, ()⟩
  | running _ _ => exact ⟨row, ()⟩

def rowAt : Fin ((registrationSize input) + 2) → Row (registrationSize input) :=
  Fin.cases .inherited (Fin.cases .obstruction .instruction)

def rowIndex : Row (registrationSize input) → Fin ((registrationSize input) + 2)
  | .inherited => 0
  | .obstruction => (0 : Fin ((registrationSize input) + 1)).succ
  | .instruction index => index.succ.succ

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument] in
theorem rowAt_index (row : Row (registrationSize input)) :
    rowAt input (rowIndex input row) = row := by
  cases row <;> rfl

def transition (current : (V input).Current) (row : Row (registrationSize input)) :
    LedgerEntryEvolutionAt (N input) (sourceEntry input current row)
      (targetEntry input current row) := by
  have receipt := transferReceipt (observation? input) (supportAt input current)
  cases current <;> cases row <;>
    exact .transferred receipt rfl rfl
      (by first | exact Nat.le_refl _ | exact Nat.le_succ 1)

def ExactTransitionAt :
    {current : (V input).Current} →
    (occurrence : (source input).toRootSource.actual.OccurrenceAt current) →
    {targetSupport : (N input).Support} →
    OpenResponsibilityAt (N input) occurrence.1 →
    OpenResponsibilityAt (N input) targetSupport → Type :=
  fun {_} _ {_} before after => LedgerEntryEvolutionAt (N input) before after

def rowSource : LedgerWriteRowSourceAt (source input) (ExactTransitionAt input) where
  IncidenceOccurrenceAt := fun {_} _ {_} before after =>
    LedgerEntryEvolutionAt (N input) before after
  compileEvolution := id
  compileExact := id

def terminalRowSource : LedgerTerminalRowSourceAt (source input) where
  IncidenceOccurrenceAt := fun _ _ => PEmpty
  compile := fun impossible => impossible.elim

def rows {current : (V input).Current}
    (occurrence : (source input).toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWriteRowsAt (rowSource input) occurrence
      ⟨supportAt input (next input current)⟩ := by
  cases occurrence_eq_emitted input occurrence
  exact {
    size := (registrationSize input) + 2
    sourceEntryAt := fun index => sourceEntry input current (rowAt input index)
    targetEntryAt := fun index => targetEntry input current (rowAt input index)
    rowAt := fun index => (rowSource input).generate
      (transition input current (rowAt input index)) }

def coverage {current : (V input).Current}
    (occurrence : (source input).toRootSource.actual.OccurrenceAt current) :
    LedgerCompleteFiniteCoverageAt (rows input occurrence) := by
  cases occurrence_eq_emitted input occurrence
  exact {
    destinationIndex := fun entry => rowIndex input entry.1
    originIndex := fun entry => rowIndex input entry.1
    destination_sound := by
      rintro ⟨row, opened⟩
      change Row (registrationSize input) at row
      change sourceEntry input current (rowAt input (rowIndex input row)) = _
      rw [rowAt_index]
      cases current with
      | bootstrap =>
          cases row with
          | inherited => cases opened; rfl
          | obstruction => cases opened; rfl
          | instruction _ => exact opened.elim
      | running _ _ => cases opened; rfl
    origin_sound := by
      rintro ⟨row, opened⟩
      change Row (registrationSize input) at row
      change targetEntry input current (rowAt input (rowIndex input row)) = _
      rw [rowAt_index]
      cases current <;> cases opened <;> rfl }

def patch {current : (V input).Current}
    (occurrence : (source input).toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWritePatchAt (rowSource input) occurrence
      ⟨supportAt input (next input current)⟩ :=
  .complete (rows input occurrence) (coverage input occurrence)

def ledgerCompiler : SourceNativeLedgerCompiler (source input) where
  IncidenceTransitionAt := fun _ _ _ => Unit
  ExactTransitionAt := ExactTransitionAt input
  exact_incidence := fun _ => ()
  exact_lineage := fun _ => rfl
  writeRowSource := rowSource input
  terminalRowSource := terminalRowSource input
  compile := fun {current} occurrence =>
    .nativeWrite () rfl (emitted input (next input current))
      (patch input occurrence).toLedgerWriteEvolution
  compilePatch := fun occurrence => ⟨patch input occurrence, rfl⟩

def ledgerSource : SourceNativeLedgerSource (N input) (V input) where
  source := source input
  ledgerCompiler := ledgerCompiler input

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.ProgrammeSource
