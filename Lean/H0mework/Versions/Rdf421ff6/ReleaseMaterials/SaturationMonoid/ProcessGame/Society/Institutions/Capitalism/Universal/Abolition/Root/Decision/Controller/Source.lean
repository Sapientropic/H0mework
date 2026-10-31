import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Decision.Batch.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Decision.Controller

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count : Nat) (datum : Admission.Datum input (Admission.frame input depth count)) (limit : Nat)

abbrev N := Settlement.N input depth count
abbrev Raw := RawCurrent Party Good Technology Instrument

structure Current where
  raw : Raw (Party := Party) (Good := Good) (Technology := Technology) (Instrument := Instrument)
  first : Bool
  original_fee_target : first = true → raw = Batch.atFee input depth count datum

def initial : Current input depth count datum := ⟨Batch.atFee input depth count datum, true, fun _ => rfl⟩

def laterCandidates (raw : Raw (Party := Party) (Good := Good) (Technology := Technology) (Instrument := Instrument)) :=
  PublicFunction.words (input.localAttempts raw ++ ProgrammeSource.wordAt input raw) limit

def ReportFor : Bool → Raw (Party := Party) (Good := Good) (Technology := Technology) (Instrument := Instrument) → Type
  | true, _ => Batch.Completed input depth count datum limit
  | false, raw => Review.Guarded.CompletedAt input (Batch.origin input depth count)
      (Batch.code input depth count datum).request (Batch.code input depth count datum).scope
      (Batch.cohort input depth count) raw (laterCandidates input limit raw)

def reportFor : (first : Bool) →
    (raw : Raw (Party := Party) (Good := Good) (Technology := Technology) (Instrument := Instrument)) →
    ReportFor input depth count datum limit first raw
  | true, _ => Batch.completed input depth count datum limit
  | false, raw => Review.Guarded.complete input (Batch.origin input depth count)
      (Batch.code input depth count datum).request (Batch.code input depth count datum).scope
      (Batch.cohort input depth count) raw (laterCandidates input limit raw)

def effect (current : Current input depth count datum) :
    Raw (Party := Party) (Good := Good) (Technology := Technology) (Instrument := Instrument) :=
  match current.first with
  | true => (Batch.completed input depth count datum limit).effect
  | false => (Review.Guarded.complete input (Batch.origin input depth count)
      (Batch.code input depth count datum).request (Batch.code input depth count datum).scope
      (Batch.cohort input depth count) current.raw (laterCandidates input limit current.raw)).effect

def next (current : Current input depth count datum) : Current input depth count datum where
  raw := effect input depth count datum limit current
  first := false
  original_fee_target := fun impossible => Bool.noConfusion impossible

def supportAt (current : Current input depth count datum) : (N input depth count).Support :=
  (Continuation.oldSupport input (Admission.frame input depth count), current.raw)

abbrev V : ConstructiveRoot.Vocabulary where
  Current := Current input depth count datum
  Anchor := (N input depth count).Anchor
  Incidence := (N input depth count).Incidence
  Lineage := (N input depth count).Lineage
  anchorAt := fun current => (N input depth count).anchorAt (supportAt input depth count datum current)
  incidenceAt := fun current => (N input depth count).incidenceAt (supportAt input depth count datum current)
  lineageAt := fun current => (N input depth count).lineageAt (supportAt input depth count datum current)
  NativeWriteAt := fun _ => Unit
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := fun {current} _ => next input depth count datum limit current
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

inductive EventAt : (V input depth count datum limit).Current → (N input depth count).Support → Type
  | emitted (current) : EventAt current (supportAt input depth count datum current)

def sourceLaw : SourceNativeEventAlgebra (N input depth count) (V input depth count datum limit) where
  EventAt := EventAt input depth count datum limit
  compile := fun _ => .nativeWrite ()
  AffectedInventoryAt := fun {_} {support} _ => OpenResponsibilityAt (N input depth count) support
  affectedInventoryPresentation := fun _ => ConstructivePresentation.refl _
  anchorKey := id
  incidenceKey := id
  lineageKey := id
  anchor_commutes := by intro current support event; cases event; rfl
  incidence_commutes := by intro current support event; cases event; rfl
  lineage_commutes := by intro current support event; cases event; rfl

def source : SourceNativeSource (N input depth count) (V input depth count datum limit) where
  initial := initial input depth count datum
  law := sourceLaw input depth count datum limit

def emitted (current : Current input depth count datum) :
    (source input depth count datum limit).toRootSource.actual.OccurrenceAt current :=
  ⟨supportAt input depth count datum current, .emitted current⟩

theorem occurrence_eq_emitted {current : Current input depth count datum}
    (occurrence : (source input depth count datum limit).toRootSource.actual.OccurrenceAt current) :
    occurrence = emitted input depth count datum limit current := by
  rcases occurrence with ⟨support, event⟩
  cases event
  rfl

theorem first_native_write_is_the_source_batch :
    (next input depth count datum limit (initial input depth count datum)).raw =
      Batch.effect input depth count datum limit := rfl

theorem every_successor_spends_the_first_fee_credit (current : Current input depth count datum) :
    (next input depth count datum limit current).first = false := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Decision.Controller
