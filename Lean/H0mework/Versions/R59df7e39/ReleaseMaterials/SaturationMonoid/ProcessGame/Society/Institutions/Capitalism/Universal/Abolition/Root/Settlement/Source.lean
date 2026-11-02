import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Admission.Actual
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Settlement.NonFinancial

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Settlement

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count : Nat) (datum : Admission.Datum input (Admission.frame input depth count))

abbrev oldFrame := Admission.frame input depth count
abbrev N := Continuation.N input (oldFrame input depth count)
abbrev Data := RawCurrent Party Good Technology Instrument

def sourceRoot := (Admission.generated input depth count datum).target.targetRoot
def sourceVisit := (Admission.generated input depth count datum).target.targetVisit
def sourceEntry := (Admission.generated input depth count datum).target.targetEntry
def sourceAuthority := (Admission.generated input depth count datum).target.targetAuthority

def initial : Data (Party := Party) (Good := Good) (Technology := Technology) (Instrument := Instrument) :=
  (Admission.generated input depth count datum).target.firstSuccessor.targetCurrent

def supportAt (current : Data (Party := Party) (Good := Good) (Technology := Technology) (Instrument := Instrument)) :
    (N input depth count).Support := (Continuation.oldSupport input (oldFrame input depth count), current)

variable (word : RawEvent Party Good Port Technology Instrument)

def next (current : Data (Party := Party) (Good := Good) (Technology := Technology) (Instrument := Instrument)) :=
  input.law.next current word

abbrev V : ConstructiveRoot.Vocabulary where
  Current := Data (Party := Party) (Good := Good) (Technology := Technology) (Instrument := Instrument)
  Anchor := (oldFrame input depth count).native.N.Anchor
  Incidence := (oldFrame input depth count).native.N.Incidence
  Lineage := (oldFrame input depth count).native.N.Lineage
  anchorAt := fun _ => (oldFrame input depth count).native.N.anchorAt (Continuation.oldSupport input (oldFrame input depth count))
  incidenceAt := fun _ => (oldFrame input depth count).native.N.incidenceAt (Continuation.oldSupport input (oldFrame input depth count))
  lineageAt := fun _ => (oldFrame input depth count).native.N.lineageAt (Continuation.oldSupport input (oldFrame input depth count))
  NativeWriteAt := fun _ => Unit
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := fun {current} _ => next input word current
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

inductive EventAt : (V input depth count word).Current → (N input depth count).Support → Type
  | emitted (current) : EventAt current (supportAt input depth count current)

def sourceLaw : SourceNativeEventAlgebra (N input depth count) (V input depth count word) where
  EventAt := EventAt input depth count word
  compile := fun _ => .nativeWrite ()
  AffectedInventoryAt := fun {_} {support} _ => OpenResponsibilityAt (N input depth count) support
  affectedInventoryPresentation := fun _ => ConstructivePresentation.refl _
  anchorKey := id
  incidenceKey := id
  lineageKey := id
  anchor_commutes := by intro current support event; cases event; rfl
  incidence_commutes := by intro current support event; cases event; rfl
  lineage_commutes := by intro current support event; cases event; rfl

def source : SourceNativeSource (N input depth count) (V input depth count word) where
  initial := initial input depth count datum
  law := sourceLaw input depth count word

def emitted (current : (V input depth count word).Current) :
    (source input depth count datum word).toRootSource.actual.OccurrenceAt current :=
  ⟨supportAt input depth count current, .emitted current⟩

theorem occurrence_eq_emitted {current : (V input depth count word).Current}
    (occurrence : (source input depth count datum word).toRootSource.actual.OccurrenceAt current) :
    occurrence = emitted input depth count datum word current := by
  rcases occurrence with ⟨support, event⟩
  cases event
  rfl

theorem initial_is_the_actual_admission_target :
    initial input depth count datum = (sourceVisit input depth count datum).current := rfl

theorem whole_period_is_the_original_next (current : (V input depth count word).Current) :
    (V input depth count word).nativeTarget (current := current) () = input.law.next current word := rfl

theorem source_checked_word_preserves_old_financial_claims (safe : NonFinancial word) :
    (next input word (initial input depth count datum)).claims = (initial input depth count datum).claims :=
  safe.next_claims input.law (initial input depth count datum) word

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Settlement
