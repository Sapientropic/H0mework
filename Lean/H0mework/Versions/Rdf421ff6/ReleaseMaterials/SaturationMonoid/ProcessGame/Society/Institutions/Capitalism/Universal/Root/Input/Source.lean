import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.ProgrammeSource
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.FreshPayment
import H0mework.Versions.R2.Arithmetic.PrimeShadow.LivingLawRootInquiryInputSourceKernel

/-!
# Full programme input on the original fresh Payment source

The epoch is assembled before its preserved emitter.  The source reader
supplies raw law, initial state and the entire instruction word; neither an
execution result nor a chosen revision enters the input.  The private germ
binds this full value to the exact original occurrence.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.InputSource

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open M9ProofCarryingRenewalInquiryRoot

variable (Party Good Port Technology Instrument : Type)

abbrev RawInput := ProgrammeSource.Input Party Good Port Technology Instrument

inductive Submission
  | legacy
  | programme (raw : RawInput Party Good Port Technology Instrument)

abbrev ledgerSource := jointRoot.source.base.restructuringSource.toLedgerSource
abbrev Occurrence {current : V.Current} :=
  ledgerSource.source.toRootSource.actual.OccurrenceAt current

structure Datum where
  reader : {current : V.Current} → Occurrence (current := current) →
    Submission Party Good Port Technology Instrument

variable {Party Good Port Technology Instrument}
  (datum : Datum Party Good Port Technology Instrument)

structure GermAt {current : V.Current} (occurrence : Occurrence (current := current)) : Type where
  private mk ::
  raw : Submission Party Good Port Technology Instrument
  private raw_eq : raw = datum.reader occurrence

def germAt {current : V.Current} (occurrence : Occurrence (current := current)) :
    GermAt datum occurrence := ⟨datum.reader occurrence, rfl⟩

theorem germ_unique {current : V.Current} (occurrence : Occurrence (current := current))
    (germ : GermAt datum occurrence) : germ = germAt datum occurrence := by
  rcases germ with ⟨raw, same⟩
  cases same
  rfl

theorem full_raw_source_exact {current : V.Current}
    (occurrence : Occurrence (current := current)) (germ : GermAt datum occurrence) :
    germ.raw = datum.reader occurrence := germ.raw_eq

inductive Projection
  | input
  | compilation

/-- The compilation token is indexed by the whole sealed germ.  Equal
instruction counts or equal results cannot substitute another input. -/
def component : SourceNativeProjectionLaw ledgerSource where
  Projection := Projection
  ActiveAt := fun _ {_current} _ => PUnit
  InactiveAt := fun _ {_current} _ => PEmpty
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun projection {_current} occurrence _ => match projection with
    | .input => GermAt datum occurrence
    | .compilation => SourceNativeInquiryCompilationTokenAt
        RootInquiryU8CompletionRegression.entry (germAt datum occurrence)
        (ULift.up.{1, 0} occurrence) RootInquiryU8CompletionRegression.inquiryAudit PUnit
  project := fun projection {_current} occurrence _ => match projection with
    | .input => germAt datum occurrence
    | .compilation => .canonical PUnit.unit

def root := jointRoot.withProjectionCoface (component datum)

def installation : SourceNativeProjectionLaw.InstallationAt (component datum)
    (root datum).source.base.projectionLaw :=
  .componentCoface jointRoot.source.base (component datum)

def inherited : SourceNativeProjectionLaw.InstallationAt jointRoot.source.base.projectionLaw
    (root datum).source.base.projectionLaw :=
  .inheritedCoface jointRoot.source.base (component datum)

theorem original_ledger_preserved :
    (root datum).toAuthoritativeRoot.toLedgerRoot = jointRoot.toAuthoritativeRoot.toLedgerRoot := rfl

theorem original_emitter_preserved : (root datum).emitted = jointRoot.emitted := rfl

def registeredInput (visit : SourceNativeTemporalVisitAt jointRoot.toAuthoritativeRoot.toLedgerRoot) :
    SourceNativeRootInquiryInputAt (root datum) visit
      (GermAt datum ((root datum).emitted visit.current)) where
  projection := (installation datum).embed .input
  active := PUnit.unit
  classifier_eq := rfl
  queryType_eq := rfl

theorem registered_query_is_source_germ
    (visit : SourceNativeTemporalVisitAt jointRoot.toAuthoritativeRoot.toLedgerRoot) :
    (registeredInput datum visit).query = germAt datum (jointRoot.emitted visit.current) := rfl

theorem registered_input_retains_entire_raw
    (visit : SourceNativeTemporalVisitAt jointRoot.toAuthoritativeRoot.toLedgerRoot) :
    (registeredInput datum visit).query.raw = datum.reader (jointRoot.emitted visit.current) := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.InputSource
