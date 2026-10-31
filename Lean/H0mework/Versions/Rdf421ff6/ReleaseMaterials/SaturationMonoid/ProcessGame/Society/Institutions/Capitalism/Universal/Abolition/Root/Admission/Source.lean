import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Continuation.Target
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Review.Code
import H0mework.Versions.R2.Arithmetic.PrimeShadow.LivingLawRootInquiryInputSourceKernel

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Admission

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (frame : Financial.Installation.Runtime.Frame input)

abbrev ledgerSource := frame.native.root.source.base.restructuringSource.toLedgerSource
abbrev Occurrence {current : frame.native.V.Current} :=
  (ledgerSource input frame).source.toRootSource.actual.OccurrenceAt current

structure Datum where
  reader : {current : frame.native.V.Current} → Occurrence input frame (current := current) →
    FeeCode (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)

variable (datum : Datum input frame)

def physicalAt (current : frame.native.V.Current) : RawCurrent Party Good Technology Instrument :=
  ProgrammeSource.rawCurrent input
    (Financial.Installation.Cursor.physicalVisit input (frame.native.cursor current)).current

structure GermAt {current : frame.native.V.Current} (occurrence : Occurrence input frame (current := current)) where
  private mk ::
  raw : FeeCode (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)
  private raw_eq : raw = datum.reader occurrence

def germAt {current : frame.native.V.Current} (occurrence : Occurrence input frame (current := current)) :
    GermAt input frame datum occurrence := ⟨datum.reader occurrence, rfl⟩

theorem germ_unique {current : frame.native.V.Current} (occurrence : Occurrence input frame (current := current))
    (germ : GermAt input frame datum occurrence) : germ = germAt input frame datum occurrence := by
  rcases germ with ⟨raw, same⟩
  cases same
  rfl

def ResultAt {current : frame.native.V.Current} (occurrence : Occurrence input frame (current := current)) :=
  Review.PaymentAt input.law (datum.reader occurrence).request (physicalAt input frame current) ⊕
    Review.Blockage input.law (datum.reader occurrence).request (datum.reader occurrence).scope
      (physicalAt input frame current)

def attemptAt {current : frame.native.V.Current} (occurrence : Occurrence input frame (current := current)) :
    ResultAt input frame datum occurrence :=
  Review.attempt input.law (datum.reader occurrence).request (datum.reader occurrence).scope
    (physicalAt input frame current)

inductive Projection
  | input | attempt | compilation | consumer

def component : SourceNativeProjectionLaw (ledgerSource input frame) where
  Projection := Projection
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun projection {current} occurrence _ => match projection with
    | .input => GermAt input frame datum occurrence
    | .attempt => ResultAt input frame datum occurrence
    | .compilation => SourceNativeInquiryCompilationTokenAt
        (Financial.Installation.Runtime.entry input frame.native current)
        (germAt input frame datum occurrence) (ULift.up.{1, 0} occurrence)
        (.answered : SourceNativeInquiryFrontAuditAt frame.installed.U7 frame.installed.calculus
          frame.native.root.source.base.lawSurface _) (ResultAt input frame datum occurrence)
    | .consumer => SourceNativeInquiryAnswerConsumerTokenAt
        (germAt input frame datum occurrence) (ULift.up.{1, 0} occurrence)
        (Financial.Installation.Runtime.entry input frame.native current) (attemptAt input frame datum occurrence)
  project := fun projection {_current} occurrence _ => match projection with
    | .input => germAt input frame datum occurrence
    | .attempt => attemptAt input frame datum occurrence
    | .compilation => .canonical (attemptAt input frame datum occurrence)
    | .consumer => .canonical

def root := frame.native.root.withProjectionCoface (component input frame datum)

def installation : SourceNativeProjectionLaw.InstallationAt (component input frame datum)
    (root input frame datum).source.base.projectionLaw :=
  .componentCoface frame.native.root.source.base (component input frame datum)

def visit : SourceNativeTemporalVisitAt (root input frame datum).toAuthoritativeRoot.toLedgerRoot :=
  frame.temporal input

def authority : SourceNativeLivingTemporalCausalEntryAuthorityAt (root input frame datum)
    (visit input frame datum) (Continuation.sourceEntry input frame) :=
  frame.authority.withProjectionCoface (component input frame datum)

abbrev Query := GermAt input frame datum (frame.native.root.emitted frame.visit.current)

def registeredInput : SourceNativeRootInquiryInputAt (root input frame datum) (visit input frame datum)
    (Query input frame datum) where
  projection := (installation input frame datum).embed .input
  active := ()
  classifier_eq := rfl
  queryType_eq := rfl

theorem original_ledger_and_emitter_preserved :
    (root input frame datum).toAuthoritativeRoot.toLedgerRoot = frame.native.root.toAuthoritativeRoot.toLedgerRoot ∧
      (root input frame datum).emitted = frame.native.root.emitted := ⟨rfl, rfl⟩

theorem registered_request_is_original_source :
    (registeredInput input frame datum).query.raw = datum.reader (frame.native.root.emitted frame.visit.current) := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Admission
