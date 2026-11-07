import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Admission.Source
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Installation.PendingDrain.Account
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Mandatory.Source
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native.Origin

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth sourceStart : Nat)

abbrev cut := (Epoch.Finance.Installation.PendingDrain.drain input depth sourceStart).last
abbrev frame := Epoch.Finance.Installation.PendingDrain.frame input depth sourceStart
abbrev ledgerSource := (frame input depth sourceStart).native.root.source.base.restructuringSource.toLedgerSource
abbrev Occurrence {current : (frame input depth sourceStart).native.V.Current} :=
  (ledgerSource input depth sourceStart).source.toRootSource.actual.OccurrenceAt current

/-- A source reader supplies raw syntax before this coface is installed.
It cannot supply a checked command, target, account, or activation. -/
structure Datum where
  reader : {current : (frame input depth sourceStart).native.V.Current} →
    Occurrence input depth sourceStart (current := current) →
      Compile.RawInput Party Good Port Technology Instrument
  nativeOrigin : Option (ReviewSource.Native.OriginAt input) := none

variable (datum : Datum input depth sourceStart) (prefixLimit renewalLimit : Nat)
  (review : Option (ReviewPhase.ContextAt input) := none)

structure GermAt {current : (frame input depth sourceStart).native.V.Current}
    (occurrence : Occurrence input depth sourceStart (current := current)) where
  private mk ::
  raw : Compile.RawInput Party Good Port Technology Instrument
  migrationLimit : Nat
  continuationLimit : Nat
  nativeOrigin : Option (ReviewSource.Native.OriginAt input)
  private raw_eq : raw = datum.reader occurrence
  private migrationLimit_eq : migrationLimit = prefixLimit
  private continuationLimit_eq : continuationLimit = renewalLimit
  private nativeOrigin_eq : nativeOrigin = datum.nativeOrigin

def germAt {current : (frame input depth sourceStart).native.V.Current}
    (occurrence : Occurrence input depth sourceStart (current := current)) :
    GermAt input depth sourceStart datum prefixLimit renewalLimit occurrence :=
  ⟨datum.reader occurrence, prefixLimit, renewalLimit, datum.nativeOrigin, rfl, rfl, rfl, rfl⟩

theorem germ_unique {current : (frame input depth sourceStart).native.V.Current}
    (occurrence : Occurrence input depth sourceStart (current := current))
    (germ : GermAt input depth sourceStart datum prefixLimit renewalLimit occurrence) :
    germ = germAt input depth sourceStart datum prefixLimit renewalLimit occurrence := by
  rcases germ with ⟨raw, migrationLimit, continuationLimit, nativeOrigin, raw_eq, migrationLimit_eq, continuationLimit_eq, nativeOrigin_eq⟩
  cases raw_eq
  cases migrationLimit_eq
  cases continuationLimit_eq
  cases nativeOrigin_eq
  rfl

def ResultAt {current : (frame input depth sourceStart).native.V.Current}
    (occurrence : Occurrence input depth sourceStart (current := current)) :=
  Mandatory.Report (review := review) input depth (cut input depth sourceStart) prefixLimit renewalLimit Physical.initial (datum.reader occurrence) ×
    Compile.Result input depth (cut input depth sourceStart) prefixLimit renewalLimit
      (Actual.initial input depth (cut input depth sourceStart))
      (Mandatory.executionRaw (review := review) input depth (cut input depth sourceStart) prefixLimit renewalLimit Physical.initial (datum.reader occurrence))

def reportAt {current : (frame input depth sourceStart).native.V.Current}
    (occurrence : Occurrence input depth sourceStart (current := current)) :
    ResultAt (review := review) input depth sourceStart datum prefixLimit renewalLimit occurrence :=
  ⟨Mandatory.produce (review := review) input depth (cut input depth sourceStart) prefixLimit renewalLimit Physical.initial (datum.reader occurrence),
    Physical.resultAt input depth (cut input depth sourceStart) prefixLimit renewalLimit
      (Mandatory.executionCursor (review := review) input depth (cut input depth sourceStart) prefixLimit renewalLimit
        Physical.initial (datum.reader occurrence))⟩

inductive Projection
  | input | sourceSelection | compilation

def component : SourceNativeProjectionLaw (ledgerSource input depth sourceStart) where
  Projection := Projection
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun projection {current} occurrence _ => match projection with
    | .input => GermAt input depth sourceStart datum prefixLimit renewalLimit occurrence
    | .sourceSelection => ResultAt (review := review) input depth sourceStart datum prefixLimit renewalLimit occurrence
    | .compilation => SourceNativeInquiryCompilationTokenAt
        (Financial.Installation.Runtime.entry input (frame input depth sourceStart).native current)
        (germAt input depth sourceStart datum prefixLimit renewalLimit occurrence) (ULift.up.{1, 0} occurrence)
        (.answered : SourceNativeInquiryFrontAuditAt (frame input depth sourceStart).installed.U7
          (frame input depth sourceStart).installed.calculus
          (frame input depth sourceStart).native.root.source.base.lawSurface _)
        (ResultAt (review := review) input depth sourceStart datum prefixLimit renewalLimit occurrence)
  project := fun projection {_current} occurrence _ => match projection with
    | .input => germAt input depth sourceStart datum prefixLimit renewalLimit occurrence
    | .sourceSelection => reportAt (review := review) input depth sourceStart datum prefixLimit renewalLimit occurrence
    | .compilation => .canonical (reportAt (review := review) input depth sourceStart datum prefixLimit renewalLimit occurrence)

def root := (frame input depth sourceStart).native.root.withProjectionCoface
  (component (review := review) input depth sourceStart datum prefixLimit renewalLimit)

def installation : SourceNativeProjectionLaw.InstallationAt
    (component (review := review) input depth sourceStart datum prefixLimit renewalLimit)
    (root (review := review) input depth sourceStart datum prefixLimit renewalLimit).source.base.projectionLaw :=
  .componentCoface (frame input depth sourceStart).native.root.source.base
    (component (review := review) input depth sourceStart datum prefixLimit renewalLimit)

def visit : SourceNativeTemporalVisitAt
    (root (review := review) input depth sourceStart datum prefixLimit renewalLimit).toAuthoritativeRoot.toLedgerRoot :=
  (frame input depth sourceStart).temporal input

def authority : SourceNativeLivingTemporalCausalEntryAuthorityAt
    (root (review := review) input depth sourceStart datum prefixLimit renewalLimit)
    (visit (review := review) input depth sourceStart datum prefixLimit renewalLimit)
    (Continuation.sourceEntry input (frame input depth sourceStart)) :=
  (frame input depth sourceStart).authority.withProjectionCoface
    (component (review := review) input depth sourceStart datum prefixLimit renewalLimit)

abbrev Query := GermAt input depth sourceStart datum prefixLimit renewalLimit
  ((frame input depth sourceStart).native.root.emitted (frame input depth sourceStart).visit.current)

def registeredInput : SourceNativeRootInquiryInputAt
    (root (review := review) input depth sourceStart datum prefixLimit renewalLimit)
    (visit (review := review) input depth sourceStart datum prefixLimit renewalLimit)
    (Query input depth sourceStart datum prefixLimit renewalLimit) where
  projection := (installation (review := review) input depth sourceStart datum prefixLimit renewalLimit).embed .input
  active := ()
  classifier_eq := rfl
  queryType_eq := rfl

def proposal := (registeredInput (review := review) input depth sourceStart datum prefixLimit renewalLimit).query.raw

theorem registered_proposal_is_the_original_source :
    proposal (review := review) input depth sourceStart datum prefixLimit renewalLimit =
      datum.reader ((frame input depth sourceStart).native.root.emitted (frame input depth sourceStart).visit.current) := rfl

theorem original_drained_root_ledger_and_emitter_are_preserved :
    (root (review := review) input depth sourceStart datum prefixLimit renewalLimit).toAuthoritativeRoot.toLedgerRoot =
      (frame input depth sourceStart).native.root.toAuthoritativeRoot.toLedgerRoot ∧
    (root (review := review) input depth sourceStart datum prefixLimit renewalLimit).emitted =
      (frame input depth sourceStart).native.root.emitted := ⟨rfl, rfl⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress.registeredInput
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress.registered_proposal_is_the_original_source
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress.original_drained_root_ledger_and_emitter_are_preserved
