import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Raw.Query
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native.Resolve

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Raw

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  {proposal : Compile.RawInput Party Good Port Technology Instrument} {sourcePosition : Nat}
  {review : Option (ReviewPhase.ContextAt input)}
  (frame : NativeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
  (data : Continuation.FinancialData frame) (reader : Reader input depth count)
  (basis : Inquiry.Basis frame.N)

inductive Projection
  | internalQuery | internalAnswer | internalCompilation | internalConsumer
  | rawQuery | rawReport | rawCompilation | rawConsumer
  | snapshot

/-- The native restriction belongs to the same installed physical/account
snapshot. An absent creator is disclosed; it is never an empty paid scope. -/
structure Snapshot where
  physical : Physical.Cursor Party Good Port Technology Instrument
  account : (Epoch.Finance.process input depth count).GeneratedState
  native : ReviewSource.Native.ReadoutsAt input depth count prefixLimit renewalLimit physical

def Snapshot.toPair (snapshot : Snapshot (input := input) (depth := depth) (count := count)
    (prefixLimit := prefixLimit) (renewalLimit := renewalLimit)) :=
  (snapshot.physical, snapshot.account)

def currentSnapshot (current : frame.V.Current) : Physical.Cursor Party Good Port Technology Instrument :=
  if Accounting.bodyPaid (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
      start proposal sourcePosition (frame.cursor current) then
    Inventory.physicalAfter (review := review) input depth count prefixLimit renewalLimit start proposal
  else start

def EnabledAt (projection : Projection) (current : frame.V.Current) : Prop :=
  match projection with
  | .internalQuery | .internalAnswer | .internalCompilation => Inquiry.HasWork frame current
  | .internalConsumer => Inquiry.HasWork frame current ∧ Inquiry.NotIssue frame current
  | .rawQuery | .rawReport | .rawCompilation | .rawConsumer => Available frame data current
  | .snapshot => True

def ActiveAt (projection : Projection) {current : frame.V.Current}
    (_occurrence : frame.root.toAuthoritativeRoot.toRoot.actual.OccurrenceAt current) : Type :=
  PLift (EnabledAt frame data projection current)

def InactiveAt (projection : Projection) {current : frame.V.Current}
    (_occurrence : frame.root.toAuthoritativeRoot.toRoot.actual.OccurrenceAt current) : Type :=
  PLift (¬ EnabledAt frame data projection current)

def classify (projection : Projection) {current : frame.V.Current}
    (occurrence : frame.root.toAuthoritativeRoot.toRoot.actual.OccurrenceAt current) :
    ActiveAt frame data projection occurrence ⊕ InactiveAt frame data projection occurrence := by
  classical
  exact if active : EnabledAt frame data projection current then .inl ⟨active⟩ else .inr ⟨active⟩

/-- Both token families retain the actual query. The raw family seals the
source-generated full history and account, not an empty completion marker. -/
def component : SourceNativeProjectionLaw frame.root.toAuthoritativeRoot.toLedgerRoot.source where
  Projection := Projection
  ActiveAt := ActiveAt frame data
  InactiveAt := InactiveAt frame data
  classify := classify frame data
  PayloadAt := fun projection {current} occurrence active => match projection with
    | .internalQuery => QueryAt frame data reader current
    | .internalAnswer => Inquiry.Answer (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
    | .internalCompilation => SourceNativeInquiryCompilationTokenAt (basis.entry occurrence.1)
        (QueryAt.internal active.down : QueryAt frame data reader current)
        (ULift.up.{1, 0} occurrence)
        (.answered : SourceNativeInquiryFrontAuditAt basis.U7 basis.calculus frame.root.toAuthoritativeRoot.source.lawSurface occurrence.1)
        (Inquiry.Answer (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
    | .internalConsumer => SourceNativeInquiryAnswerConsumerTokenAt
        (QueryAt.internal active.down.1 : QueryAt frame data reader current)
        (ULift.up.{1, 0} occurrence) (basis.entry occurrence.1)
        (Inquiry.answer (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition frame current)
    | .rawQuery => QueryAt frame data reader current
    | .rawReport => ResultAt frame data reader (germAt frame data reader current active.down)
    | .rawCompilation => SourceNativeInquiryCompilationTokenAt (basis.entry occurrence.1)
        (QueryAt.raw (germAt frame data reader current active.down))
        (ULift.up.{1, 0} occurrence)
        (.answered : SourceNativeInquiryFrontAuditAt basis.U7 basis.calculus frame.root.toAuthoritativeRoot.source.lawSurface occurrence.1)
        (ResultAt frame data reader (germAt frame data reader current active.down))
    | .rawConsumer => SourceNativeInquiryAnswerConsumerTokenAt
        (QueryAt.raw (germAt frame data reader current active.down))
        (ULift.up.{1, 0} occurrence) (basis.entry occurrence.1)
        (reportAt frame data reader (germAt frame data reader current active.down))
    | .snapshot => Snapshot (input := input) (depth := depth) (count := count)
        (prefixLimit := prefixLimit) (renewalLimit := renewalLimit)
  project := by
    intro projection current occurrence active
    cases projection with
    | internalQuery => exact .internal active.down
    | internalAnswer => exact Inquiry.answer (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition frame current
    | internalCompilation => exact .canonical (Inquiry.answer (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition frame current)
    | internalConsumer => exact .canonical
    | rawQuery => exact .raw (germAt frame data reader current active.down)
    | rawReport => exact reportAt frame data reader (germAt frame data reader current active.down)
    | rawCompilation => exact .canonical (reportAt frame data reader (germAt frame data reader current active.down))
    | rawConsumer => exact .canonical
    | snapshot => exact ⟨currentSnapshot frame current, frame.account current,
        ReviewSource.Native.readouts input depth count prefixLimit renewalLimit
          (currentSnapshot frame current) frame.nativeOrigin review⟩

/-- The entire next-input law is present before activation. Adding these
faces leaves the original source, whole ledger and generated target intact. -/
def installCompleteFrame : NativeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition where
  nativeOrigin := frame.nativeOrigin
  N := frame.N
  V := frame.V
  root := frame.root.withProjectionCoface (component frame data reader basis)
  cursor := frame.cursor
  successor := frame.successor
  next_exact := frame.next_exact
  entry := fun current => basis.entry (frame.sourceSupport current)
  entries_finite := frame.entries_finite
  open_fibres := frame.open_fibres
  successor_keys := frame.successor_keys

def installCompleteData : Continuation.FinancialData (installCompleteFrame frame data reader basis) where
  Ready := data.Ready
  ready_next := data.ready_next
  bodyPaid := data.bodyPaid
  familyAt := data.familyAt
  next_support := data.next_support
  occurrence_eq_emitted := data.occurrence_eq_emitted

def installation : SourceNativeProjectionLaw.InstallationAt (component frame data reader basis)
    (installCompleteFrame frame data reader basis).root.source.base.projectionLaw :=
  .componentCoface frame.root.source.base (component frame data reader basis)

def registeredInternalInput
    (visit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot)
    (work : Inquiry.HasWork frame visit.current) :
    SourceNativeRootInquiryInputAt (installCompleteFrame frame data reader basis).root visit
      (QueryAt frame data reader visit.current) where
  projection := (installation frame data reader basis).embed .internalQuery
  active := ⟨work⟩
  classifier_eq := by
    change classify frame data .internalQuery _ = _
    exact dif_pos work
  queryType_eq := rfl

def registeredRawInput
    (visit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot)
    (available : Available frame data visit.current) :
    SourceNativeRootInquiryInputAt (installCompleteFrame frame data reader basis).root visit
      (QueryAt frame data reader visit.current) where
  projection := (installation frame data reader basis).embed .rawQuery
  active := ⟨available⟩
  classifier_eq := by
    change classify frame data .rawQuery _ = _
    exact dif_pos available
  queryType_eq := rfl

def registeredInput
    (visit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot)
    (ready : data.Ready visit.current)
    (same : Continuation.AccountIsSourceFold (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
      start proposal sourcePosition (frame.cursor visit.current)) :
    SourceNativeRootInquiryInputAt (installCompleteFrame frame data reader basis).root visit
      (QueryAt frame data reader visit.current) :=
  if work : Inquiry.HasWork frame visit.current then
    registeredInternalInput frame data reader basis visit work
  else registeredRawInput frame data reader basis visit
    ⟨ready, same, no_work_is_source_complete frame visit.current work⟩

theorem registered_input_is_the_source_query
    (visit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot)
    (ready : data.Ready visit.current)
    (same : Continuation.AccountIsSourceFold (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
      start proposal sourcePosition (frame.cursor visit.current)) :
    (registeredInput frame data reader basis visit ready same).query =
      queryAt frame data reader visit.current ready same := by
  unfold registeredInput queryAt
  split_ifs <;> rfl

theorem original_source_ledger_and_next_are_unchanged :
    (installCompleteFrame frame data reader basis).root.toAuthoritativeRoot.toLedgerRoot =
      frame.root.toAuthoritativeRoot.toLedgerRoot ∧
    (installCompleteFrame frame data reader basis).cursor = frame.cursor ∧
    (installCompleteFrame frame data reader basis).successor = frame.successor :=
  ⟨rfl, rfl, rfl⟩

theorem financial_source_is_the_same
    (current : frame.V.Current) (ready : data.Ready current) :
    (installCompleteData frame data reader basis).familyAt current ready = data.familyAt current ready ∧
    (installCompleteFrame frame data reader basis).account current = frame.account current :=
  ⟨rfl, rfl⟩

theorem completed_source_registers_the_actual_raw_germ
    (visit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot)
    (available : Available frame data visit.current) :
    (registeredRawInput frame data reader basis visit available).query =
      QueryAt.raw (germAt frame data reader visit.current available) := rfl

def snapshotFace (visit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot) :
    SourceNativeRootSemanticFaceAt (installCompleteFrame frame data reader basis).root visit where
  projection := (installation frame data reader basis).embed .snapshot
  active := ⟨trivial⟩
  classifier_eq := by
    change classify frame data .snapshot _ = _
    exact dif_pos trivial

theorem snapshot_of_a_completed_body_is_the_actual_past
    (current : frame.V.Current) (ready : data.Ready current) :
    currentSnapshot frame current =
      Inventory.physicalAfter (review := review) input depth count prefixLimit renewalLimit start proposal := by
  unfold currentSnapshot
  rw [data.bodyPaid current ready]
  rfl

theorem snapshot_before_the_body_retains_the_original_past
    (current : frame.V.Current)
    (unpaid : Accounting.bodyPaid (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
      start proposal sourcePosition (frame.cursor current) = false) :
    currentSnapshot frame current = start := by
  unfold currentSnapshot
  rw [unpaid]
  rfl

theorem installed_snapshot_reads_the_same_source
    (visit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot) :
    (snapshotFace frame data reader basis visit).rootRead.toPair =
      (currentSnapshot frame visit.current, frame.account visit.current) := rfl

theorem installed_snapshot_reads_its_original_native_creator
    (visit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot) :
    (snapshotFace frame data reader basis visit).rootRead.native =
      ReviewSource.Native.readouts input depth count prefixLimit renewalLimit
        (currentSnapshot frame visit.current) frame.nativeOrigin review := rfl

#print axioms registered_input_is_the_source_query
#print axioms original_source_ledger_and_next_are_unchanged
#print axioms financial_source_is_the_same
#print axioms completed_source_registers_the_actual_raw_germ
#print axioms installed_snapshot_reads_the_same_source

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Raw
