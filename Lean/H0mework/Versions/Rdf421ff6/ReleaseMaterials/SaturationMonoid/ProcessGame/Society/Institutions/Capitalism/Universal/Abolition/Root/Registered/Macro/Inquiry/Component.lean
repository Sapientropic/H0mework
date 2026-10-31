import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Inquiry.Foundation
import H0mework.Versions.R2.Arithmetic.PrimeShadow.LivingLawRootInquiryInputSourceKernel

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Inquiry

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
  (basis : Basis frame.N)

inductive Projection
  | query | answer | compilation | consumer

def NotIssue (current : frame.V.Current) : Prop :=
  match frame.item? current with
  | none => True
  | some item => (registration? input depth count item (frame.account current)).isSome = false

instance (current : frame.V.Current) : Decidable (NotIssue frame current) := by
  unfold NotIssue
  cases frame.item? current <;> infer_instance

def HasWork (current : frame.V.Current) : Prop :=
  Accounting.bodyPaid (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition (frame.cursor current) = false ∨
    (frame.item? current).isSome = true

instance (current : frame.V.Current) : Decidable (HasWork frame current) := inferInstanceAs (Decidable (_ ∨ _))

def ActiveAt (projection : Projection) {current : frame.V.Current}
    (_occurrence : frame.root.toAuthoritativeRoot.toRoot.actual.OccurrenceAt current) : Type :=
  match projection with
  | .query => PLift (HasWork frame current)
  | .consumer => PLift (NotIssue frame current)
  | _ => Unit

def InactiveAt (projection : Projection) {current : frame.V.Current}
    (_occurrence : frame.root.toAuthoritativeRoot.toRoot.actual.OccurrenceAt current) : Type :=
  match projection with
  | .query => PLift (¬ HasWork frame current)
  | .consumer => PLift (¬ NotIssue frame current)
  | _ => PEmpty

def classify (projection : Projection) {current : frame.V.Current}
    (occurrence : frame.root.toAuthoritativeRoot.toRoot.actual.OccurrenceAt current) :
    ActiveAt frame projection occurrence ⊕ InactiveAt frame projection occurrence := by
  cases projection with
  | query => exact if work : HasWork frame current then .inl ⟨work⟩ else .inr ⟨work⟩
  | consumer => exact if ordinary : NotIssue frame current then .inl ⟨ordinary⟩ else .inr ⟨ordinary⟩
  | answer | compilation => exact .inl ()

def component : SourceNativeProjectionLaw frame.root.toAuthoritativeRoot.toLedgerRoot.source where
  Projection := Projection
  ActiveAt := ActiveAt frame
  InactiveAt := InactiveAt frame
  classify := classify frame
  PayloadAt := fun projection {current} occurrence _ => match projection with
    | .query => PUnit
    | .answer => Answer (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
    | .compilation => SourceNativeInquiryCompilationTokenAt (basis.entry occurrence.1) PUnit.unit
        (ULift.up.{1, 0} occurrence)
        (.answered : SourceNativeInquiryFrontAuditAt basis.U7 basis.calculus frame.root.toAuthoritativeRoot.source.lawSurface occurrence.1)
        (Answer (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
    | .consumer => SourceNativeInquiryAnswerConsumerTokenAt PUnit.unit (ULift.up.{1, 0} occurrence)
        (basis.entry occurrence.1) (answer (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition frame current)
  project := fun projection {current} _occurrence _ => match projection with
    | .query => PUnit.unit
    | .answer => answer (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition frame current
    | .compilation => .canonical (answer (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition frame current)
    | .consumer => .canonical

/-- The inquiry faces are fixed before this source is activated. Its material
emitter, complete ledger and computed target are definitionally unchanged. -/
def installFrame : NativeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition where
  nativeOrigin := frame.nativeOrigin
  N := frame.N
  V := frame.V
  root := frame.root.withProjectionCoface (component frame basis)
  cursor := frame.cursor
  successor := frame.successor
  next_exact := frame.next_exact
  entry := fun current => basis.entry (frame.sourceSupport current)
  entries_finite := frame.entries_finite
  open_fibres := frame.open_fibres
  successor_keys := frame.successor_keys

def installation : SourceNativeProjectionLaw.InstallationAt (component frame basis)
    (installFrame frame basis).root.source.base.projectionLaw :=
  .componentCoface frame.root.source.base (component frame basis)

def registeredInput (visit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot)
    (work : HasWork frame visit.current) :
    SourceNativeRootInquiryInputAt (installFrame frame basis).root visit PUnit where
  projection := (installation frame basis).embed .query
  active := ⟨work⟩
  classifier_eq := by
    change classify frame .query _ = _
    exact dif_pos work
  queryType_eq := rfl

theorem original_source_and_native_next_are_unchanged :
    (installFrame frame basis).root.toAuthoritativeRoot.toLedgerRoot = frame.root.toAuthoritativeRoot.toLedgerRoot ∧
      (installFrame frame basis).cursor = frame.cursor := ⟨rfl, rfl⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Inquiry
