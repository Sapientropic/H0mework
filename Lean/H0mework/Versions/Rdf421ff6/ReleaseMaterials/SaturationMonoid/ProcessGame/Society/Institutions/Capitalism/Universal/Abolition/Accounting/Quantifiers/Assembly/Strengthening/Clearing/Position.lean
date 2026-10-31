import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing.NativeOne
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing.Raw
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Native.Selection

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)
  (reader : Macro.Raw.Reader input depth count)

/-- A fixed-input view of the original current. Its root, native account,
authority and old rows are those of the existing frame. -/
structure Position : Type 4 where
  start : Physical.Cursor Party Good Port Technology Instrument
  frame : Public.NativeFrame input depth count 0 0 [] start
  visit : SourceNativeTemporalVisitAt (Public.Inquiry.installedFrame frame reader).root.toAuthoritativeRoot.toLedgerRoot
  actual : Public.Inquiry.ActualAt frame visit.current
  paid : actual.actual.bodyPaid = true
  authority : SourceNativeLivingTemporalCausalEntryAuthorityAt (Public.Inquiry.installedFrame frame reader).root visit
    ((Public.Inquiry.installedFrame frame reader).entry visit.current)
  rows : Evolving.PaidRowsAt frame.N (frame.sourceSupport visit.current)
  ready : ¬ Public.Inquiry.HasWork frame actual.actual

namespace Position
variable {input depth count reader}

def native (position : Position input depth count reader) : Evolving.NativeCurrent
    (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) where
  input := input
  depth := depth
  count := count
  prefixLimit := 0
  renewalLimit := 0
  oldPast := []
  start := position.start
  frame := position.frame
  reader := reader
  visit := position.visit
  actual := position.actual
  bodyPaid := position.paid
  authority := position.authority
  rows := position.rows

def past (position : Position input depth count reader) := position.actual.readerCursor.past

theorem raw_state_is_read_from_its_actual_past (position : Position input depth count reader) :
    Public.Scope.actualState input depth count 0 0 [] position.actual.snapshot =
      Physical.Public.stateAt input depth count 0 0 [] position.past := by
  unfold past Public.Scope.actualState Public.Inquiry.ActualAt.readerCursor
  simp only [Physical.receive,Physical.Prefix.past_readback,List.nil_append]

def step (position : Position input depth count reader)
    (request : Request Party Good Port Technology Instrument)
    (selected : position.actual.proposal reader = .primitive request)
    (noConsents : request.consents = [])
    (valid : (Physical.Public.interpreter input).Valid
      (Physical.Public.stateAt input depth count 0 0 [] position.past).raw request) :
    Position input depth count reader := by
  have checked : (Physical.Public.interpreter input).Valid
      (Public.Scope.actualState input depth count 0 0 [] position.actual.snapshot).raw request := by
    rw [raw_state_is_read_from_its_actual_past]
    exact valid
  let next := (position.native.raw position.ready).ordinary
  exact { start := next.start
          frame := next.frame
          visit := next.visit
          actual := next.actual
          paid := next.bodyPaid
          authority := next.authority
          rows := next.rows
          ready := the_consumed_primitive_is_ready_for_its_next_actual_request position.native request selected
            position.ready noConsents checked }

theorem step_native_is_the_original_raw_and_financial_successor
    (position : Position input depth count reader)
    (request : Request Party Good Port Technology Instrument)
    (selected : position.actual.proposal reader = .primitive request)
    (noConsents : request.consents = [])
    (valid : (Physical.Public.interpreter input).Valid
      (Physical.Public.stateAt input depth count 0 0 [] position.past).raw request) :
    (step position request selected noConsents valid).native = (position.native.raw position.ready).ordinary := rfl

end Position
end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing
